"""One source binds original UF methods, const overloads and constructor exports."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT/'verifier'), str(ROOT/'tools'), str(ROOT/'tests')]
import context_class_ir as bundle
from class_copy_layout import MEMBER_VIEW_SUPPORT, MEMBER_COPY_SUPPORT
from check_proof_security import BUILTINS
from proof_security import audit_source
from test_scalar_ir import lean_environment
from offline import disable_network
from nested_bridge import check_source
from context_method_ir import emit_context_methods

SOURCE = ROOT/'tests/imports/union_find_public_compat.hpp'


class ContextClassTests(unittest.TestCase):
    def test_member_view_support_independent_kernel(self):
        lake,env = lean_environment()
        exporter = ROOT/'.tools/lean4export/.lake/build/bin/lean4export'
        nanoda = ROOT/'.tools/nanoda_lib/target/release/nanoda_bin'
        with tempfile.TemporaryDirectory(prefix='member-view-independent-') as directory:
            scratch = Path(directory)
            proof = scratch/'MemberViewSupportAudit.lean'
            proof.write_text('import Proofs.CppConstructorView\nimport Proofs.CppConstructorMultiFinish\n'
                             'import Proofs.CppClassCopyCommands\nimport Proofs.CppFrameResolveExtension\n'
                             'namespace MemberViewIndependent\n'+MEMBER_VIEW_SUPPORT+
                             MEMBER_COPY_SUPPORT+
                             (ROOT/'tests/lean/member_copy_values.lean').read_text()+
                             (ROOT/'tests/lean/member_copy_containers.lean').read_text()+
                             '\nend MemberViewIndependent\n')
            audit_source(proof)
            env = dict(env,LEAN_PATH=directory,LEAN_NUM_THREADS='1')
            compiled = subprocess.run([lake,'env','lean','--root='+directory,
                                       '-o',str(proof.with_suffix('.olean')),str(proof)],
                                      cwd=ROOT,env=env,capture_output=True,text=True,timeout=120)
            self.assertEqual(compiled.returncode,0,compiled.stdout+compiled.stderr)
            self.assertNotIn('warning:',compiled.stdout+compiled.stderr)
            roots = ['restrictVectors','restrict_identity','VectorView','restrict_properties',
                     'finishView','constructViewFuel','constructView_of_steps','finishView_ok']
            permitted = ['propext','Classical.choice','Quot.sound']
            export = scratch/'export.ndjson'
            with export.open('w') as output:
                exported = subprocess.run([lake,'env',str(exporter),'MemberViewSupportAudit','--',
                    *BUILTINS,*permitted,*['MemberViewIndependent.MemberView.'+name for name in roots],
                    *['MemberViewIndependent.MemberCopy.'+name for name in
                      ['Field','statement','validate','command','reference','runCopyFuel','Steps',
                       'command_complete','copy_complete','Ready','ready_steps','copy_ready_complete',
                       'source_copy_complete','PreservesContainers','ready_preserves_containers',
                       'source_copy_preserves_containers','PreservesReferences','ready_preserves_references',
                       'source_copy_preserves_observers','scalar_destination','resolved_payload','vector_destination',
                       'ready_shape','source_copy_layout','source_copy_values','source_copy_positions','source_copy_work','source_copy_space',
                       'vector_owners_distinct','scalar_addresses_distinct','vector_old_separated','scalar_old_separated','invalid_source']],
                    *['MemberViewIndependent.MemberCopyValuesRegression.'+name for name in
                      ['ordered_copy','wrong_order_rejected','wrong_permission_rejected','scalar_work_exact']],
                    *['MemberViewIndependent.MemberCopyContainersRegression.'+name for name in
                      ['nested_headers_preserved','captured_read_preserved','borrowed_header_stale',
                       'captured_read_still_live','copy_after_header_invalidation','captured_read_after_copy',*[f'check_{i}' for i in range(1,13)]]]],
                    cwd=ROOT,env=env,stdout=output,stderr=subprocess.PIPE,text=True,timeout=120)
            self.assertEqual(exported.returncode,0,exported.stderr)
            config = scratch/'nanoda.json'
            config.write_text(json.dumps(dict(export_file_path=str(export),permitted_axioms=permitted,
                unpermitted_axiom_hard_error=True,unsafe_permit_all_axioms=False,nat_extension=True,
                string_extension=True,num_threads=2,print_success_message=True,print_axioms=False)))
            checked = subprocess.run([str(nanoda),str(config)],cwd=scratch,env=env,
                                     capture_output=True,text=True,timeout=120)
            self.assertEqual(checked.returncode,0,checked.stdout+checked.stderr)
            self.assertRegex(checked.stdout,r'\AChecked [1-9][0-9]* declarations with no errors\s*\Z')
            print(checked.stdout.strip())
            cpp = scratch/'member_copy_observers.cpp'
            cpp.write_text((ROOT/'tests/imports/member_copy_observers.cpp').read_text())
            binary = scratch/'native'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined',
                            '-fno-sanitize-recover=all',str(cpp),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)

    def test_all_methods_and_constructor_exports_match_proved_programs(self):
        generated = bundle.emit_context_class(SOURCE, 'cp::UnionFind', 'UFClassBundle')
        metadata = dict(translation='context_class_ir', qualified_class='cp::UnionFind',
            lean_namespace='UFClassBundle', source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
            public_declarations=['CXXRecordDecl:UnionFind'])
        check_source(SOURCE, metadata, generated)
        imports = [line for line in generated.splitlines() if line.startswith('import ')]
        body = '\n'.join(line for line in generated.splitlines() if not line.startswith('import '))
        checks = ['import Proofs.UfPublicSource', 'import Proofs.UfReadValues', 'import Proofs.UfClassCopyBridge',
                  'import Proofs.Generated.UnionFindCandidate',
                  'import Proofs.Generated.UnionFindConstruction', *imports, body]
        for emitted, old in [('unite','unite'), ('same_2','same'), ('root','root'),
                             ('size_1','size'), ('num_groups_0','num_groups')]:
            checks.append(f'example : UFClassBundle.Calls.Methods.UnionFind_{emitted} = '
                f'Proofs.UnionFindCandidateInstance.UnionFind_{old} := rfl')
        for emitted, old in [('size_1_2','sizeProgram'), ('same_2_2','sameProgram'),
                             ('num_groups_0_2','counterProgram')]:
            checks.append(f'example : UFClassBundle.Calls.Methods.UnionFind_{emitted} = '
                f'Proofs.UfReadPrograms.{old} := rfl')
        for index in [0, 1]:
            checks.append(f'example : UFClassBundle.Construction.UnionFind_construct{index} = '
                f'Proofs.UnionFindConstructionInstance.UnionFind_construct{index} := rfl')
        checks.extend([
            'example : UFClassBundle.Construction.profile = Proofs.UfClassCopyBridge.profile := rfl',
            'example (fuel : Nat) (s : Proofs.CppNestedProgram.NState)',
            '    (args : List Proofs.CppNestedCall.NArgument) :',
            '    UFClassBundle.Construction.UnionFind_construct1_exportFuel fuel s args =',
            '      Proofs.UnionFindConstructionInstance.UnionFind_construct1.constructFuel fuel s args',
            '        1 (.integer ⟨32,true,false⟩) [⟨2,⟨32,true,false⟩⟩,⟨3,⟨32,true,false⟩⟩] := rfl',
        ])
        # Reuse source-receiver mappings for both ordinary and const methods;
        # the generated class wrapper must not bypass their actual adapters.
        checks.append((ROOT/'tests/lean/union_find_read_call_mapping.lean').read_text()
            .replace('UnionFindPublicCompat', 'UFClassBundle.Calls'))
        with tempfile.TemporaryDirectory(prefix='context-class-') as directory:
            proof = Path(directory)/'check.lean'
            proof.write_text('\n'.join(checks)+'\n')
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
            self.assertNotIn('warning:', result.stdout+result.stderr)

    def test_registered_compat_model_matches_the_complete_audited_source(self):
        generated = bundle.emit_context_class(SOURCE, 'cp::UnionFind',
            'Proofs.UnionFindPublicCompatInstance')
        self.assertEqual(generated,
            (ROOT/'Proofs/Generated/UnionFindPublicCompat.lean').read_text())

    def test_constructor_and_method_changes_both_affect_generated_model(self):
        original = SOURCE.read_text()
        baseline = bundle.emit_context_class(SOURCE, 'cp::UnionFind', 'MutationBundle')
        with tempfile.TemporaryDirectory(prefix='context-class-mutation-') as directory:
            source = Path(directory)/'changed.hpp'
            for before, after in [('_ps(n, -1)', '_ps(n, -2)'),
                                  ('return _num_groups;', 'return _n;')]:
                with self.subTest(change=after):
                    self.assertIn(before, original)
                    source.write_text(original.replace(before, after))
                    changed = bundle.emit_context_class(source, 'cp::UnionFind', 'MutationBundle')
                    # Exclude digests: changed source bytes alone are not model coverage.
                    def semantics(text):
                        return '\n'.join(line for line in text.splitlines()
                            if not line.startswith('def sourceSHA256'))
                    self.assertNotEqual(semantics(changed), semantics(baseline))
                    if before == 'return _num_groups;':
                        metadata = dict(translation='context_class_ir', qualified_class='cp::UnionFind',
                            lean_namespace='MutationBundle',
                            source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                            public_declarations=['CXXRecordDecl:UnionFind'])
                        # Updating the source hash cannot authorize the old model.
                        with self.assertRaisesRegex(ValueError, 'mismatch'):
                            check_source(source, metadata, baseline)

    def test_source_changed_between_generation_stages_is_rejected(self):
        with tempfile.TemporaryDirectory(prefix='context-class-race-') as directory:
            source = Path(directory)/'source.hpp'
            source.write_text(SOURCE.read_text())
            real = bundle.emit_class_layout
            def changed(*args, **kwargs):
                result = real(*args, **kwargs)
                source.write_text(source.read_text().replace('_ps(n, -1)', '_ps(n, -2)'))
                return result
            with patch.object(bundle, 'emit_class_layout', side_effect=changed):
                with self.assertRaisesRegex(ValueError, 'source changed'):
                    bundle.emit_context_class(source, 'cp::UnionFind', 'ChangedClass')

    def test_resizing_method_is_rejected_instead_of_omitted(self):
        with tempfile.TemporaryDirectory(prefix='context-class-resize-') as directory:
            source = Path(directory)/'resize.hpp'
            source.write_text(SOURCE.read_text().replace('public:',
                'public:\n int add(){_ps.push_back(-1);return _num_groups;}'))
            with self.assertRaises(ValueError):
                bundle.emit_context_class(source, 'cp::UnionFind', 'ResizingClass')

    def test_bundle_rejects_a_static_method_added_to_the_same_public_class(self):
        with tempfile.TemporaryDirectory(prefix='strict-class-static-') as directory:
            source = Path(directory)/'source.hpp'
            source.write_text(SOURCE.read_text().replace('public:',
                'public:\n static int omitted(){return 42;}'))
            with self.assertRaisesRegex(ValueError, 'class declaration omitted'):
                bundle.emit_context_class(source, 'cp::UnionFind', 'StaticUF')

    def test_omitted_class_declarations_are_rejected(self):
        additions = [
            'template<class T> int identity(T value){return 0;}',
            'int out_of_line();',
            'UnionFind(long n);',
            'inline static int counter = 0;',
            'operator int() const{return _num_groups;}',
            'friend int external(const UnionFind&){return 0;}',
            'struct Tag {};',
            'using counter_type = int;',
        ]
        with tempfile.TemporaryDirectory(prefix='strict-class-declarations-') as directory:
            source = Path(directory)/'source.hpp'
            for addition in additions:
                with self.subTest(declaration=addition):
                    source.write_text(SOURCE.read_text().replace('public:', 'public:\n '+addition))
                    with self.assertRaisesRegex(ValueError, 'class declaration omitted'):
                        emit_context_methods(source, 'cp::UnionFind', 'OmittedUF', strict_declarations=True)

    def test_partial_method_selection_retains_its_explicit_scope(self):
        with tempfile.TemporaryDirectory(prefix='context-class-partial-') as directory:
            source = Path(directory)/'source.hpp'
            source.write_text(SOURCE.read_text().replace('public:',
                'public:\n static int omitted(){return 42;}'))
            selected = emit_context_methods(source, 'cp::UnionFind', 'PartialClass',
                method_names=['num_groups'])
            self.assertIn('selected_context_method_receivers', selected)
            self.assertIn('UnionFind_num_groups', selected)
            with self.assertRaisesRegex(ValueError, 'cannot select only some methods'):
                emit_context_methods(source, 'cp::UnionFind', 'InvalidSelection',
                    method_names=['num_groups'], strict_declarations=True)


    def test_multi_member_constructor_void_calls_growth_and_field_alias(self):
        source_text = '''#include <vector>
struct Multi {
 int count;
 std::vector<int> left;
 const int stamp;
 std::vector<int> right;
 Multi(int &x):count(x),left(2,x),stamp(x+1),right(1,0) { x=9; set_right(x); }
 void set_right(int value) { right[0]=value; }
 void update(int &outside) { outside=12; count=outside; left[0]=count+stamp; right[0]=left[0]; }
 int peek() const { return left[0]+right[0]+count+stamp; }
 int alias(int &value) { value=17; return count; }
 void grow(int value) { left.push_back(value); }
};
'''
        checks = r'''
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop
abbrev i32 : Ty := ⟨32,true,false⟩
def caller : NState := ⟨⟨[⟨i32,7⟩],[⟨0,true⟩],0,0,1⟩,
  ⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[.scalar 0],0,1⟩
def made := MultiBundle.Construction.Multi_construct0_exportFuel 64 caller [.scalarReference 0]
def created : NState := match made with | .finished (s,_) => s | _ => caller
def object : Proofs.CppConstructorMultiFinish.ObjectRef := ⟨[1,2],[3,4]⟩
example : made = .finished (created,object) := by decide +kernel
example (a b c d outside : Nat) :
    MultiBundle.Calls.Multi_update_arguments ⟨[a,b],[c,d]⟩ [.scalarReference outside] =
      some [.vectorReference a,.vectorReference b,.scalarReference c,.scalarReference d,
        .scalarReference outside] :=
  MultiBundle.Calls.Multi_update_arguments_of_fields _ _ a b c d rfl rfl rfl
#guard MultiBundle.Calls.fieldNames == ["left","right","count","stamp"]
#guard MultiBundle.Calls.fieldPermutation == [1,3,0,2]
#guard created.scalars.memory == [⟨i32,9⟩,⟨i32,7⟩,⟨i32,8⟩]
def updated := MultiBundle.Calls.Multi_update_callFuel 64 created object false [.scalarReference 0]
def afterUpdate : NState := match updated with | .finished (s,_) => s | _ => caller
example : updated = .finished (afterUpdate,.unit) := by decide +kernel
#guard afterUpdate.scalars.memory == [⟨i32,12⟩,⟨i32,12⟩,⟨i32,8⟩]
#guard (afterUpdate.frame.state.storage.lookup 0).map (·.items) == some [.integer 20,.integer 7]
#guard (afterUpdate.frame.state.storage.lookup 1).map (·.items) == some [.integer 20]
def peek := MultiBundle.Calls.Multi_peek_callFuel 64 afterUpdate object true []
#guard (match peek with | .finished (_, .scalar n) => some n | _ => none) == some 60
def aliased := MultiBundle.Calls.Multi_alias_callFuel 64 afterUpdate object false [.scalarReference 3]
def afterAlias : NState := match aliased with | .finished (s,_) => s | _ => caller
example : aliased = .finished (afterAlias,.scalar 17) := by decide +kernel
#guard afterAlias.scalars.memory == [⟨i32,12⟩,⟨i32,17⟩,⟨i32,8⟩]
def grown := MultiBundle.Calls.Multi_grow_callFuel 64 afterAlias object false [.value (.literal i32 3)]
def afterGrow : NState := match grown with | .finished (s,_) => s | _ => caller
example : grown = .finished (afterGrow,.unit) := by decide +kernel
#guard (afterGrow.frame.state.storage.lookup 0).map (·.items) == some [.integer 20,.integer 7,.integer 3]
#guard (afterGrow.frame.state.storage.lookup 1).map (·.items) == some [.integer 20]
#guard afterGrow.scalars.memory == afterAlias.scalars.memory
#guard afterGrow.slots == created.slots
#guard afterGrow.scope == caller.scope
#guard afterGrow.frame.state.wellFormed
#guard (match MultiBundle.Calls.Multi_grow_callFuel 64 afterAlias object true [.value (.literal i32 3)] with
  | .fault => true | _ => false)
#guard (MultiBundle.Calls.Multi_update_arguments ⟨[1],[3,4]⟩ [.scalarReference 0]).isNone
#guard (MultiBundle.Calls.Multi_update_arguments object []).isNone
#guard (MultiBundle.Calls.Multi_peek_arguments ⟨[1,2],[3]⟩ []).isNone
def aliasCaller : NState := {caller with
  scalars := {caller.scalars with bindings := [⟨0,true⟩,⟨0,false⟩]},
  slots := [.scalar 0,.scalar 1]}
def constCreated := MultiBundle.Construction.Multi_construct0_exportViewFuel 64 aliasCaller
  [.scalarReference 0] true
def constState : NState := match constCreated with | .finished (s,_) => s | _ => caller
example : constCreated = .finished (constState,⟨[2,3],[4,5]⟩) := by decide +kernel
#guard constState.scalars.memory == [⟨i32,9⟩,⟨i32,7⟩,⟨i32,8⟩]
#guard constState.scalars.bindings == [⟨0,true⟩,⟨0,false⟩,⟨1,false⟩,⟨2,false⟩]
#guard constState.scalarCell 1 i32 == some (⟨0,false⟩,⟨i32,9⟩)
#guard constState.frame.bindings.map (·.writable) == [false,false]
'''
        with tempfile.TemporaryDirectory(prefix='class-multi-members-') as directory:
            root = Path(directory)
            source = root/'source.hpp'
            source.write_text(source_text)
            generated = bundle.emit_context_class(source,'Multi','MultiBundle',member_exports=True)
            imports = '\n'.join(line for line in generated.splitlines() if line.startswith('import '))
            body = '\n'.join(line for line in generated.splitlines() if not line.startswith('import '))
            proof = root/'check.lean'
            proof.write_text(imports+'\n'+body+'\n'+checks)
            lake, env = lean_environment()
            result = subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,
                                    capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            self.assertNotIn('warning:',result.stdout+result.stderr)
            cpp = root/'check.cpp'
            cpp.write_text('#include "source.hpp"\n#include <cassert>\n'
                'int main(){int x=7;Multi m(x);assert(x==9);m.update(x);assert(x==12);'
                'const Multi &c=m;assert(c.peek()==60);assert(m.alias(m.count)==17);'
                'm.grow(3);assert(m.left==std::vector<int>({20,7,3}));'
                'assert(m.right==std::vector<int>({20}));assert(m.count==17 && m.stamp==8);'
                'int y=7;const Multi c2(y);assert(y==9 && c2.peek()==31);}')
            binary = root/'native'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined',
                            '-fno-sanitize-recover=all',str(cpp),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)
            with self.assertRaises(ValueError):
                bundle.emit_context_class(source,'Multi','LegacyMulti')
            source.write_text(source_text.replace('int peek() const',
                'static int omitted(){return 1;} int peek() const'))
            with self.assertRaisesRegex(ValueError,'class declaration omitted'):
                bundle.emit_context_class(source,'Multi','OmittedMulti',member_exports=True)


    def test_multi_member_const_export_keeps_mutable_fields_and_constructor_writes(self):
        source_text = '''#include <vector>
struct Qualified {
 int number; mutable int changes; const int stamp;
 std::vector<int> normal;
 mutable std::vector<long long> scratch;
 const std::vector<int> frozen;
 Qualified(int value):number(value),changes(0),stamp(value+1),normal(1,value),
   scratch(1,value+2),frozen(1,value+3) { ++number; normal[0]=number; if(value==7) return; }
 long long adjust() const { ++changes; scratch[0]+=changes; return scratch[0]; }
 int read() const { return number+normal[0]+stamp+frozen[0]; }
};
'''
        checks = r'''
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop
abbrev i32 : Ty := ⟨32,true,false⟩
abbrev i64 : Ty := ⟨64,true,false⟩
def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
def made := QualifiedBundle.Construction.Qualified_construct0_exportViewFuel 64 empty
  [.value (.literal i32 7)] true
def initial : NState := match made with | .finished (s,_) => s | _ => empty
def object : Proofs.CppConstructorMultiFinish.ObjectRef := ⟨[0,1,2],[3,4,5]⟩
example : made = .finished (initial,object) := by decide +kernel
#guard QualifiedBundle.Construction.vectorPermissions true == [false,true,false]
#guard QualifiedBundle.Construction.vectorPermissions false == [true,true,false]
#guard initial.scalars.memory == [⟨i32,8⟩,⟨i32,0⟩,⟨i32,8⟩]
#guard initial.scalars.bindings == [⟨0,false⟩,⟨1,true⟩,⟨2,false⟩]
#guard initial.frame.bindings.map (·.writable) == [false,true,false]
#guard (initial.frame.state.storage.lookup 0).map (·.items) == some [.integer 8]
#guard (initial.frame.state.storage.lookup 1).map (·.items) == some [.integer 9]
#guard (initial.frame.state.storage.lookup 2).map (·.items) == some [.integer 10]
#guard ((initial.frame.elementRef 0 i32 0).bind (fun r => initial.frame.write r 23)).isNone
#guard ((initial.frame.elementRef 1 i64 0).bind (fun r => initial.frame.write r 23)).isSome
#guard ((initial.frame.elementRef 2 i32 0).bind (fun r => initial.frame.write r 23)).isNone
def adjusted := QualifiedBundle.Calls.Qualified_adjust_callFuel 64 initial object true []
def afterAdjust : NState := match adjusted with | .finished (s,_) => s | _ => empty
example : adjusted = .finished (afterAdjust,.scalar 10) := by decide +kernel
#guard afterAdjust.scalars.memory == [⟨i32,8⟩,⟨i32,1⟩,⟨i32,8⟩]
#guard (afterAdjust.frame.state.storage.lookup 1).map (·.items) == some [.integer 10]
#guard afterAdjust.frame.state.wellFormed
def read := QualifiedBundle.Calls.Qualified_read_callFuel 64 afterAdjust object true []
#guard (match read with | .finished (_, .scalar v) => some v | _ => none) == some 34
def copied := QualifiedBundle.Construction.copyFuel 64 afterAdjust object false
def copyState : NState := match copied with | .finished (s,_) => s | _ => empty
def copyObject : Proofs.CppConstructorMultiFinish.ObjectRef := ⟨[9,10,11],[6,7,8]⟩
example : copied = .finished (copyState,copyObject) := by decide +kernel
#guard copyState.work == afterAdjust.work + 18
#guard decide (copyState.scalars.peak ≤ QualifiedBundle.Construction.MemberCopy.scalarPeakBound afterAdjust 18)
#guard decide (copyState.frame.state.storage.peak ≤ QualifiedBundle.Construction.MemberCopy.storagePeakBound afterAdjust 18)
#guard decide (copyState.peak ≤ QualifiedBundle.Construction.MemberCopy.peakBound afterAdjust 18)
def based : NState :=
  let storage := {afterAdjust.frame.state.storage with baseSpace := 2}
  let state := {afterAdjust.frame.state with storage := storage}
  let frame := {afterAdjust.frame with state := state}
  {afterAdjust with
    scalars := {afterAdjust.scalars with baseMemory := 1}
    frame := frame}
def basedCopy := QualifiedBundle.Construction.copyFuel 64 based object false
def basedAfter : NState := match basedCopy with | .finished (s,_) => s | _ => empty
#guard basedAfter.scalars.baseMemory == 1 && basedAfter.frame.state.storage.baseSpace == 2
#guard basedAfter.work == based.work + 18
#guard decide (basedAfter.scalars.peak ≤ QualifiedBundle.Construction.MemberCopy.scalarPeakBound based 18)
#guard decide (basedAfter.frame.state.storage.peak ≤ QualifiedBundle.Construction.MemberCopy.storagePeakBound based 18)
#guard decide (basedAfter.peak ≤ QualifiedBundle.Construction.MemberCopy.peakBound based 18)
def reserved : NState := match afterAdjust.frame.reserve 1 (.integer i64) 5 with
  | some frame => ({afterAdjust with frame := frame} : NState).observe
  | none => empty
#guard (reserved.frame.state.storage.lookup 1).map (·.capacity) == some 5
#guard (reserved.frame.state.storage.lookup 1).map (·.epoch) == some 1
def metadataCopied := QualifiedBundle.Construction.copyFuel 64 reserved object false
def metadataState : NState := match metadataCopied with | .finished (s,_) => s | _ => empty
#guard metadataState.work == reserved.work + 18
#guard (metadataState.frame.state.storage.lookup 4).map (·.capacity) == some 1
#guard (metadataState.frame.state.storage.lookup 4).map (·.epoch) == some 0
#guard (metadataState.frame.state.storage.lookup 4).map (·.limit) ==
  (reserved.frame.state.storage.lookup 1).map (·.limit)
#guard copyState.scalars.memory == [⟨i32,8⟩,⟨i32,1⟩,⟨i32,8⟩,⟨i32,8⟩,⟨i32,1⟩,⟨i32,8⟩]
#guard copyState.frame.bindings.map (·.owner) == [0,1,2,3,4,5]
#guard copyState.frame.bindings.map (·.writable) == [false,true,false,true,true,false]
#guard copyState.scalars.bindings.map (·.writable) == [false,true,false,true,true,false]
#guard (copyState.frame.state.storage.lookup 3).map (·.items) == some [.integer 8]
#guard (copyState.frame.state.storage.lookup 4).map (·.items) == some [.integer 10]
def copyAdjusted := QualifiedBundle.Calls.Qualified_adjust_callFuel 64 copyState copyObject false []
def copyAfter : NState := match copyAdjusted with | .finished (s,_) => s | _ => empty
example : copyAdjusted = .finished (copyAfter,.scalar 12) := by decide +kernel
#guard (copyAfter.frame.state.storage.lookup 1).map (·.items) == some [.integer 10]
#guard (copyAfter.frame.state.storage.lookup 4).map (·.items) == some [.integer 12]
#guard copyAfter.scalars.memory == [⟨i32,8⟩,⟨i32,1⟩,⟨i32,8⟩,⟨i32,8⟩,⟨i32,2⟩,⟨i32,8⟩]
def constCopied := QualifiedBundle.Construction.copyFuel 64 copyAfter copyObject true
def constCopyState : NState := match constCopied with | .finished (s,_) => s | _ => empty
example : constCopied = .finished (constCopyState,⟨[15,16,17],[12,13,14]⟩) := by decide +kernel
#guard constCopyState.frame.bindings.map (·.writable) == [false,true,false,true,true,false,false,true,false]
#guard constCopyState.scalars.bindings.map (·.writable) == [false,true,false,true,true,false,false,true,false]
#guard constCopyState.frame.state.wellFormed
-- These absent sources would become readable after earlier declarations.
#guard (match QualifiedBundle.Construction.copyFuel 64 afterAdjust ⟨[0,1,9],[3,4,5]⟩ false with
  | .fault => true | _ => false)
#guard (match QualifiedBundle.Construction.copyFuel 64 afterAdjust ⟨[0,1,2],[3,4,6]⟩ false with
  | .fault => true | _ => false)
#guard (match QualifiedBundle.Construction.copyFuel 0 afterAdjust object false with
  | .exhausted => true | _ => false)
#guard (QualifiedBundle.Construction.copyFields ⟨[0,1],[3,4,5]⟩ false).isNone
def ordinary := QualifiedBundle.Construction.Qualified_construct0_exportViewFuel 64 empty
  [.value (.literal i32 7)] false
example : ordinary = QualifiedBundle.Construction.Qualified_construct0_exportFuel 64 empty
    [.value (.literal i32 7)] := by decide +kernel
#guard (QualifiedBundle.Construction.MemberView.restrictVectors
  [⟨0,.integer i32,false,.root 0⟩] [true]).isNone
#guard (QualifiedBundle.Construction.MemberView.restrictVectors
  [⟨0,.integer i32,true,.root 0⟩] []).isNone
'''
        with tempfile.TemporaryDirectory(prefix='class-multi-const-view-') as directory:
            root = Path(directory)
            source = root/'source.hpp'
            source.write_text(source_text)
            generated = bundle.emit_context_class(source,'Qualified','QualifiedBundle',member_exports=True)
            self.assertNotIn('set_option',generated)
            proof = root/'check.lean'
            proof.write_text(generated+'\n'+checks)
            lake,env = lean_environment()
            result = subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,
                                    capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            self.assertNotIn('warning:',result.stdout+result.stderr)
            cpp = root/'check.cpp'
            cpp.write_text('#include "source.hpp"\n#include <cassert>\n#include <type_traits>\n'
                'int main(){const Qualified q(7);'
                'static_assert(std::is_const_v<std::remove_reference_t<decltype((q.normal))>>);'
                'static_assert(!std::is_const_v<std::remove_reference_t<decltype((q.scratch))>>);'
                'assert(q.number==8 && q.normal[0]==8 && q.stamp==8 && q.frozen[0]==10);'
                'assert(q.adjust()==10 && q.changes==1 && q.read()==34);'
                'q.scratch.reserve(5);const Qualified metadata(q);'
                'assert(q.scratch.capacity()>=5 && metadata.scratch.size()==1 && metadata.scratch.capacity()==1);'
                'Qualified r(q);assert(r.number==8 && r.adjust()==12);'
                'assert(q.scratch[0]==10 && q.changes==1 && r.changes==2);'
                'const Qualified z(r);assert(z.adjust()==15 && r.scratch[0]==12);'
                'q.scratch[0]=23;assert(q.scratch[0]==23);}')
            binary = root/'native'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined',
                            '-fno-sanitize-recover=all',str(cpp),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)


if __name__ == '__main__':
    disable_network()
    unittest.main()
