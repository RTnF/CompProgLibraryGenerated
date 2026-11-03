"""Range-preserving Beats candidate: runtime regression and typed initializer generation."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT/'tools'), str(ROOT/'tests'), str(ROOT/'verifier')]
from nested_ir import lower_source, emit_lean, render_expression, render_commands
from context_class_ir import emit_context_class
from test_scalar_ir import lean_environment
from check_public import check_compiler
from offline import disable_network

CANDIDATE = ROOT/'experiments/verification/segment_tree_beats_wide.hpp'


class BeatsWideCandidateTests(unittest.TestCase):
    def test_member_bundle_matches_constructor_and_all_original_methods(self):
        model = emit_context_class(CANDIDATE,'cp::SegmentTreeBeats','BeatsMemberBundle',member_exports=True)
        self.assertNotIn('set_option',model)
        self.assertIn('private def',model)
        original = lower_source(ROOT/'library/segment_tree_beats.hpp')
        methods = [f['name'] for f in original['functions'] if f['name']!='SegmentTreeBeats_new0']
        self.assertEqual(len(methods),14)
        checks = ['example : BeatsMemberBundle.Construction.Stages.SegmentTreeBeats_construct0 = '
                  'Proofs.BeatsConstructCall.program := rfl']
        checks += [f'theorem source_{name} : BeatsMemberBundle.Calls.Methods.«{name}» = '
                   f'Proofs.BeatsInstance.«{name}» := rfl' for name in methods]
        checks += ['example : BeatsMemberBundle.Construction.Stages.SegmentTreeBeats_construct0.vectorFields = '
                   'Proofs.BeatsConstructorFields.vectorFields := rfl',
                   'example : BeatsMemberBundle.Construction.Stages.SegmentTreeBeats_construct0.scalarFields = '
                   'Proofs.BeatsConstructorFields.scalarFields := rfl']
        checks += ['theorem generated_constructor_call (fuel : Nat) (caller : Proofs.CppNestedProgram.NState)',
                   '    (arguments : List Proofs.CppNestedCall.NArgument) :',
                   '    BeatsMemberBundle.Construction.SegmentTreeBeats_construct0_exportFuel fuel caller arguments =',
                   '      Proofs.BeatsConstructCall.program.constructMembersFuel fuel caller arguments',
                   '        Proofs.BeatsConstructorFields.vectorFields Proofs.BeatsConstructorFields.scalarFields := rfl']
        checks += ['open Proofs.CppNestedProgram Proofs.CppNestedCall',
                   'def sourceReceiver (sl : Nat → Nat) (base : Nat) : Proofs.CppConstructorMultiFinish.ObjectRef := '
                   '⟨(List.range 15).map sl,[base+15,base+16]⟩',
                   'example (caller : NState) : Proofs.CppConstructorMultiFinish.reference caller 15 2 = '
                   'sourceReceiver (fun i => caller.slots.length+i) caller.slots.length := rfl']
        for name in ['chmin','chmax','add_val','update_val','calc_max','calc_min']:
            query = name.startswith('calc_')
            expressions = ['qa','qb'] if query else ['qa','qb','value']
            args = '['+','.join('.value '+expr for expr in expressions)+']'
            expanded = ('Proofs.BeatsPrepare.vargs sl 0 15 ++ '
                        '[.value (Proofs.BeatsReceiverCalls.infExpr base),'
                        '.value (Proofs.BeatsReceiverCalls.sizeExpr base),'+
                        ','.join('.value '+expr for expr in expressions)+']')
            slots = ' '.join([*(f'(sl {i})' for i in range(15)), '(base+15)', '(base+16)'])
            method = 'SegmentTreeBeats_'+name
            checks += [f'theorem generated_{name}_call (fuel : Nat) (receiver : NState) (sl : Nat → Nat) (base : Nat)',
                       '    ('+' '.join(expressions)+' : NExpr) :',
                       f'    BeatsMemberBundle.Calls.{method}_callFuel fuel receiver (sourceReceiver sl base) false {args} =',
                       f'      Proofs.BeatsInstance.{method}.callFuel fuel receiver ({expanded}) := by',
                       f'  have mapped := BeatsMemberBundle.Calls.{method}_arguments_of_fields '
                       f'(sourceReceiver sl base) {args} {slots} rfl rfl rfl',
                       f'  rw [BeatsMemberBundle.Calls.{method}_call_of_arguments _ _ _ _ _ mapped, source_{method}]',
                       '  rfl']
        with tempfile.TemporaryDirectory(prefix='beats-member-bundle-') as directory:
            proof = Path(directory)/'check.lean'
            proof.write_text('import Proofs.BeatsReceiverRestore\n'+model+'\n'+'\n'.join(checks)+'\n'+
                             (ROOT/'tests/lean/beats_member_receiver.lean').read_text()+'\n'+
                             (ROOT/'tests/lean/beats_member_copy_proof.lean').read_text()+'\n'+
                             (ROOT/'tests/lean/beats_member_copy.lean').read_text())
            lake,env = lean_environment()
            result = subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,
                                    capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            self.assertNotIn('warning:',result.stdout+result.stderr)
            cpp = Path(directory)/'copy.cpp'
            cpp.write_text(f'#include "{CANDIDATE}"\n#include <cassert>\n'
                'int main(){std::vector<long long> a{4,6,5};cp::SegmentTreeBeats original(a);'
                'cp::SegmentTreeBeats copied(original);assert(copied.calc_max(0,3)==6);'
                'copied.chmin(0,3,5);assert(copied.calc_max(0,3)==5);'
                'assert(original.calc_max(0,3)==6);}')
            binary = Path(directory)/'copy-native'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined',
                            '-fno-sanitize-recover=all',str(cpp),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)

    def test_existing_operations_normal_and_sanitized(self):
        check_compiler()
        with tempfile.TemporaryDirectory(prefix='beats-wide-native-') as directory:
            root = Path(directory)
            source = (ROOT/'tests/segment_tree_beats.cpp').read_text()
            source = source.replace('../experiments/library/cpp/template/small_template.hpp',
                                    str(ROOT/'experiments/library/cpp/template/small_template.hpp'))
            source = source.replace('../library/segment_tree_beats.hpp', str(CANDIDATE))
            cpp = root/'checks.cpp'; cpp.write_text(source)
            binary = root/'check'
            for flags in [['-O2'], ['-O1','-g','-fsanitize=address,undefined','-fno-omit-frame-pointer']]:
                subprocess.run(['g++','-std=c++17','-Wall','-Wextra','-pedantic',*flags,
                                str(cpp),'-o',str(binary)],check=True)
                env = os.environ.copy()
                env['ASAN_OPTIONS'] = 'detect_leaks=0:halt_on_error=1'
                env['UBSAN_OPTIONS'] = 'halt_on_error=1:print_stacktrace=1'
                subprocess.run([str(binary)],env=env,check=True)

    def test_large_arithmetic_without_large_allocations(self):
        with tempfile.TemporaryDirectory(prefix='beats-wide-arithmetic-') as directory:
            root = Path(directory); cpp = root/'check.cpp'; binary = root/'check'
            cpp.write_text('''#include <cassert>
#include <climits>
int main() {
  constexpr unsigned long long n = 1ULL << 28;
  static_assert(4ULL*n <= INT_MAX && 2ULL*n <= INT_MAX);
  static_assert(8ULL*n+8ULL > INT_MAX);
  static_assert(8ULL*n+8ULL == 2147483656ULL);
  constexpr int original_max_n = INT_MAX/4;
  static_assert(8ULL*original_max_n+8ULL == (1ULL<<32));
  int largest_scanned_k = 4*original_max_n-1;
  unsigned long long child = 2ULL*(unsigned long long)largest_scanned_k+2ULL;
  assert(child > INT_MAX && child < 8ULL*original_max_n+8ULL);
}
''')
            subprocess.run(['g++','-std=c++17','-fsanitize=undefined','-fno-sanitize-recover=all',
                            str(cpp),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)

    def test_full_stage_and_body_models_typecheck(self):
        stage = lower_source(CANDIDATE, construction_stages=True)
        body = lower_source(CANDIDATE)
        prefix = stage['functions'][0]['body'][:15]
        self.assertEqual([s['kind'] for s in prefix], ['fill_vector']*15)
        for i in [*range(11),14]:
            self.assertEqual(prefix[i]['count']['type'],
                             {'width':64,'signed':False,'boolean':False})
        def permute(node):
            if isinstance(node,list): return [permute(x) for x in node]
            if not isinstance(node,dict): return node
            out = {key:permute(value) for key,value in node.items()}
            if 'slot' in out and out['slot']<16: out['slot']=(out['slot']+1)%16
            return out
        ctor = next(f for f in body['functions'] if f['name']=='SegmentTreeBeats_new0')
        self.assertEqual(stage['functions'][0]['body'][15:],permute(ctor['body']))
        scan_loop = next(s for s in ctor['body'] if s['kind']=='while')
        scan = scan_loop['body'][0]['body']
        children = [s['value'] for s in scan if s['kind']=='declare' and
                    s['type']=={'width':64,'signed':False,'boolean':False}]
        self.assertEqual(len(children),2)
        # Anchor the general wide-expression theorem to both actual source expressions.
        child_proofs = '\n'.join(
            f'example : ({render_expression(expr)} : Proofs.CppNestedProgram.NExpr) = '
            f'Proofs.BeatsExec.wideChild 19 {d} := rfl'
            for d,expr in enumerate(children,1))
        count_proofs = '\n'.join(
            f'example : ({render_expression(prefix[i]["count"])} : Proofs.CppNestedProgram.NExpr) = '
            'Proofs.BeatsExec.wideCount 0 := rfl'
            for i in [*range(11),14])
        loop_proof = (
            f'def sourceWideCtorLoop : Proofs.CppNestedProgram.Command := {render_commands(scan)}\n'
            'example : sourceWideCtorLoop = Proofs.BeatsExec.WideCtLoopBody 16 := rfl\n'
            f'example : ({render_commands([scan_loop])} : Proofs.CppNestedProgram.Command) = '
            '(.sequence (Proofs.BeatsRep.WideCtLoop1 16) (.primitive .skip)) := rfl\n'
            'example : WideBody.SegmentTreeBeats_new0.body = '
            'Proofs.BeatsRep.WideCtorCmd 16 := rfl\n'
            f'example : ({render_commands(stage["functions"][0]["body"][15:])} : Proofs.CppNestedProgram.Command) = '
            'Proofs.CppSlotRename.command Proofs.BeatsSlotCycle.cycle '
            '(Proofs.BeatsRep.WideCtorCmd 16) := rfl\n'
            f'example : ({render_commands(prefix)} : Proofs.CppNestedProgram.Command) = '
            'Proofs.BeatsAllocation.fillPrefix 0 15 := rfl\n'
            f'example : ({render_commands(stage["functions"][0]["body"])} : Proofs.CppNestedProgram.Command) = '
            'Proofs.BeatsInlineExec.stage 0 15 := rfl\n')
        fields = stage['functions'][0]['construction_fields']
        self.assertEqual([f['slot'] for f in fields],list(range(1,18)))
        layout = stage['functions'][0]['construction_layout']
        self.assertEqual([f['kind'] for f in layout], ['vector']*15+['scalar']*2)
        self.assertEqual([f['slot'] for f in layout], list(range(1,18)))
        field_proofs = ('example : WideStage.SegmentTreeBeats_construct0 = Proofs.BeatsConstructCall.program := rfl\n'
                        'example : WideStage.SegmentTreeBeats_construct0.vectorFields = '
                        'Proofs.BeatsConstructorFields.vectorFields := rfl\n'
                        'example : WideStage.SegmentTreeBeats_construct0.scalarFields = '
                        'Proofs.BeatsConstructorFields.scalarFields := rfl\n'
                        'example (fuel : Nat) (caller : Proofs.CppNestedProgram.NState) '
                        '(args : List Proofs.CppNestedCall.NArgument) : '
                        'WideStage.SegmentTreeBeats_construct0.exportMembersFuel fuel caller args = '
                        'Proofs.BeatsConstructCall.program.constructMembersFuel fuel caller args '
                        'Proofs.BeatsConstructorFields.vectorFields '
                        'Proofs.BeatsConstructorFields.scalarFields := rfl\n')
        public = lower_source(ROOT/'library/segment_tree_beats.hpp')
        old_functions = {f['name']:f for f in public['functions']}
        for function in body['functions']:
            if function['name'] != 'SegmentTreeBeats_new0':
                self.assertEqual(function, old_functions[function['name']])
        models=[emit_lean(stage,'WideStage',constructor_exports=True),emit_lean(body,'WideBody')]
        imports=list(dict.fromkeys(line for model in models for line in model.splitlines()
                                   if line.startswith('import ')))
        text='import Proofs.BeatsReceiverRestore\nimport Proofs.BeatsReceiverCalls\nimport Proofs.BeatsConstructCall\nimport Proofs.BeatsConstructorFields\nimport Proofs.BeatsInlineExec\nimport Proofs.BeatsAllocation\nimport Proofs.BeatsWideExec\nimport Proofs.BeatsWideCtorExec\n'+'\n'.join(imports)+'\n'+'\n'.join(line for model in models for line in model.splitlines()
                                              if not line.startswith('import '))
        text+='\n'+field_proofs+'\n'+child_proofs+'\n'+count_proofs+'\n'+loop_proof+'\n'+(ROOT/'tests/lean/beats_wide_exec.lean').read_text()
        with tempfile.TemporaryDirectory(prefix='beats-wide-model-') as directory:
            proof=Path(directory)/'check.lean'; proof.write_text(text)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,
                                  capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            self.assertNotIn('warning:',result.stdout+result.stderr)


if __name__=='__main__':
    disable_network()
    unittest.main()
