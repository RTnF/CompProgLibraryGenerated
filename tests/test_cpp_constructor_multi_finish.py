"""Export actual constructor fields with updated caller cells and usable grants."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import copy

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT/'tools'), str(ROOT/'tests'), str(ROOT/'verifier')]
from offline import disable_network
from test_scalar_ir import lean_environment
from nested_ir import lower_source, emit_lean

SOURCE = '''#include <vector>
struct Bundle {
 std::vector<int> first, second; int captured, seen;
 Bundle(int &outside): first(2,outside),second(1,4),captured(outside),seen(0) {
   outside=9; second[0]=outside; seen=captured;
 }
};
'''
CHECKS = r'''
namespace GeneratedMultiFinishExamples
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop
open Proofs.CppConstructorMultiFinish
abbrev i32 : Ty := ⟨32,true,false⟩
def caller : NState := ⟨⟨[⟨i32,7⟩,⟨i32,13⟩],[⟨0,true⟩,⟨1,false⟩,⟨0,true⟩],3,1,3⟩,
  ⟨⟨⟨[some ⟨.integer i32,none,some 2,[]⟩]⟩,
    {objects := [some ⟨0,[.integer 101],1,64,5⟩],work := 7,baseSpace := 1,peak := 2}⟩,
    [false],[⟨0,.integer i32,false,.root 2⟩]⟩,
  [.scalar 0,.vector 0,.scalar 2,.scalar 1],2,5⟩
def vectors : List VectorField := [⟨1,.integer i32⟩,⟨2,.integer i32⟩]
def scalars : List Proofs.CppConstructorFinish.ScalarField := [⟨3,i32⟩,⟨4,i32⟩]
example : GeneratedBundle.Bundle_construct0.vectorFields = vectors := rfl
example : GeneratedBundle.Bundle_construct0.scalarFields = scalars := rfl
def make := GeneratedBundle.Bundle_construct0.exportMembersFuel 64 caller [.scalarReference 0]
def out : NState := match make with | .finished (s,_) => s | _ => caller
def object : ObjectRef := reference caller 2 2
example : make = .finished (out,object) := by decide +kernel
#guard object.vectorSlots == [4,5]
#guard object.scalarSlots == [6,7]
#guard out.scope == 2
#guard out.scalars.memory == [⟨i32,9⟩,⟨i32,13⟩,⟨i32,7⟩,⟨i32,7⟩]
#guard out.scalars.bindings == [⟨0,true⟩,⟨1,false⟩,⟨0,true⟩,⟨2,true⟩,⟨3,true⟩]
#guard out.scalarCell 2 i32 == some (⟨0,true⟩,⟨i32,9⟩)
#guard out.scalarCell 3 i32 == some (⟨1,false⟩,⟨i32,13⟩)
#guard out.scalars.baseMemory == 1
#guard out.frame.state.storage.baseSpace == 1
#guard out.frame.bindings == [⟨0,.integer i32,false,.root 2⟩,
  ⟨1,.integer i32,true,.root 2⟩,⟨2,.integer i32,true,.root 2⟩]
#guard (out.frame.state.storage.lookup 0).map (·.items) == some [.integer 101]
#guard (out.frame.state.storage.lookup 1).map (·.items) == some [.integer 7,.integer 7]
#guard (out.frame.state.storage.lookup 2).map (·.items) == some [.integer 9]
#guard (out.frame.resolve 1 (.integer i32)).isSome
#guard (out.frame.resolve 2 (.integer i32)).isSome
#guard (out.frame.elementRef 2 i32 0).bind (fun ref =>
  (out.frame.write ref 23).bind (fun f => (f.state.storage.lookup 2).map (·.items))) == some [.integer 23]
#guard out.frame.state.wellFormed
#guard GeneratedBundle.Bundle_construct0.constructMembersFuel 0 caller [.scalarReference 0] vectors scalars == .exhausted
end GeneratedMultiFinishExamples
'''


class ConstructorMultiFinishTests(unittest.TestCase):
    def check_lean(self, directory, text):
        proof = Path(directory)/'check.lean'
        proof.write_text('import Proofs.CppConstructorMultiFinish\n'+text)
        lake, env = lean_environment()
        result = subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,
                                capture_output=True,text=True)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertNotIn('warning:',result.stdout+result.stderr)

    def test_nested_members_grants_and_general_finish_theorem(self):
        with tempfile.TemporaryDirectory(prefix='constructor-multi-model-') as directory:
            self.check_lean(directory,'\n'.join((ROOT/'tests/lean'/name).read_text() for name in
                ['cpp_constructor_roots.lean','cpp_constructor_multi_finish.lean']))

    def test_generated_constructor_exports_fields_and_keeps_caller_writes(self):
        with tempfile.TemporaryDirectory(prefix='constructor-multi-source-') as directory:
            source = Path(directory)/'source.hpp'
            source.write_text(SOURCE)
            ir = lower_source(source, construction_stages=True)
            self.assertEqual(ir['functions'][0]['construction_fields'],[
                {'name':'first','slot':1},{'name':'second','slot':2},
                {'name':'captured','slot':3},{'name':'seen','slot':4}])
            fields = ir['functions'][0]['construction_layout']
            self.assertEqual([(f['name'], f['slot'], f['kind']) for f in fields],
                             [('first',1,'vector'),('second',2,'vector'),
                              ('captured',3,'scalar'),('seen',4,'scalar')])
            self.check_lean(directory,emit_lean(ir,'GeneratedBundle',constructor_exports=True)+CHECKS)
            cpp = Path(directory)/'check.cpp'
            cpp.write_text('#include "source.hpp"\n#include <cassert>\nint main(){'
                'int x=7;Bundle b(x);assert(x==9);assert(b.first==std::vector<int>({7,7}));'
                'assert(b.second==std::vector<int>({9}));assert(b.captured==7);assert(b.seen==7);'
                'b.second[0]=23;assert(b.second[0]==23);}')
            binary = Path(directory)/'native'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined',
                            '-fno-sanitize-recover=all',str(cpp),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)

    def test_constructor_export_layout_rejects_invalid_metadata(self):
        with tempfile.TemporaryDirectory(prefix='constructor-multi-layout-') as directory:
            source = Path(directory)/'source.hpp'
            source.write_text(SOURCE)
            ir = lower_source(source, construction_stages=True)
        legacy = copy.deepcopy(ir)
        del legacy['functions'][0]['construction_layout']
        self.assertEqual(emit_lean(ir), emit_lean(legacy))
        with self.assertRaisesRegex(ValueError, 'typed constructor field layout required'):
            emit_lean(legacy, constructor_exports=True)
        for label, key, value in [
            ('name', 'name', 'other'), ('slot', 'slot', 99),
            ('boolean slot', 'slot', True), ('negative slot', 'slot', -1),
            ('kind', 'kind', 'array'), ('writable', 'writable', 1),
            ('mutable', 'mutable', None),
        ]:
            with self.subTest(label=label):
                invalid = copy.deepcopy(ir)
                invalid['functions'][0]['construction_layout'][0][key] = value
                with self.assertRaisesRegex(ValueError, 'constructor field layout'):
                    emit_lean(invalid, constructor_exports=True)
        swapped = copy.deepcopy(ir)
        swapped['functions'][0]['construction_layout'].reverse()
        with self.assertRaisesRegex(ValueError, 'constructor field layout'):
            emit_lean(swapped, constructor_exports=True)
        duplicate = copy.deepcopy(ir)
        duplicate['functions'][0]['construction_layout'][1]['slot'] = 1
        duplicate['functions'][0]['construction_fields'][1]['slot'] = 1
        with self.assertRaisesRegex(ValueError, 'constructor field layout'):
            emit_lean(duplicate, constructor_exports=True)

    def test_interleaved_const_and_nested_fields_export_actual_permissions(self):
        source_text = '''#include <vector>
struct Mixed {
 const int frozen;
 std::vector<std::vector<int>> rows;
 mutable int marker;
 const std::vector<int> fixed;
 Mixed(int v):frozen(v),rows(2),marker(v+1),fixed(1,v+2) { marker+=1; }
};
'''
        checks = r'''
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop
abbrev i32 : Ty := ⟨32,true,false⟩
def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
example : MixedGenerated.Mixed_construct0.vectorFields =
  [⟨2,.vector (.integer i32)⟩,⟨4,.integer i32⟩] := rfl
example : MixedGenerated.Mixed_construct0.scalarFields = [⟨1,i32⟩,⟨3,i32⟩] := rfl
def make := MixedGenerated.Mixed_construct0.exportMembersFuel 64 empty [.value (.literal i32 7)]
def out : NState := match make with | .finished (s,_) => s | _ => empty
example : make = .finished (out,⟨[0,1],[2,3]⟩) := by decide +kernel
#guard out.scope == 0
#guard out.scalars.memory == [⟨i32,7⟩,⟨i32,9⟩]
#guard out.scalars.bindings == [⟨0,false⟩,⟨1,true⟩]
#guard out.frame.bindings == [⟨0,.vector (.integer i32),true,.root 0⟩,
  ⟨3,.integer i32,false,.root 0⟩]
#guard (out.frame.state.storage.lookup 0).map (·.items.length) == some 2
#guard (out.frame.state.storage.lookup 1).map (·.items) == some []
#guard (out.frame.state.storage.lookup 2).map (·.items) == some []
#guard (out.frame.state.storage.lookup 3).map (·.items) == some [.integer 9]
#guard out.frame.state.wellFormed
#guard (out.frame.elementRef 1 i32 0).bind (fun ref => out.frame.write ref 23) |>.isNone
'''
        with tempfile.TemporaryDirectory(prefix='constructor-multi-mixed-') as directory:
            source = Path(directory)/'source.hpp'
            source.write_text(source_text)
            ir = lower_source(source, construction_stages=True)
            fields = ir['functions'][0]['construction_layout']
            self.assertEqual([(f['name'],f['slot'],f['kind'],f['writable'],f['mutable']) for f in fields],
                             [('frozen',1,'scalar',False,False),('rows',2,'vector',True,False),
                              ('marker',3,'scalar',True,True),('fixed',4,'vector',False,False)])
            self.check_lean(directory,emit_lean(ir,'MixedGenerated',constructor_exports=True)+checks)
            cpp = Path(directory)/'check.cpp'
            cpp.write_text('#include "source.hpp"\n#include <cassert>\n#include <type_traits>\n'
                'int main(){const Mixed x(7);static_assert(std::is_const_v<decltype(x.frozen)>);'
                'static_assert(std::is_const_v<decltype(x.fixed)>);'
                'assert(x.frozen==7 && x.marker==9);assert(x.rows.size()==2);'
                'assert(x.rows[0].empty() && x.rows[1].empty());'
                'assert(x.fixed==std::vector<int>({9}));x.marker=23;assert(x.marker==23);}')
            binary = Path(directory)/'native'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined',
                            '-fno-sanitize-recover=all',str(cpp),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)

    def test_shared_command_parts_preserve_the_entire_program(self):
        with tempfile.TemporaryDirectory(prefix='constructor-command-sharing-') as directory:
            source = Path(directory)/'source.hpp'
            repeated = 'outside=9;'*70
            source.write_text(SOURCE.replace('outside=9;',
                'if(outside>0){'+repeated+'}else{'+repeated+'}'))
            ir = lower_source(source, construction_stages=True)
            plain = emit_lean(ir,'PlainCommands')
            shared = emit_lean(ir,'SharedCommands',constructor_exports=True,share_commands=True)
            self.assertIn('private def «Bundle_construct0».commandPart',shared)
            self.assertNotIn('set_option',shared)
            models = [plain,shared]
            imports = list(dict.fromkeys(line for model in models for line in model.splitlines()
                                         if line.startswith('import ')))
            bodies = '\n'.join(line for model in models for line in model.splitlines()
                               if not line.startswith('import '))
            self.check_lean(directory,'\n'.join(imports)+'\n'+bodies+
                '\nexample : SharedCommands.Bundle_construct0 = PlainCommands.Bundle_construct0 := rfl\n')


if __name__=='__main__':
    disable_network()
    unittest.main()
