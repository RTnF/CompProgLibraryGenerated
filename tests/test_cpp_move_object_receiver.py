"""Physical ObjectRef fields and audited generated receiver argument evaluation."""
from pathlib import Path
import copy
import subprocess
import sys
import tempfile
import unittest
ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / 'verifier'), str(ROOT / 'tools'), str(ROOT / 'tests')]
from context_method_ir import emit_context_methods, lower_context_methods, _object_receiver_profile
from test_scalar_ir import lean_environment
from test_cpp_move_receiver_layout import UF_CHECKS
from offline import disable_network
SOURCE = ROOT / 'experiments/verification/data_structure/union_find.hpp'

CHECKS = r'''

namespace ObjectReceiverExamples
open Proofs.CppMoveObjectReceiver Proofs.CppMoveContext Proofs.CppMoveReceiverResolve
open UfMoveCallExamples

def target : Receiver moved.1 moved.2 ty :=
  ⟨⟨4,2,2,true,1,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,
    ⟨5,3,3,true,4,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,
    rfl,rfl,1,⟨1,true⟩,⟨some 0,0,true,limit⟩,by decide +kernel,by decide +kernel,rfl⟩
example := Receiver.capture moved.1 moved.2 ty target
def ext : List (Proofs.CppNestedProgram.NExpr × Int) := [(.literal ty 3,3)]
theorem ready : Ready moved.1 ty ext := by
  intro expression value member
  simp [ext] at member
  rcases member with ⟨rfl,rfl⟩
  exact ⟨rfl,rfl,by decide +kernel⟩
example := Receiver.resolve moved.1 moved.2 ty target ext ready
example : moved.2.scalarSlots = [target.counter.slot,target.size.slot] := target.fields

def source : Proofs.CppConstructorFinish.ObjectRef := ⟨0,[1,2]⟩
def empty : Receiver moved.1 source ty :=
  ⟨⟨1,0,0,true,1,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,
    ⟨2,1,1,true,4,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,
    rfl,rfl,0,⟨0,true⟩,⟨none,0,true,limit⟩,by decide +kernel,by decide +kernel,rfl⟩
example := Receiver.resolve moved.1 source ty empty [] (by intro e v member; simp at member)
#guard empty.size.value == 4 && empty.counter.value == 1
end ObjectReceiverExamples

namespace GeneratedObjectReceiverExamples
open ObjectReceiverExamples UfMoveCallExamples
open Proofs.CppMoveReceiverResolve Proofs.CppMoveObjectReceiver

def two : List (Proofs.CppNestedProgram.NExpr × Int) := [(.literal ty 3,3),(.literal ty 1,1)]
theorem twoReady : Ready moved.1 ty two := by
  intro expression value member
  simp [two] at member
  rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> exact ⟨rfl,rfl,by decide +kernel⟩
example := ObjectReceiverMethods.«UnionFind_root_resolve_of_receiver» moved.1 moved.2 target ext ready rfl
example := ObjectReceiverMethods.«UnionFind_size_resolve_of_receiver» moved.1 moved.2 target ext ready rfl
example := ObjectReceiverMethods.«UnionFind_same_resolve_of_receiver» moved.1 moved.2 target two twoReady rfl
example := ObjectReceiverMethods.«UnionFind_unite_resolve_of_receiver» moved.1 moved.2 target two twoReady rfl
example := ObjectReceiverMethods.«UnionFind_num_groups_resolve_of_receiver» moved.1 moved.2 target [] (by intro e v member; simp at member) rfl

example := ObjectReceiverMethods.«UnionFind_num_groups_resolve_of_receiver» moved.1 source empty []
  (by intro e v member; simp at member) rfl
example := ObjectReceiverMethods.«UnionFind_root_arguments_of_fields» moved.2
  (arguments ext) target.counter.slot target.size.slot target.fields (by decide +kernel)
end GeneratedObjectReceiverExamples
'''


RENAMED = r'''
#include <vector>
namespace alternate {struct Store {
  std::vector<int> entries;
  int updates;
  int scale;
  int value(int index){updates=updates+1;return entries[index]+scale;}
};}
'''

class ObjectReceiverTests(unittest.TestCase):
    def check_lean(self, text):
        with tempfile.TemporaryDirectory(prefix='object-receiver-') as directory:
            proof = Path(directory) / 'check.lean'
            proof.write_text(text)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_original_object_fields_and_generated_all_method_resolution(self):
        generated = emit_context_methods(SOURCE, 'cp::UnionFind', 'ObjectReceiverMethods')
        for name in ('root', 'size', 'same', 'unite', 'num_groups'):
            self.assertIn('UnionFind_' + name + '_resolve_of_receiver', generated)
        self.check_lean('import Proofs.UfClassCopyBridge\nimport Proofs.UfReceiverLayout\n'
            'import Proofs.UfFieldsSize\nimport Proofs.UfFieldsUnite\n' + generated + UF_CHECKS + CHECKS)

    def test_structural_profile_and_renamed_source(self):
        ir = lower_context_methods(SOURCE, 'cp::UnionFind')
        for method in ir['methods']:
            self.assertTrue(_object_receiver_profile(method))
        original = next(method for method in ir['methods'] if method['arguments'])
        for kind in ('vector_permission', 'counter_mode', 'size_mode', 'external_reference', 'field_type'):
            method = copy.deepcopy(original)
            if kind == 'vector_permission': method['fields'][0]['writable'] = False
            elif kind == 'counter_mode': method['fields'][1]['reference'] = False
            elif kind == 'size_mode': method['fields'][2]['reference'] = True
            elif kind == 'external_reference': method['program']['parameters'][3]['reference'] = True
            elif kind == 'field_type': method['fields'][2]['element'] = {'unsupported': True}
            self.assertFalse(_object_receiver_profile(method), kind)
        with tempfile.TemporaryDirectory(prefix='object-receiver-source-') as directory:
            source = Path(directory) / 'renamed.hpp'
            source.write_text(RENAMED)
            generated = emit_context_methods(source, 'alternate::Store', 'RenamedObjectMethods')
            self.assertIn('Store_value_resolve_of_receiver', generated)
            self.assertIn('Store_value_arguments_of_fields', generated)
            self.check_lean(generated)

if __name__ == '__main__':
    disable_network()
    unittest.main()
