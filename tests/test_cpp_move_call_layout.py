"""Call metadata/heap preservation and reuse of the original ObjectRef across calls."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / 'tools'), str(ROOT / 'tests')]
from test_scalar_ir import lean_environment
from test_cpp_move_receiver_layout import UF_CHECKS, RECEIVER_CHECKS
from test_uf_receiver_layout import CHECKS as FRAME_CHECKS
from test_cpp_move_object_receiver import CHECKS as OBJECT_CHECKS
from test_uf_object_methods import APART_CHECKS
from offline import disable_network
APART_DEFINITIONS = APART_CHECKS[:APART_CHECKS.index('example : ∃ (fuel : Nat)')] + 'end UfObjectApartExamples\n'

CHECKS = r'''

namespace CallLayoutExamples
open Proofs.CppMoveCallLayout Proofs.CppMoveObjectReceiver Proofs.CppMoveContext
open Proofs.CppNestedProgram Proofs.CppMoveReceiverLayout
open UfMoveCallExamples UfReceiverLayoutExamples UfObjectApartExamples

example : ∃ (fuel : Nat) (out : Context) (result : Int) (last : Context),
    Proofs.CppMoveCallBindings.callFuel Proofs.UnionFindCandidateInstance.UnionFind_unite fuel apart ty
      [.vectorReference 3,.scalarReference 4,.value (.variable ty 5),.value (.literal ty 3),.value (.literal ty 1)] =
      .finished (out,.scalar result) ∧
    Nonempty (Receiver out moved.2 ty) ∧
    resolveArguments out ty Proofs.UnionFindCandidateInstance.UnionFind_num_groups.parameters
      [.vectorReference 3,.scalarReference 4,.value (.variable ty 5)] =
      some (last,receiverArguments ⟨1,true⟩ ty 2 true [4]) ∧
    out.scalars.memory[2]? = some ⟨ty,1⟩ := by
  obtain ⟨rank,validUF⟩ := apartValid
  obtain ⟨prepared,initial,vc,fuel,out,r1,r2,middle,two,final,run,compacted,fw,actual,c1,c2,finalEq,newValid,connected,cost,memory,rest⟩ :=
    Proofs.UfObjectMethods.unite_call apart moved.2 receiver ⟨0,apartParents,5,limit,0⟩ rfl rfl
      rank validUF 3 (by decide +kernel) 1 (by decide +kernel)
      (.literal ty 3) rfl rfl (by decide +kernel) (.literal ty 1) rfl rfl (by decide +kernel)
      (by decide +kernel) unique apartCovered apartAllocations rfl (by decide +kernel) apartContexts
  have different : r1 ≠ r2 := fun equal => notConnected (connected.mp equal)
  have update : Proofs.UfFieldsUnite.updatedMemory apart.scalars.memory 2 2 r1 r2 =
      [⟨ty,1⟩,⟨ty,4⟩,⟨ty,1⟩,⟨ty,4⟩] := by
    simp only [Proofs.UfFieldsUnite.updatedMemory,ite_eq_right different]
    rfl
  change out.scalars.memory = Proofs.UfFieldsUnite.updatedMemory apart.scalars.memory 2 2 r1 r2 at memory
  rw [update] at memory
  have layout := call_layout Proofs.UnionFindCandidateInstance.UnionFind_unite fuel apart out ty
    (Proofs.UfObjectCall.arguments apart moved.2 receiver [(.literal ty 3,3),(.literal ty 1,1)])
    (.scalar (Proofs.UfUniteCall.uniteX two r1 r2 : Int)) actual
  have counter : out.scalars.memory[receiver.counter.address]? = some ⟨ty,1⟩ := by rw [memory]; rfl
  have size : out.scalars.memory[receiver.size.address]? = some ⟨ty,4⟩ := by rw [memory]; rfl
  let next := Receiver.update apart out moved.2 ty receiver layout 1 4 counter (by decide +kernel) size (by decide +kernel)
  obtain ⟨last,resolved⟩ := Receiver.resolve out moved.2 ty next [] (by intro e value member; simp at member)
  exact ⟨fuel,out,(Proofs.UfUniteCall.uniteX two r1 r2 : Int),last,actual,⟨next⟩,resolved,counter⟩
end CallLayoutExamples
'''

SEQUENCE_CHECKS = r'''

namespace CallSequenceExamples
open Proofs.CppMoveCallLayout Proofs.CppMoveObjectReceiver Proofs.CppMoveContext
open Proofs.CppNestedProgram Proofs.CppMoveReceiverLayout
open UfMoveCallExamples UfReceiverLayoutExamples UfObjectApartExamples

example : ∃ (fuel getterFuel : Nat) (out final : Context) (result : Int),
    Proofs.CppMoveCallBindings.callFuel Proofs.UnionFindCandidateInstance.UnionFind_unite fuel apart ty
      [.vectorReference 3,.scalarReference 4,.value (.variable ty 5),.value (.literal ty 3),.value (.literal ty 1)] =
      .finished (out,.scalar result) ∧
    Proofs.CppMoveCallBindings.callFuel Proofs.UnionFindCandidateInstance.UnionFind_num_groups getterFuel out ty
      [.vectorReference 3,.scalarReference 4,.value (.variable ty 5)] = .finished (final,.scalar 1) ∧
    final.scalars.memory = out.scalars.memory ∧ final.scalars.memory.map (·.value) = [1,4,1,4] := by
  obtain ⟨rank,validUF⟩ := apartValid
  obtain ⟨prepared,initial,vc,fuel,out,r1,r2,middle,two,final,run,compacted,fw,actual,c1,c2,finalEq,newValid,connected,cost,memory,rest⟩ :=
    Proofs.UfObjectMethods.unite_call apart moved.2 receiver ⟨0,apartParents,5,limit,0⟩ rfl rfl
      rank validUF 3 (by decide +kernel) 1 (by decide +kernel)
      (.literal ty 3) rfl rfl (by decide +kernel) (.literal ty 1) rfl rfl (by decide +kernel)
      (by decide +kernel) unique apartCovered apartAllocations rfl (by decide +kernel) apartContexts
  have different : r1 ≠ r2 := fun equal => notConnected (connected.mp equal)
  have update : Proofs.UfFieldsUnite.updatedMemory apart.scalars.memory 2 2 r1 r2 =
      [⟨ty,1⟩,⟨ty,4⟩,⟨ty,1⟩,⟨ty,4⟩] := by
    simp only [Proofs.UfFieldsUnite.updatedMemory,ite_eq_right different]
    rfl
  change out.scalars.memory = Proofs.UfFieldsUnite.updatedMemory apart.scalars.memory 2 2 r1 r2 at memory
  rw [update] at memory
  have layout := call_layout Proofs.UnionFindCandidateInstance.UnionFind_unite fuel apart out ty
    (Proofs.UfObjectCall.arguments apart moved.2 receiver [(.literal ty 3,3),(.literal ty 1,1)])
    (.scalar (Proofs.UfUniteCall.uniteX two r1 r2 : Int)) actual
  have counter : out.scalars.memory[receiver.counter.address]? = some ⟨ty,1⟩ := by rw [memory]; rfl
  have size : out.scalars.memory[receiver.size.address]? = some ⟨ty,4⟩ := by rw [memory]; rfl
  let next := Receiver.update apart out moved.2 ty receiver layout 1 4 counter (by decide +kernel) size (by decide +kernel)

  let program := Proofs.UnionFindCandidateInstance.UnionFind_unite
  let args := Proofs.UfObjectCall.arguments apart moved.2 receiver [(.literal ty 3,3),(.literal ty 1,1)]
  let result : Ret := .scalar (Proofs.UfUniteCall.uniteX two r1 r2 : Int)
  have afterUnique := call_unique program fuel apart out ty args result actual unique
  have afterCovered := call_ownsAll program fuel apart out ty args result actual apartCovered
  have afterAllocations := call_allocationsValid program fuel apart out ty args result actual
  have afterReadable := call_readable program fuel apart out ty args result actual receiver.header (by decide +kernel)
  have afterContexts := call_contexts program fuel apart out ty args result actual apartCovered apartContexts
  have afterBaseline := Layout.baseline_fits apart out layout (by decide +kernel)
  obtain ⟨prepared2,initial2,vc2,data2,getterFuel,final,run2,compacted2,current2,fw2,actual2,cost2,memory2,rest2⟩ :=
    Proofs.UfObjectCall.counter_call out moved.2 next afterReadable afterUnique afterCovered afterAllocations rfl
      afterBaseline afterContexts
  refine ⟨fuel,getterFuel,out,final,(Proofs.UfUniteCall.uniteX two r1 r2 : Int),actual,actual2,memory2,?_⟩
  rw [memory2,memory]
  rfl
end CallSequenceExamples
'''


class CallLayoutTests(unittest.TestCase):
    def check_lean(self, checks):
        with tempfile.TemporaryDirectory(prefix='call-layout-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.CppMoveCallLayout\nimport Proofs.UfObjectMethods\n'
                'import Proofs.UfClassCopyBridge\n' + UF_CHECKS + RECEIVER_CHECKS + FRAME_CHECKS +
                OBJECT_CHECKS.split('namespace GeneratedObjectReceiverExamples')[0] + APART_DEFINITIONS + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_same_object_receiver_reconstructed_from_updated_fields(self):
        self.check_lean(CHECKS)

    def test_union_then_getter_normal_termination_using_preserved_heap_conditions(self):
        self.check_lean(SEQUENCE_CHECKS)

if __name__ == '__main__':
    disable_network()
    unittest.main()
