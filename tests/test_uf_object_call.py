"""Original UF ObjectRef normal root/getter calls and audited generated wrappers."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / 'verifier'), str(ROOT / 'tools'), str(ROOT / 'tests')]
from context_method_ir import emit_context_methods
from test_scalar_ir import lean_environment
from test_cpp_move_object_receiver import CHECKS as OBJECT_CHECKS
from test_cpp_move_receiver_layout import UF_CHECKS, RECEIVER_CHECKS
from test_uf_receiver_layout import CHECKS as FRAME_CHECKS
from offline import disable_network

CHECKS = r'''

namespace UfObjectNormalCallExamples
open Proofs.CppMoveContext Proofs.CppMoveReceiverResolve Proofs.CppMoveFrame Proofs.CppVector
open UfMoveCallExamples ObjectReceiverExamples UfReceiverLayoutExamples

-- The general theorem supplies every setup state and the complete resource post.
example := Proofs.UfObjectCall.root_call moved.1 moved.2 target ⟨0,parents,5,limit,0⟩ rfl rfl
  ranks parentForest (by decide +kernel) 3 (by decide +kernel) (.literal ty 3) rfl rfl
  (by decide +kernel) (by decide +kernel) unique covered allocationsValid rfl (by decide +kernel) contexts
example := Proofs.UfObjectCall.counter_call moved.1 source empty (by decide +kernel)
  unique covered allocationsValid rfl (by decide +kernel) contexts
example := Proofs.UfObjectCall.counter_call moved.1 moved.2 target (by decide +kernel)
  unique covered allocationsValid rfl (by decide +kernel) contexts

example : ∃ (fuel : Nat) (out : Context) (r : Nat) (final : List Int),
    ObjectReceiverMethods.«UnionFind_root_callFuel» fuel moved.1 moved.2
      [.value (.binary ty .add (.literal ty 2) (.literal ty 1))] = .finished (out,.scalar (r : Int)) ∧
    Proofs.UfCompression.Compressed parents final 3 r := by
  obtain ⟨prepared,initial,vc,fuel,out,r,final,run,compacted,fw,actual,compressed,rest⟩ :=
    Proofs.UfObjectCall.root_call moved.1 moved.2 target ⟨0,parents,5,limit,0⟩ rfl rfl
      ranks parentForest (by decide +kernel) 3 (by decide +kernel)
      (.binary ty .add (.literal ty 2) (.literal ty 1)) rfl rfl
      (by decide +kernel) (by decide +kernel) unique covered allocationsValid rfl (by decide +kernel) contexts
  have mapped := ObjectReceiverMethods.«UnionFind_root_arguments_of_fields» moved.2
    [.value (.binary ty .add (.literal ty 2) (.literal ty 1))] target.counter.slot target.size.slot target.fields rfl
  refine ⟨fuel,out,r,final,?_,compressed⟩
  rw [ObjectReceiverMethods.«UnionFind_root_call_of_arguments» fuel moved.1 moved.2 _ _ mapped]
  exact actual

-- The moved-from source has empty vector storage and still returns count=1.
example : ∃ (fuel : Nat) (out : Context),
    ObjectReceiverMethods.«UnionFind_num_groups_callFuel» fuel moved.1 source [] = .finished (out,.scalar 1) := by
  obtain ⟨prepared,initial,vc,data,fuel,out,run,compacted,current,fw,actual,rest⟩ :=
    Proofs.UfObjectCall.counter_call moved.1 source empty (by decide +kernel)
      unique covered allocationsValid rfl (by decide +kernel) contexts
  have mapped := ObjectReceiverMethods.«UnionFind_num_groups_arguments_of_fields» source []
    empty.counter.slot empty.size.slot empty.fields rfl
  refine ⟨fuel,out,?_⟩
  rw [ObjectReceiverMethods.«UnionFind_num_groups_call_of_arguments» fuel moved.1 source [] _ mapped]
  exact actual
end UfObjectNormalCallExamples
'''


class UfObjectCallTests(unittest.TestCase):
    def test_source_object_normal_calls_and_generated_wrapper_termination(self):
        generated = emit_context_methods(ROOT / 'experiments/verification/data_structure/union_find.hpp',
            'cp::UnionFind', 'ObjectReceiverMethods')
        with tempfile.TemporaryDirectory(prefix='uf-object-call-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.UfObjectCall\nimport Proofs.UfClassCopyBridge\n'
                'import Proofs.UfFieldsSize\nimport Proofs.UfFieldsUnite\n' + generated +
                UF_CHECKS + RECEIVER_CHECKS + FRAME_CHECKS + OBJECT_CHECKS + CHECKS)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

if __name__ == '__main__':
    disable_network()
    unittest.main()
