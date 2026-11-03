"""Peak composition through actual argument preparation and compact borrowed exit."""
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
from test_cpp_move_receiver_resolve import CHECKS as RESOLVE_CHECKS
from offline import disable_network

PREPARE_CHECKS = r'''
namespace ArgumentOuterExamples
open Proofs.CppMoveArgumentOuter Proofs.CppMoveReceiverResolve Proofs.CppMoveArgumentFacts
open Proofs.CppMoveArgumentWork Proofs.CppMoveContext Proofs.CppNestedProgram
open UfMoveCallExamples ReceiverResolveExamples
example : ∃ out, prepareArguments moved.1 ty (parameters ty expressions) (arguments expressions) = some out ∧
    moved.1.scalars.peak ≤ out.scalars.peak ∧ out.objects.heap = moved.1.objects.heap ∧
    out.peak ≤ max moved.1.peak (out.scalars.peak+moved.1.objects.heap.peak) := by
  obtain ⟨last,resolved⟩ := resolve_values moved.1 ty expressions ready
  obtain ⟨out,prepared,heap,slots⟩ := prepareArguments_of_resolve moved.1 last ty
    (parameters ty expressions) (arguments expressions) _ resolved
  have pure : ∀ argument ∈ arguments expressions, argumentPure argument := by
    simp [arguments,expressions,argumentPure,NExpr.scalarOnly]
  have effects := prepare_effects moved.1 out ty _ _ pure prepared
  exact ⟨out,prepared,effects.scalar,effects.heap,effects.outer⟩
end ArgumentOuterExamples
'''

WEAK_CHECKS = r'''
namespace WeakCallOuterExamples
open Proofs.CppMoveCallOuter Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppMoveArgumentWork
open UfMoveCallExamples ObjectReceiverExamples UfReceiverLayoutExamples
example : ∃ (fuel : Nat) (out : Context),
    Proofs.CppMoveCallBindings.callFuel Proofs.UnionFindCandidateInstance.UnionFind_num_groups fuel moved.1 ty
      (Proofs.UfObjectCall.arguments moved.1 source empty []) = .finished (out,.scalar 1) ∧
    out.peak ≤ max moved.1.peak (out.scalars.peak+out.objects.heap.peak) := by
  obtain ⟨prepared,initial,vc,data,fuel,out,post⟩ :=
    Proofs.UfObjectCall.counter_call moved.1 source empty (by decide +kernel)
      unique covered allocationsValid rfl (by decide +kernel) contexts
  have actual := post.2.2.2.2.1
  have pure : ∀ argument ∈ Proofs.UfObjectCall.arguments moved.1 source empty [], argumentPure argument := by
    simp [Proofs.UfObjectCall.arguments,Proofs.CppMoveReceiverResolve.arguments,argumentPure,NExpr.scalarOnly]
  have bound := call_outer Proofs.UnionFindCandidateInstance.UnionFind_num_groups fuel moved.1 out ty ty _ (.scalar 1)
    pure (by decide +kernel) rfl contexts covered actual
  exact ⟨fuel,out,actual,bound⟩
end WeakCallOuterExamples
'''

class CallOuterTests(unittest.TestCase):
    def check_lean(self, checks):
        with tempfile.TemporaryDirectory(prefix='cpp-move-call-outer-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.CppMoveCallOuter\nimport Proofs.UfObjectCall\nimport Proofs.CppMoveReceiverResolve\n'
                'import Proofs.UfReceiverLayout\nimport Proofs.UfClassCopyBridge\n' +
                UF_CHECKS + RECEIVER_CHECKS + FRAME_CHECKS +
                OBJECT_CHECKS.split('namespace GeneratedObjectReceiverExamples')[0] +
                RESOLVE_CHECKS.split('namespace ReceiverFieldsResolveExamples')[0] + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_real_expression_prepare_preserves_heap_and_composes_peak(self):
        self.check_lean(PREPARE_CHECKS)

    def test_moved_from_weak_getter_uses_generic_outer_bound(self):
        self.check_lean(WEAK_CHECKS)

if __name__ == '__main__':
    disable_network()
    unittest.main()
