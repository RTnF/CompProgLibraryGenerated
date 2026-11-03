"""Scalar peak accounting for real variable/arithmetic argument preparation."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / 'tools'), str(ROOT / 'tests')]
from test_scalar_ir import lean_environment
from test_cpp_move_receiver_layout import UF_CHECKS, RECEIVER_CHECKS
from test_cpp_move_receiver_resolve import CHECKS as RESOLVE_CHECKS
from offline import disable_network

CHECKS = r'''
namespace ArgumentPeakExamples
open Proofs.CppMoveArgumentPeak Proofs.CppMoveReceiverResolve Proofs.CppMoveArgumentFacts
open Proofs.CppMoveArgumentWork Proofs.CppMoveContext Proofs.CppNestedProgram
open UfMoveCallExamples ReceiverResolveExamples

example : ∃ out, prepareArguments moved.1 ty (parameters ty expressions) (arguments expressions) = some out ∧
    out.scalars.peak ≤ 22 := by
  obtain ⟨last,resolved⟩ := resolve_values moved.1 ty expressions ready
  obtain ⟨out,prepared,heap,slots⟩ := prepareArguments_of_resolve moved.1 last ty
    (parameters ty expressions) (arguments expressions) _ resolved
  have pure : ∀ argument ∈ arguments expressions, argumentPure argument := by
    simp [arguments,expressions,argumentPure,NExpr.scalarOnly]
  have peak := prepare_peak moved.1 out ty _ _ pure prepared
  have nodes : argumentsWork (arguments expressions) = 5 := rfl
  have count : (parameters ty expressions).length = 3 := rfl
  rw [nodes,count] at peak
  have bound : max (max moved.1.scalars.peak (scalarLive moved.1+5))
      ((moved.1.scalars.memory.length+moved.1.slots.length+2*3-moved.1.scalars.baseMemory)+2*3) ≤ 22 := by decide +kernel
  exact ⟨out,prepared,peak.trans bound⟩
end ArgumentPeakExamples
'''

class ArgumentPeakTests(unittest.TestCase):
    def test_variable_arithmetic_literal_arguments_include_prepared_scalar_peak(self):
        with tempfile.TemporaryDirectory(prefix='cpp-move-argument-peak-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.CppMoveArgumentPeak\nimport Proofs.CppMoveReceiverResolve\n'
                'import Proofs.UfReceiverLayout\nimport Proofs.UfClassCopyBridge\n' +
                UF_CHECKS + RECEIVER_CHECKS +
                RESOLVE_CHECKS.split('namespace ReceiverFieldsResolveExamples')[0] + CHECKS)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

if __name__ == '__main__':
    disable_network()
    unittest.main()
