"""Actual pure-expression evaluation and argument preparation work bounds."""
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
namespace ArgumentWorkExamples
open Proofs.CppMoveArgumentWork Proofs.CppMoveReceiverResolve Proofs.CppMoveArgumentFacts
open Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppNestedEval
open UfMoveCallExamples ReceiverResolveExamples

-- Variable read, arithmetic and literal: five expression nodes and three parameters.
example : ∃ out, prepareArguments moved.1 ty (parameters ty expressions) (arguments expressions) = some out ∧
    work moved.1 ≤ work out ∧ work out ≤ work moved.1 + 9 := by
  obtain ⟨last,resolved⟩ := resolve_values moved.1 ty expressions ready
  obtain ⟨out,prepared,heap,slots⟩ := prepareArguments_of_resolve moved.1 last ty
    (parameters ty expressions) (arguments expressions) _ resolved
  have pure : ∀ argument ∈ arguments expressions, argumentPure argument := by
    simp [arguments,expressions,argumentPure,NExpr.scalarOnly]
  have bound := prepare_work moved.1 out ty _ _ pure prepared
  have nodes : argumentsWork (arguments expressions) = 5 := rfl
  have count : (parameters ty expressions).length = 3 := rfl
  rw [nodes,count] at bound
  exact ⟨out,prepared,bound.1,by omega⟩

#guard (prepareArguments moved.1 ty [] [.value (.literal ty 1)]).isNone
#guard (prepareArguments moved.1 ty [.scalar ty true true] [.value (.literal ty 1)]).isNone
end ArgumentWorkExamples
'''

UNSIGNED_CHECKS = r'''
namespace UnsignedArgumentWorkExamples
open Proofs.CppMoveArgumentWork Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppNestedEval
open UfMoveCallExamples

def uint32 : Proofs.CppScalar.Ty := ⟨32,false,false⟩
def wrapped : NExpr := .binary uint32 .add (.literal uint32 4294967295) (.literal uint32 1)

-- The vector projection type remains i32; the pure expression itself is unsigned32.
example : ∃ out, evalExpression moved.1 ty wrapped = some (out,0) ∧
    work moved.1 ≤ work out ∧ work out ≤ work moved.1 + 3 := by
  obtain ⟨next,actual⟩ := denote_complete wrapped (project moved.1 ty) 0 rfl (by decide +kernel)
  have evaluated : evalExpression moved.1 ty wrapped = some (resumeExpression moved.1 next,0) := by
    simp only [evalExpression,actual,Bind.bind,Option.bind]
  have bound := eval_work moved.1 (resumeExpression moved.1 next) ty wrapped 0 rfl evaluated
  exact ⟨resumeExpression moved.1 next,evaluated,bound⟩

#guard (evalExpression moved.1 ty (.binary ty .add (.literal ty 2147483647) (.literal ty 1))).isNone
end UnsignedArgumentWorkExamples
'''

class ArgumentWorkTests(unittest.TestCase):
    def check_lean(self, checks):
        with tempfile.TemporaryDirectory(prefix='cpp-move-argument-work-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.CppMoveArgumentWork\nimport Proofs.CppMoveReceiverResolve\nimport Proofs.UfReceiverLayout\nimport Proofs.UfClassCopyBridge\n' +
                UF_CHECKS + RECEIVER_CHECKS +
                RESOLVE_CHECKS.split('namespace ReceiverFieldsResolveExamples')[0] + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_variable_arithmetic_arguments_and_preparation_cost(self):
        self.check_lean(CHECKS)

    def test_unsigned_expression_work_and_signed_overflow_rejection(self):
        self.check_lean(UNSIGNED_CHECKS)

if __name__ == '__main__':
    disable_network()
    unittest.main()
