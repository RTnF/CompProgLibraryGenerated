"""Argument evaluation data/type invariants and preparation correspondence."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parent.parent
sys.path[:0]=[str(ROOT/'tools'),str(ROOT/'tests')]
from test_scalar_ir import lean_environment
from test_cpp_move_headers import CHECKS as HEADER_CHECKS
from test_cpp_move_frame import CHECKS as FRAME_CHECKS
from test_cpp_move_write import CHECKS as WRITE_CHECKS
from test_cpp_move_context import CHECKS as CONTEXT_CHECKS
from offline import disable_network

CHECKS = r'''
namespace ArgumentFactsExamples
open Proofs.CppMoveArgumentFacts Proofs.CppMoveContext ContextExamples FrameExamples
example := evalExpression_correspondence callerContext ty arithmetic
example (out : Context) (value : Int) (run : evalExpression callerContext ty arithmetic = some (out,value)) : Stable callerContext out :=
  evalExpression_stable callerContext out ty arithmetic value run
example (out : Context) (saved : List SavedArgument)
    (run : resolveArguments callerContext ty expressionParameters expressionArguments = some (out,saved)) : Stable callerContext out :=
  resolveArguments_stable callerContext out ty expressionParameters expressionArguments saved run

def resolved := (resolveArguments callerContext ty expressionParameters expressionArguments).getD (callerContext,[])
theorem resolvedRun : resolveArguments callerContext ty expressionParameters expressionArguments = some resolved := by
  have live : (resolveArguments callerContext ty expressionParameters expressionArguments).isSome = true := by decide +kernel
  have nonempty : resolveArguments callerContext ty expressionParameters expressionArguments ≠ none := by
    intro missing
    simp [missing] at live
  exact (Option.getD_of_ne_none nonempty (callerContext,[])).symm
theorem resolvedStable : Stable callerContext resolved.1 :=
  resolveArguments_stable callerContext resolved.1 ty expressionParameters expressionArguments resolved.2 resolvedRun
#guard resolved.1.slots == callerContext.slots
#guard resolved.1.scalars.memory == callerContext.scalars.memory
#guard resolved.1.scalars.bindings == callerContext.scalars.bindings
#guard work resolved.1 > work callerContext
#guard resolved.2.length == 5
example : SavedReady resolved.1 (.scalar ⟨ty,true,true⟩ (.reference 0)) :=
  stable_savedReady callerContext resolved.1 _ resolvedStable ⟨⟨ty,7⟩,rfl,rfl,rfl,by decide⟩
example := captureBorrow_ready callerContext 3 true targetArgument rfl
example := captureScalarReference_ready callerContext ty 1 true (.scalar ⟨ty,true,true⟩ (.reference 0)) (by decide +kernel)

example := resolveArguments_ready callerContext resolved.1 ty expressionParameters expressionArguments resolved.2 resolvedRun
example := prepareArguments_of_resolve callerContext resolved.1 ty expressionParameters expressionArguments resolved.2 resolvedRun
example := resolveArguments_lengths callerContext resolved.1 ty expressionParameters expressionArguments resolved.2 resolvedRun
theorem expressionPreparedRun : prepareArguments callerContext ty expressionParameters expressionArguments = some expressionPrepared := by
  have live : (prepareArguments callerContext ty expressionParameters expressionArguments).isSome = true := by decide +kernel
  have nonempty : prepareArguments callerContext ty expressionParameters expressionArguments ≠ none := by intro missing; simp [missing] at live
  exact (Option.getD_of_ne_none nonempty callerContext).symm
example := prepareArguments_resources callerContext resolved.1 expressionPrepared ty expressionParameters expressionArguments resolved.2
  resolvedRun expressionPreparedRun (by decide)
example := convert_valid (⟨8,false,false⟩ : Proofs.CppScalar.Ty) (-1) 255 (by decide)
example := targetConvert_valid (⟨32,true,false⟩ : Proofs.CppScalar.Ty) (2^31) (-(2^31)) (by decide +kernel)
#guard (evalExpression callerContext ty (.logical true (.literal ty 0) (.read ty (.local 3) (.literal ty 99)))).map Prod.snd == some 0
#guard (evalExpression callerContext ty (.logical false (.literal ty 1) (.read ty (.local 3) (.literal ty 99)))).map Prod.snd == some 1
#guard (evalExpression callerContext ty (.logical false (.literal ty 0) (.read ty (.local 3) (.literal ty 99)))).isNone
#guard (evalExpression callerContext ty (.divrem ty false (.literal ty (-(2^63))) (.literal ty (-1)))).isNone
end ArgumentFactsExamples
'''

class MoveArgumentFactsTests(unittest.TestCase):
    def test_evaluation_invariants_types_and_preparation(self):
        with tempfile.TemporaryDirectory(prefix='move-arguments-') as directory:
            proof=Path(directory)/'checks.lean'
            proof.write_text('import Proofs.CppMoveArgumentFacts\n'+HEADER_CHECKS+FRAME_CHECKS+WRITE_CHECKS+CONTEXT_CHECKS+CHECKS)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)

if __name__=='__main__':
    disable_network()
    unittest.main()
