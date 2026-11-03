"""Outer history remains separate from monotone scalar/storage components."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_dynamic_expr import fixture_checks
from test_cpp_no_resize import CHECKS as SCALAR_CHECKS
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
CHECKS = '''
open Proofs.CppEvalPeak Proofs.CppPeakComponents
 def successful : List NExpr := [rowRead,rowSize,rootSize,combined,.literal i32 7,.variable i32 3,
   .cast i32 rootSize,.targetCast i32 rootSize,.unary i32 .neg rowRead,
   .divrem i32 false rowRead (.literal i32 2),.divrem i32 true rowRead (.literal i32 2),
   .logical true (.literal i32 0) bad,.logical false (.literal i32 1) bad,
   .logical true (.literal i32 1) rowRead,.logical false (.literal i32 0) rowRead,
   .read i32 (.local 2) (.literal i32 0),.size atom (.local 2)]
 def output (e : NExpr) : NState × Int := (e.eval state).getD (state,0)
 theorem evaluated : successful.all (fun e => decide (e.eval state = some (output e))) = true := by decide +kernel
 theorem eachGrows (e : NExpr) (member : e ∈ successful) : Grows state (output e).1 := by
   apply expression_peak e state (output e).1 (output e).2
   simpa only [decide_eq_true_eq] using List.all_eq_true.mp evaluated e member
 example (e : NExpr) (member : e ∈ successful) := (eachGrows e member).outer
 #guard successful.all (fun e => state.scalars.peak <= (output e).1.scalars.peak &&
   state.frame.state.storage.peak <= (output e).1.frame.state.storage.peak &&
   (output e).1.peak <= max state.peak ((output e).1.scalars.peak+(output e).1.frame.state.storage.peak))
 def rowResult : NState := (output rowRead).1
 example := (expression_peak rowRead state rowResult (-3) (by decide +kernel)).trans (release rowResult state)
 #guard rowResult.frame.bindings.length == state.frame.bindings.length+1
 #guard (rowResult.release state).frame.bindings == state.frame.bindings
 #guard (rowResult.release state).scalars.peak == rowResult.scalars.peak
 example := Proofs.CppStmtPeak.scalar_peak action state declared rfl (by decide +kernel)
 example := Proofs.CppStmtPeak.scalar_peak assignment state assigned rfl (by decide +kernel)
 example := Proofs.CppStmtPeak.primitive (.ret rowRead) state returned rfl (by decide +kernel)
 example := Proofs.CppStmtPeak.primitive (.check rowSize) state checked rfl (by decide +kernel)
 example := Proofs.CppStmtPeak.write_peak state written (.row (.local 0) atom idx) i32 pos (.literal i32 42) (by decide +kernel)
 def historic : NState := {state with peak := 100000000}
 def historicOutput := (rowRead.eval historic).getD (historic,0)
 theorem historicGrowth : Grows historic historicOutput.1 := expression_peak rowRead historic historicOutput.1 historicOutput.2 (by decide +kernel)
 #guard historicOutput.1.peak == 100000000
 #guard historicOutput.1.peak > historicOutput.1.scalars.peak+historicOutput.1.frame.state.storage.peak
 example := historicGrowth.bound historicOutput.1.scalars.peak historicOutput.1.frame.state.storage.peak (Nat.le_refl _) (Nat.le_refl _)
 def scalarHistoric : NState := {state with peak := 0,scalars := {state.scalars with peak := 100000000}}
 def scalarOutput := (rowRead.eval scalarHistoric).getD (scalarHistoric,0)
 example := expression_peak rowRead scalarHistoric scalarOutput.1 scalarOutput.2 (by decide +kernel)
 #guard scalarOutput.1.peak >= 100000000
 #guard scalarOutput.1.scalars.peak >= scalarHistoric.scalars.peak
 example (e : NExpr) (s t : NState) (v : Int) (ran : e.eval s = some (t,v)) := expression_peak e s t v ran
 example (container : Container) (s t : NState) (v : Nat) (ran : container.eval s = some (t,v)) := container_peak container s t v ran
 example (stmt : NStmt) (s : NState) (out : NStep)
   (allowed : Proofs.CppNoResizeStmt.Allowed stmt = true) (ran : stmt.run s = some out) :=
   Proofs.CppStmtPeak.primitive stmt s out allowed ran
'''

class PeakComponentTests(unittest.TestCase):
    def test_nested_expressions_primitives_and_large_history(self):
        with tempfile.TemporaryDirectory(prefix='cpp-peak-components-') as directory:
            proof = Path(directory)/'checks.lean'
            proof.write_text('import Proofs.CppStmtPeak\nimport Proofs.Generated.UnionFindCandidate\n'
                             +'\n'.join(fixture_checks())+SCALAR_CHECKS+CHECKS)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)

if __name__ == '__main__':
    disable_network()
    unittest.main()
