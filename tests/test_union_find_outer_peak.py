"""Outer peak across control, general calls, and actual UF finite histories."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_dynamic_expr import fixture_checks
from test_cpp_no_resize import CHECKS as SCALAR_CHECKS
from test_cpp_call_metadata import CONTROL
from test_union_find_construction import HEADER
from test_union_find_original_api import HEADER as CALLER_HEADER
from test_union_find_construction_footprint import CHECKS as STAGE_CHECKS
from test_union_find_constructed_receiver import CHECKS as RECEIVER_CHECKS
from test_union_find_receiver_trace import CHECKS as TRACE_CHECKS
from test_union_find_rank_doubling import CHECKS as RANK_CHECKS
from test_union_find_storage_peak import UF as STORAGE_CHECKS
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
NESTED = '''
 example := Proofs.CppPeakRun.run_grows 128 flowBody state result (by decide +kernel) contexts (by decide +kernel)
 example := Proofs.CppPeakRun.run_grows 32 early state earlyResult (by decide +kernel) contexts (by decide +kernel)
 example := Proofs.CppPeakRun.run_grows 16 broken state brokenResult rfl contexts (by decide +kernel)
 example := Proofs.CppCallPeak.call_peak nestedProgram 8 state nestedOut nestedArgs (.scalar (-3)) i32
   rfl rfl contexts (by decide +kernel)
 #guard result.state.peak <= max state.peak (result.state.scalars.peak+result.state.frame.state.storage.peak)
 #guard earlyResult.state.peak <= max state.peak (earlyResult.state.scalars.peak+earlyResult.state.frame.state.storage.peak)
 #guard brokenResult.state.scalars.peak >= state.scalars.peak
 def multiProgram : Proofs.CppNestedCall.NProgram :=
   ⟨[.nested i32 false,.vector i32 false,.scalar i32 true false,.scalar i32 false false],.scalar i32,
     .primitive (.ret (.binary i32 .add (.read i32 (.local 1) (.literal i32 0)) (.variable i32 3)))⟩
 def multiArgs : List Proofs.CppNestedCall.NArgument := [.vectorReference 1,.vectorReference 2,.scalarReference 3,.value rowRead]
 def multiInit : NState := (Proofs.CppNestedCall.prepare state multiProgram.parameters multiArgs).getD state
 example := Proofs.CppPreparePeak.prepare_peak state multiInit multiProgram.parameters multiArgs (by decide +kernel)
 #guard multiInit.vectorSlot 0 == some 0 && multiInit.vectorSlot 1 == some 1
 #guard multiInit.frame.bindings.length == 2
 def multiOut : NState := match multiProgram.callFuel 16 state multiArgs with
   | .finished (out,_) => out | _ => state
 theorem multiGrowth : Proofs.CppPeakComponents.Grows state multiOut :=
   Proofs.CppCallPeak.call_peak multiProgram 16 state multiOut multiArgs (.scalar 74) i32 rfl rfl contexts (by decide +kernel)
 #guard multiOut.scalars.memory == state.scalars.memory
 #guard multiOut.frame.bindings == state.frame.bindings
 #guard multiOut.peak <= max state.peak (multiOut.scalars.peak+multiOut.frame.state.storage.peak)
 def historic : NState := {state with peak := 100000000}
 def historicOut : NState := match multiProgram.callFuel 16 historic multiArgs with
   | .finished (out,_) => out | _ => historic
 example := Proofs.CppCallPeak.call_peak multiProgram 16 historic historicOut multiArgs (.scalar 74) i32
   rfl rfl contexts (by decide +kernel)
 #guard historicOut.peak == 100000000
 #guard historicOut.scalars.peak == multiOut.scalars.peak
 example (fuel : Nat) (command : Command) (s : NState) (out : NStep)
   (allowed : Proofs.CppNoResizeScope.Allowed command = true)
   (ctx : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope)
   (ran : Proofs.CppNestedProgram.runFuel fuel command s = .finished out) :=
   Proofs.CppPeakRun.run_grows fuel command s out allowed ctx ran
'''
UF = '''
 theorem wholePeak : twiceOut.peak ≤ max built.peak (Proofs.UfUniformPeak.components built) :=
   Proofs.UfUniformPeak.actual_calls_peak (List.replicate twice.length 128) twice built (layoutOf populated)
     twiceOut twiceAnswers (List.replicate 4 (-1)) 4 (fun _ => 0) builtStrong twiceAllowed twiceActual
 #guard twiceOut.peak <= max built.peak (Proofs.UfUniformPeak.components built)
 #guard twiceOut.peak == onceOut.peak
 example := Proofs.UfUniformPeak.actual_calls (List.replicate twice.length 128) twice built (layoutOf populated)
   twiceOut twiceAnswers builtContexts twiceActual
 example := Proofs.UfUniformPeak.calls_peak twice built (layoutOf populated)
   (List.replicate 4 (-1)) 4 (fun _ => 0) builtStrong twiceAllowed
 example := Proofs.UfUniformPeak.calls_peak [] built (layoutOf populated)
   (List.replicate 4 (-1)) 4 (fun _ => 0) builtStrong (by simp)
 example (ops : List Operation) (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
   (strong : Proofs.UfBalancedReceiver.Strong s layout ps count rank)
   (allowed : ∀ op ∈ ops, op.allowed ps.length) := Proofs.UfUniformPeak.calls_peak ops s layout ps count rank strong allowed
'''

class OuterPeakTests(unittest.TestCase):
    def check(self, source):
        with tempfile.TemporaryDirectory(prefix='uf-outer-peak-') as directory:
            proof = Path(directory)/'checks.lean'
            proof.write_text(source)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)

    def test_control_and_multiple_vector_argument_call(self):
        self.check('import Proofs.CppCallPeak\nimport Proofs.Generated.UnionFindCandidate\n'
                   +'\n'.join(fixture_checks())+SCALAR_CHECKS+CONTROL+NESTED)

    def test_uf_uniform_whole_peak(self):
        self.check('import Proofs.UfUniformPeak\n'+HEADER+CALLER_HEADER+STAGE_CHECKS+RECEIVER_CHECKS
                   +TRACE_CHECKS+RANK_CHECKS+STORAGE_CHECKS+UF)

if __name__ == '__main__':
    disable_network()
    unittest.main()
