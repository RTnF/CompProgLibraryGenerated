"""Root call scalar peak stays independent of an inflated outer history."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_union_find_original_api import HEADER
from test_union_find_fields_call import FIXTURE
from test_union_find_root_ready import CHECKS as ROOT_CHECKS
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
CHECKS = '''
open Proofs.UfRootScalarPeak
 example := root_scalar_peak (cslot := 1) rootCaller ownerOK ⟨0,true⟩ 1 (by decide +kernel) rfl
   parents ranks parentForest (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl rfl
   nExpr aExpr 3 rfl rfl rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
 def hotCaller : NState := {rootCaller with peak := 100000000}
 theorem hotOK : VOKWF hotCaller 0 0 0 0 rootBuffer :=
   ⟨ownerOK.valid,ownerOK.slot,ownerOK.binding,ownerOK.vtag,ownerOK.vfound,
     ownerOK.lengths,ownerOK.flag,ownerOK.strict,ownerOK.base⟩
 def hotArgs : List Proofs.CppNestedCall.NArgument := [.vectorReference 0,.scalarReference 1,.value nExpr,.value aExpr]
 def hotRun := Proofs.UnionFindCandidateInstance.UnionFind_root.callFuel 64 hotCaller hotArgs
 def hotOut : NState := match hotRun with | .finished (out,_) => out | _ => hotCaller
 theorem hotActual : Proofs.UnionFindCandidateInstance.UnionFind_root.callFuel 64 hotCaller hotArgs =
   .finished (hotOut,.scalar 0) := by decide +kernel
 theorem hotPeak : ∃ init, Proofs.CppNestedCall.prepare hotCaller
   Proofs.UnionFindCandidateInstance.UnionFind_root.parameters hotArgs = some init ∧
   hotOut.scalars.peak ≤ max init.scalars.peak
     ((Proofs.DoublingCall.callerP hotCaller).length+12-hotCaller.scalars.baseMemory+100) :=
   root_scalar_peak_actual (cslot := 1) hotCaller hotOK ⟨0,true⟩ 1 (by decide +kernel) rfl
     parents ranks parentForest (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl rfl
     nExpr aExpr 3 rfl rfl rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
     64 hotOut (.scalar 0) hotActual
 def hotPrepared : NState := (Proofs.CppNestedCall.prepare hotCaller
   Proofs.UnionFindCandidateInstance.UnionFind_root.parameters hotArgs).getD hotCaller
 theorem hotPrepare : Proofs.CppNestedCall.prepare hotCaller
   Proofs.UnionFindCandidateInstance.UnionFind_root.parameters hotArgs = some hotPrepared := by decide +kernel
 theorem hotSmall : hotOut.scalars.peak ≤ 1000 := by
   obtain ⟨init,prep,bound⟩ := hotPeak
   rw [hotPrepare] at prep
   have eq := Option.some.inj prep
   subst init
   exact Nat.le_trans bound (by decide +kernel)
 #guard hotOut.peak >= 100000000
 #guard hotOut.scalars.peak < 1000
 #guard hotOut.frame.state.storage.peak == middle.frame.state.storage.peak
 #guard hotOut.scalars.memory == middle.scalars.memory
 #guard hotOut.frame.state == middle.frame.state
 #guard hotOut.scalars.peak == middle.scalars.peak
 example (program : Proofs.CppNestedCall.NProgram) (first second : Nat) (caller : NState)
   (args : List Proofs.CppNestedCall.NArgument) (a b : NState × Ret)
   (one : program.callFuel first caller args = .finished a) (two : program.callFuel second caller args = .finished b) :=
   Proofs.CppCallUnique.call_unique program first second caller args a b one two
 example := Proofs.CppCallUnique.call_unique Proofs.UnionFindCandidateInstance.UnionFind_root 64 128 hotCaller hotArgs
   (hotOut,.scalar 0) (hotOut,.scalar 0) hotActual (by decide +kernel)
'''

class ScalarPeakTests(unittest.TestCase):
    def test_root_actual_call_independent_outer_history(self):
        header = HEADER.replace('ps.length+1,64,0','ps.length+1,Proofs.CppVectorBindings.sizeLimit intTy,0')
        with tempfile.TemporaryDirectory(prefix='uf-scalar-peak-') as directory:
            proof = Path(directory)/'checks.lean'
            proof.write_text('import Proofs.UfRootScalarPeak\nimport Proofs.UfRootReady\n'+header+FIXTURE+ROOT_CHECKS+CHECKS)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)

if __name__ == '__main__':
    disable_network()
    unittest.main()
