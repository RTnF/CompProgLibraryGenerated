"""Inductive certificates compose dynamic reads through all scalar operators."""
from pathlib import Path
import subprocess
import tempfile
import unittest

from test_dynamic_expr import fixture_checks
from test_scalar_ir import lean_environment
from offline import disable_network

ROOT=Path(__file__).resolve().parent.parent


class DynamicCertifiedTests(unittest.TestCase):
    def test_inductive_soundness_with_live_row_temporaries(self):
        checks=fixture_checks()
        checks[0]='import Proofs.DynamicExprDerive\n'+checks[0]
        checks += ['open Proofs.DynamicExprCertified',
                   'theorem rootCert : Evaluation params (snapshot state) logical rootSize 4 :=',
                   '  Evaluation.atom _ _ (Proofs.DynamicExprAtoms.root_size params (snapshot state) logical 1 p1 (by decide +kernel) (by decide +kernel) i32 0 values (by decide +kernel) (by decide +kernel))',
                   'theorem rowSizeCert : Evaluation params (snapshot state) logical rowSize 2 :=',
                   '  Evaluation.atom _ _ (Proofs.DynamicExprAtoms.row_size params (snapshot state) logical 1 p1 (by decide +kernel) (by decide +kernel) i32 0 1 values [17,-3] idx (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))',
                   'theorem rowReadCert : Evaluation params (snapshot state) logical rowRead (-3) :=',
                   '  Evaluation.atom _ _ (Proofs.DynamicExprAtoms.row_read params (snapshot state) logical 1 p1 (by decide +kernel) (by decide +kernel) i32 0 1 1 values [17,-3] idx pos (-3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))',
                   'def flatRead : NExpr := .read i32 (.local 2) (.literal i32 0)',
                   'theorem flatReadCert : Evaluation params (snapshot state) logical flatRead 77 :=',
                   '  Evaluation.atom _ _ (Proofs.DynamicExprAtoms.flat_read params (snapshot state) logical 2 p2 (by decide +kernel) (by decide +kernel) i32 1 0 [77] (.literal i32 0) 77 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))',
                   'theorem flatSizeCert : Evaluation params (snapshot state) logical (.size atom (.local 2)) 1 :=',
                   '  Evaluation.atom _ _ (Proofs.DynamicExprAtoms.flat_size params (snapshot state) logical 2 p2 (by decide +kernel) (by decide +kernel) i32 1 [77] (by decide +kernel) (by decide +kernel))',
                   'theorem castRootCert : Evaluation params (snapshot state) logical (.cast i32 rootSize) 4 := Evaluation.cast _ _ _ _ rootCert (by decide +kernel)',
                   'theorem castRowCert : Evaluation params (snapshot state) logical (.cast i32 rowSize) 2 := Evaluation.cast _ _ _ _ rowSizeCert (by decide +kernel)',
                   'theorem combinedCert : Evaluation params (snapshot state) logical combined 1 := Evaluation.binary _ _ _ _ _ _ _ castRootCert rowReadCert (by decide +kernel)',
                   'def withLength : NExpr := .binary i32 .add combined (.cast i32 rowSize)',
                   'theorem lengthCert : Evaluation params (snapshot state) logical withLength 3 := Evaluation.binary _ _ _ _ _ _ _ combinedCert castRowCert (by decide +kernel)',
                   'def inspectE : NExpr := .binary i32 .add withLength flatRead',
                   'theorem inspectCert : Evaluation params (snapshot state) logical inspectE 80 := Evaluation.binary _ _ _ _ _ _ _ lengthCert flatReadCert (by decide +kernel)',
                   'theorem zeroCert : Evaluation params (snapshot state) logical (.literal i32 0) 0 := Evaluation.scalar _ _ (by decide +kernel) (by decide +kernel)',
                   'theorem oneCert : Evaluation params (snapshot state) logical (.literal i32 1) 1 := Evaluation.scalar _ _ (by decide +kernel) (by decide +kernel)',
                   'theorem twoCert : Evaluation params (snapshot state) logical (.literal i32 2) 2 := Evaluation.scalar _ _ (by decide +kernel) (by decide +kernel)',
                   'theorem negCert : Evaluation params (snapshot state) logical (.unary i32 .neg rowRead) 3 := Evaluation.unary _ _ _ _ _ rowReadCert (by decide +kernel)',
                   'theorem targetCert : Evaluation params (snapshot state) logical (.targetCast ⟨8,false,false⟩ rowRead) 253 := Evaluation.targetCast _ _ _ _ rowReadCert (by decide +kernel)',
                   'theorem quotientCert : Evaluation params (snapshot state) logical (.divrem i32 false (.unary i32 .neg rowRead) (.literal i32 2)) 1 := Evaluation.divrem _ _ _ _ _ _ _ negCert twoCert (by decide +kernel)',
                   'theorem remainderCert : Evaluation params (snapshot state) logical (.divrem i32 true rowRead (.literal i32 2)) (-1) := Evaluation.divrem _ _ _ _ _ _ _ rowReadCert twoCert (by decide +kernel)',
                   'theorem mulCert : Evaluation params (snapshot state) logical (.binary i32 .mul combined (.cast i32 rowSize)) 2 := Evaluation.binary _ _ _ _ _ _ _ combinedCert castRowCert (by decide +kernel)',
                   'theorem shortAndCert : Evaluation params (snapshot state) logical (.logical true (.literal i32 0) bad) 0 := Evaluation.logicalShort _ _ _ _ zeroCert (by decide +kernel)',
                   'theorem shortOrCert : Evaluation params (snapshot state) logical (.logical false (.literal i32 1) bad) 1 := Evaluation.logicalShort _ _ _ _ oneCert (by decide +kernel)',
                   'theorem nextAndCert : Evaluation params (snapshot state) logical (.logical true combined rowRead) 1 := Evaluation.logicalNext _ _ _ _ _ combinedCert rowReadCert (by decide +kernel)',
                   'theorem nextOrCert : Evaluation params (snapshot state) logical (.logical false (.literal i32 0) rowRead) 1 := Evaluation.logicalNext _ _ _ _ _ zeroCert rowReadCert (by decide +kernel)',
                   'theorem nextZeroCert : Evaluation params (snapshot state) logical (.logical true combined (.literal i32 0)) 0 := Evaluation.logicalNext _ _ _ _ _ combinedCert zeroCert (by decide +kernel)',
                   'example (s : NState) (r : Realizes params (snapshot state) logical s) : Proofs.DynamicExpr.denote params (snapshot state) logical inspectE = some 80 ∧ ∃ t, inspectE.eval s = some (t,80) ∧ Realizes params (snapshot state) logical ((t.release s).charge 1 0) ∧ ((t.release s).charge 1 0).work ≤ s.work+2*inspectE.nodes+1 ∧ ((t.release s).charge 1 0).peak ≤ max s.peak (max s.scalars.peak (Proofs.CppNestedEval.liveS s+2*inspectE.nodes)+s.frame.state.storage.peak) := released inspectCert s r']
        for name,e,value in [('inspectCert','inspectE',80),('targetCert','.targetCast ⟨8,false,false⟩ rowRead',253),
                             ('quotientCert','.divrem i32 false (.unary i32 .neg rowRead) (.literal i32 2)',1),
                             ('remainderCert','.divrem i32 true rowRead (.literal i32 2)',-1),
                             ('shortAndCert','.logical true (.literal i32 0) bad',0),
                             ('shortOrCert','.logical false (.literal i32 1) bad',1),
                             ('nextAndCert','.logical true combined rowRead',1),
                             ('nextOrCert','.logical false (.literal i32 0) rowRead',1),
                             ('nextZeroCert','.logical true combined (.literal i32 0)',0)]:
            checks += [f'example : Atomic params (snapshot state) logical ({e}) ({value}) := sound {name}',
                       f'#guard (({e} : NExpr).eval state).map Prod.snd == some ({value})']
        checks += ['open Proofs.DynamicExprDerive',
                   'theorem rootReady : Ready params (snapshot state) logical rootSize := known (by decide +kernel) (sound rootCert)',
                   'theorem sizeReady : Ready params (snapshot state) logical rowSize := known (by decide +kernel) (sound rowSizeCert)',
                   'theorem readReady : Ready params (snapshot state) logical rowRead := known (by decide +kernel) (sound rowReadCert)',
                   'theorem flatReady : Ready params (snapshot state) logical flatRead := known (by decide +kernel) (sound flatReadCert)',
                   'theorem combinedReady : Ready params (snapshot state) logical combined := Ready.binary _ _ _ _ (Ready.cast _ _ rootReady) readReady',
                   'theorem inspectReady : Ready params (snapshot state) logical inspectE := Ready.binary _ _ _ _ (Ready.binary _ _ _ _ combinedReady (Ready.cast _ _ sizeReady)) flatReady',
                   'theorem autoInspect : Evaluation params (snapshot state) logical inspectE 80 := derive inspectReady 80 (by decide +kernel)',
                   'theorem badReady : Ready params (snapshot state) logical bad := failed (by decide +kernel)',
                   'theorem autoShort : Evaluation params (snapshot state) logical (.logical true (.literal i32 0) bad) 0 := derive (Ready.logical _ _ _ (Ready.scalar _ (by decide +kernel)) badReady) 0 (by decide +kernel)',
                   'example (s : NState) (r : Realizes params (snapshot state) logical s) : Atomic params (snapshot state) logical inspectE 80 := sound autoInspect',
                   'example : ¬ Evaluation params (snapshot state) logical (.divrem i32 false rowRead (.literal i32 0)) 0 := by',
                   '  intro c',
                   '  have pure := (sound c state realizes).1',
                   '  have rejected : Proofs.DynamicExpr.denote params (snapshot state) logical (.divrem i32 false rowRead (.literal i32 0)) = none := by decide +kernel',
                   '  rw [rejected] at pure; contradiction']
        with tempfile.TemporaryDirectory(prefix='dynamic-certified-') as directory:
            proof=Path(directory)/'checks.lean';proof.write_text('\n'.join(checks))
            lake,env=lean_environment();result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)


if __name__ == '__main__':
    disable_network()
    unittest.main()
