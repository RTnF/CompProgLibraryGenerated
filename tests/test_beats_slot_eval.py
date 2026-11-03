"""Stateful slot permutation: arrays, new row bindings, faults and short circuiting."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT/'tools'), str(ROOT/'tests')]
from offline import disable_network
from test_scalar_ir import lean_environment


class BeatsSlotEvalTests(unittest.TestCase):
    def check_fixtures(self, module, names):
        with tempfile.TemporaryDirectory(prefix='beats-slot-eval-') as directory:
            proof = Path(directory)/'check.lean'
            proof.write_text(f'import Proofs.{module}\n' + '\n'.join(
                (ROOT/'tests/lean'/name).read_text() for name in names))
            lake, env = lean_environment()
            result = subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,
                                    capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            self.assertNotIn('warning:',result.stdout+result.stderr)

    def test_stateful_expression_permutation(self):
        self.check_fixtures('BeatsSlotEval',['beats_slot_eval.lean'])

    def test_declare_assign_write_and_scope(self):
        self.check_fixtures('BeatsSlotStmt',['beats_slot_eval.lean','beats_slot_stmt.lean'])

    def test_run_fuel_control_and_outcomes(self):
        self.check_fixtures('BeatsSlotRun',['beats_slot_eval.lean','beats_slot_run.lean'])

    def test_binding_permutation_and_saved_references(self):
        self.check_fixtures('BeatsBindingCycle',['beats_slot_eval.lean','beats_binding_cycle.lean'])

    def test_current_scope_vector_ownership(self):
        self.check_fixtures('MultiVecOwnedSound',['beats_owned_scope.lean'])

    def test_binding_view_expression_evaluation(self):
        self.check_fixtures('BeatsBindingExpr',['beats_slot_eval.lean','beats_binding_expr.lean'])

    def test_binding_view_statements_and_scope(self):
        self.check_fixtures('BeatsBindingStmt',[
            'beats_slot_eval.lean','beats_binding_expr.lean','beats_binding_stmt.lean'])

    def test_binding_view_control_and_outcomes(self):
        self.check_fixtures('BeatsBindingRun',[
            'beats_slot_eval.lean','beats_slot_run.lean','beats_binding_run.lean'])


if __name__=='__main__':
    disable_network()
    unittest.main()
