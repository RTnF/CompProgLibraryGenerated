"""Exercise constructor states with distinct node and DFS stack capacities."""
from pathlib import Path
import json
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / 'tools'), str(ROOT / 'tests')]
from test_scalar_ir import lean_environment
from offline import disable_network
from check_proof_security import BUILTINS


class BeatsCapacityTests(unittest.TestCase):
    def test_constructor_independent_kernel(self):
        # The constructor's inline arithmetic certificate formerly exhausted
        # nanoda's default 16 MiB worker stack after hours of checking.
        lake, env = lean_environment()
        env.pop('LEAN_PATH', None)
        exporter = ROOT / '.tools/lean4export/.lake/build/bin/lean4export'
        nanoda = ROOT / '.tools/nanoda_lib/target/release/nanoda_bin'
        permitted = [entry['name'] for entry in json.loads(
            (ROOT / 'verification/allowed_axioms.json').read_text())['axioms']]
        with tempfile.TemporaryDirectory(prefix='beats-constructor-kernel-') as directory:
            scratch = Path(directory)
            export = scratch / 'export.ndjson'
            with export.open('w') as output:
                subprocess.run([lake, 'env', str(exporter), 'Proofs.BeatsWideCall',
                                '--', *BUILTINS, *permitted,
                                'Proofs.BeatsRep.segment_tree_beats_new0',
                                'Proofs.BeatsSeparate.segment_tree_beats_new0',
                                'Proofs.BeatsWideCall.call'],
                               cwd=ROOT, env=env, stdout=output, check=True, timeout=120)
            config = scratch / 'nanoda.json'
            config.write_text(json.dumps(dict(
                export_file_path=str(export), permitted_axioms=permitted,
                unpermitted_axiom_hard_error=True, unsafe_permit_all_axioms=False,
                nat_extension=True, string_extension=True, num_threads=2,
                print_success_message=True, print_axioms=False)))
            result = subprocess.run([str(nanoda), str(config)], cwd=scratch, env=env,
                                    capture_output=True, text=True, timeout=120)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertRegex(result.stdout,
                             r'\AChecked [1-9][0-9]* declarations with no errors\s*\Z')

    def test_actual_constructor_capacities(self):
        with tempfile.TemporaryDirectory(prefix='beats-capacities-') as directory:
            proof = Path(directory) / 'check.lean'
            proof.write_text('import Proofs.SegmentTreeBeatsCall\nimport Proofs.BeatsSlotCycle\nimport Proofs.BeatsIndexHeight\n' +
                             (ROOT / 'tests/lean/beats_capacities.lean').read_text())
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                                    env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)


if __name__ == '__main__':
    disable_network()
    unittest.main()
