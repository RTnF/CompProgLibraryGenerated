"""Independently check matrix exponentiation with the pinned kernel's default stack."""
from pathlib import Path
import json
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / 'tools'), str(ROOT / 'tests')]
from check_proof_security import BUILTINS
from offline import disable_network
from test_scalar_ir import lean_environment


class MatrixPowerKernelTests(unittest.TestCase):
    def test_loop_and_final_specification(self):
        lake, env = lean_environment()
        env.pop('LEAN_PATH', None)
        permitted = ['propext', 'Classical.choice', 'Quot.sound']
        exporter = ROOT / '.tools/lean4export/.lake/build/bin/lean4export'
        nanoda = ROOT / '.tools/nanoda_lib/target/release/nanoda_bin'
        with tempfile.TemporaryDirectory(prefix='matrix-power-kernel-') as directory:
            scratch = Path(directory)
            export = scratch / 'export.ndjson'
            with export.open('w') as output:
                subprocess.run(
                    [lake, 'env', str(exporter), 'Proofs.MatPowExec', '--',
                     *BUILTINS, *permitted, 'Proofs.MatPowExec.pow_while',
                     'Proofs.MatPowExec.pow_final'],
                    cwd=ROOT, env=env, stdout=output, check=True, timeout=120)
            config = scratch / 'nanoda.json'
            config.write_text(json.dumps(dict(
                export_file_path=str(export), permitted_axioms=permitted,
                unpermitted_axiom_hard_error=True, unsafe_permit_all_axioms=False,
                nat_extension=True, string_extension=True, num_threads=2,
                print_success_message=True, print_axioms=False)))
            result = subprocess.run(
                [str(nanoda), str(config)], cwd=scratch, env=env,
                capture_output=True, text=True, timeout=120)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertRegex(result.stdout,
                             r'\AChecked [1-9][0-9]* declarations with no errors\s*\Z')
            print(result.stdout.strip(), flush=True)


if __name__ == '__main__':
    disable_network()
    unittest.main()
