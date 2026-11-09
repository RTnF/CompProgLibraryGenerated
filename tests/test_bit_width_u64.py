"""Actual bit-width source generation, universal proof and mutation checks."""
import copy
import json
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'verifier'))
sys.path.insert(0, str(ROOT / 'tools'))
from state_ir import lower_source, emit_lean
from test_scalar_ir import lean_environment
from offline import disable_network

SOURCE = ROOT / 'library/number_theory/bit_width_u64.hpp'
FIXTURE = ROOT / 'experiments/verification/array/bit_width_u64_ir.json'


class BitWidthTests(unittest.TestCase):
    def compile(self, path, text):
        path.write_text(text)
        lake, env = lean_environment()
        return subprocess.run([lake, 'env', 'lean', str(path)], cwd=ROOT,
                              env=env, capture_output=True, text=True)

    def test_regeneration_and_independent_results(self):
        ir = lower_source(SOURCE)
        self.assertEqual(ir, json.loads(FIXTURE.read_text()))
        generated = emit_lean(ir, 'Proofs.BitWidthU64Instance')
        self.assertEqual(generated, (ROOT / 'Proofs/Generated/BitWidthU64.lean').read_text())
        rng = random.Random(1729)
        values = set(range(257))
        values.update(rng.getrandbits(64) for _ in range(100))
        for bit in range(64):
            values.update([(1 << bit)-1, 1 << bit, (1 << bit)+1])
        checks = ['import Proofs.BitWidthU64\nopen Proofs.CppScalar Proofs.CppState Proofs.CppLoop\n']
        # Evaluate actual generated calls; Python bit_length is an independent oracle.
        for n in sorted(values):
            w = n.bit_length()
            checks.append(f'#guard Proofs.BitWidthU64Instance.bit_width_u64.callFuel 80 '
                f'[⟨⟨32,true,false⟩,17⟩] [.value {n}] == '
                f'Outcome.finished ⟨{w},[⟨⟨32,true,false⟩,17⟩],{9+14*w},8⟩\n')
        checks.append('#guard Proofs.BitWidthU64Instance.bit_width_u64.callFuel 0 [] [.value 1] == '
                      'Outcome.exhausted\n')
        for arguments in ['[]', '[.value (-1)]', '[.value 18446744073709551616]',
                          '[.value 1,.value 2]', '[.reference 0]']:
            checks.append(f'#guard Proofs.BitWidthU64Instance.bit_width_u64.callFuel 80 [] {arguments} == '
                          'Outcome.fault\n')
        with tempfile.TemporaryDirectory(prefix='bit-width-') as directory:
            result = self.compile(Path(directory)/'results.lean', ''.join(checks))
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
            renamed = Path(directory)/'renamed.hpp'
            renamed.write_text(SOURCE.read_text().replace('bit_width_u64', 'other_name')
                               .replace('value', 'argument').replace('result', 'count'))
            other = lower_source(renamed)
            expected = copy.deepcopy(ir)
            expected['functions'][0]['name'] = 'other_name'
            self.assertEqual(other, expected)

    def test_source_changes_reject_existing_whole_body_proofs(self):
        proofs = (ROOT/'Proofs/BitWidthU64.lean').read_text().replace(
            'import Proofs.Generated.BitWidthU64\n', '')
        mutations = [('value /= 2;', 'value /= 3;'), ('++result;', 'result += 2;'),
                     ('value != 0', 'value > 1'), ('return result;', 'return result + 1;')]
        with tempfile.TemporaryDirectory(prefix='bit-width-mutations-') as directory:
            scratch = Path(directory)
            baseline = self.compile(scratch/'baseline.lean',
                emit_lean(lower_source(SOURCE), 'Proofs.BitWidthU64Instance')+'\n'+proofs)
            self.assertEqual(baseline.returncode, 0, baseline.stdout+baseline.stderr)
            for old, new in mutations:
                with self.subTest(change=new):
                    source = scratch/'changed.hpp'
                    self.assertIn(old, SOURCE.read_text())
                    source.write_text(SOURCE.read_text().replace(old, new))
                    result = self.compile(scratch/'changed.lean',
                        emit_lean(lower_source(source), 'Proofs.BitWidthU64Instance')+'\n'+proofs)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn('error:', result.stdout+result.stderr)


if __name__ == '__main__':
    disable_network()
    unittest.main()
