"""Bitwise operators in the common generators: regeneration, renaming, mutations and rejected shapes."""
import json
from pathlib import Path
import re
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'verifier'))
sys.path.insert(0, str(ROOT / 'tools'))
import nested_ir
from offline import disable_network

SOURCE = ROOT / 'library/mod61.hpp'


class BitwiseTests(unittest.TestCase):
    def lower(self, text, scratch, name='case.hpp'):
        path = scratch / name
        path.write_text(text)
        return nested_ir.lower_source(path, [scratch])

    def test_generated_model_matches(self):
        ir = nested_ir.lower_source(SOURCE, [SOURCE.parent])
        text = nested_ir.emit_lean(ir, 'Proofs.Mod61Instance')
        for operator in ('.shr', '.band', '.shl'):
            self.assertIn(operator, text)
        self.assertEqual(text, (ROOT / 'Proofs/Generated/Mod61.lean').read_text())

    def test_renaming_and_source_changes(self):
        original = SOURCE.read_text()
        baseline = nested_ir.lower_source(SOURCE, [SOURCE.parent])
        with tempfile.TemporaryDirectory(prefix='bitwise-mutations-') as directory:
            scratch = Path(directory)
            renamed = original
            for old, new in [('mod61', 'reduce'), ('mul61', 'product'), ('xu', 'high'), ('xd', 'low')]:
                renamed = re.sub(rf'\b{old}\b', new, renamed)
            other = self.lower(renamed, scratch, 'renamed.hpp')
            expected = json.loads(json.dumps(baseline))
            expected['functions'][0]['name'] = 'reduce'
            expected['functions'][1]['name'] = 'product'
            self.assertEqual(other, expected)
            for old, new in [('x >> 61', 'x >> 60'), ('x & m', 'x | m'), ('midd << 31', 'midd << 30'),
                             ('a >> 31', 'a >> 30'), ('ad * bu + au * bd', 'ad * bu + au * bu')]:
                with self.subTest(change=new):
                    self.assertIn(old, original)
                    changed = self.lower(original.replace(old, new), scratch, 'changed.hpp')
                    self.assertNotEqual(changed, baseline)

    def test_unsupported_shapes_fail_closed(self):
        with tempfile.TemporaryDirectory(prefix='bitwise-unsupported-') as directory:
            scratch = Path(directory)
            prelude = '#include <vector>\nnamespace cp {\n'
            cases = {
                'signed operands': 'inline int f(int x) { return x & 7; }',
                'signed shift': 'inline int f(int x) { return x >> 1; }',
                'variable shift count': 'inline unsigned long long f(unsigned long long x, int k) { return x >> k; }',
                'shift count too large': 'inline unsigned long long f(unsigned long long x) { return x >> 64; }',
                'negative shift count': 'inline unsigned long long f(unsigned long long x) { return x << -1; }',
                'narrow unsigned operands': 'inline unsigned char f(unsigned char x) { return x & 1; }',
            }
            for name, body in cases.items():
                with self.subTest(name):
                    with self.assertRaises(Exception):
                        self.lower(prelude + body + '\n}\n', scratch)


if __name__ == '__main__':
    disable_network()
    unittest.main()
