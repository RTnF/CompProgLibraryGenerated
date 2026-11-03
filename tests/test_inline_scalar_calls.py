"""`[[gnu::always_inline]]` scalar helpers are inlined into their callers by the common generator."""
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'verifier'))
sys.path.insert(0, str(ROOT / 'tools'))
import nested_ir
from offline import disable_network

PRELUDE = '#include <vector>\nnamespace cp {\n'
HELPER = ('{attr} inline unsigned long long twice_mod(unsigned long long a, unsigned long long m) {{\n'
          '  unsigned long long r = a + a;\n  if (a >= m - a) {{\n    r = a - (m - a);\n  }}\n  return r;\n}}\n')
USER = ('inline unsigned long long f(unsigned long long x, unsigned long long m) {\n'
        '  unsigned long long y = twice_mod(x, m);\n  return y;\n}\n')


class InlineScalarCallTests(unittest.TestCase):
    def lower(self, text, scratch):
        path = scratch / 'case.hpp'
        path.write_text(text)
        return nested_ir.lower_source(path, [scratch])

    def test_always_inline_removes_the_call(self):
        with tempfile.TemporaryDirectory(prefix='inline-scalar-') as directory:
            scratch = Path(directory)
            ir = self.lower(PRELUDE + HELPER.format(attr='[[gnu::always_inline]]') + USER + '}\n', scratch)
            text = nested_ir.emit_lean(ir, 'Proofs.CaseInstance')
            self.assertNotIn('invokeScalar', text)
            self.assertEqual(ir['callees'], [])
            plain = nested_ir.emit_lean(self.lower(PRELUDE + HELPER.format(attr='') + USER + '}\n', scratch),
                                        'Proofs.CaseInstance')
            self.assertIn('invokeScalar', plain)

    def test_early_return_is_rejected(self):
        helper = ('[[gnu::always_inline]] inline unsigned long long g(unsigned long long a) {\n'
                  '  if (a == 0) {\n    return 1;\n  }\n  return a;\n}\n')
        user = ('inline unsigned long long f(unsigned long long x) {\n'
                '  unsigned long long y = g(x);\n  return y;\n}\n')
        with tempfile.TemporaryDirectory(prefix='inline-scalar-') as directory:
            with self.assertRaises(Exception):
                self.lower(PRELUDE + helper + user + '}\n', Path(directory))


if __name__ == '__main__':
    disable_network()
    unittest.main()
