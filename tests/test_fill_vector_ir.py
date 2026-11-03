"""Fill-constructed flat vectors in the common nested generator: renaming, mutations and rejected shapes."""
import json
from pathlib import Path
import re
import shutil
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'verifier'))
sys.path.insert(0, str(ROOT / 'tools'))
import nested_ir
from offline import disable_network

LIBRARY = ROOT / 'library/sort_util.hpp'


def inv_perm_source():
    """The self-contained text of `inv_perm` (with its explicit instance) taken from the sort utilities."""
    text = LIBRARY.read_text()
    start = text.index('template <class T> std::vector<int> inv_perm')
    end = text.index('inv_perm<int>(const std::vector<int> &);') + len('inv_perm<int>(const std::vector<int> &);')
    return '#pragma once\n#include <cassert>\n#include <vector>\n\nnamespace cp {\n\n' + text[start:end] + '\n\n} // namespace cp\n'


class FillVectorTests(unittest.TestCase):
    def test_generated_model_uses_fill_vector_and_write(self):
        ir = nested_ir.lower_source(LIBRARY, [LIBRARY.parent])
        text = nested_ir.emit_lean(ir, 'Proofs.SortUtilInstance')
        self.assertIn('.fillVector', text)
        self.assertIn('.write (.local 2)', text)
        self.assertEqual(text, (ROOT / 'Proofs/Generated/SortUtil.lean').read_text())

    def test_renaming_and_source_changes(self):
        original = inv_perm_source()
        with tempfile.TemporaryDirectory(prefix='fill-vector-mutations-') as directory:
            scratch = Path(directory)
            (scratch / 'original.hpp').write_text(original)
            baseline = nested_ir.lower_source(scratch / 'original.hpp', [scratch])
            renamed = original
            for old, new in [('inv_perm', 'other_name'), ('inv', 'result'), ('v', 'perm'), ('n', 'size')]:
                renamed = re.sub(rf'\b{old}\b', new, renamed)
            (scratch / 'renamed.hpp').write_text(renamed)
            other = nested_ir.lower_source(scratch / 'renamed.hpp', [scratch])
            expected = json.loads(json.dumps(baseline))
            expected['functions'][0]['name'] = 'other_name_std_vector_int'
            self.assertEqual(other, expected)
            for old, new in [('inv(n, -1)', 'inv(n, 0)'), ('inv(n, -1)', 'inv(n + 1, -1)'),
                             ('inv[v[i]] = i;', 'inv[v[i]] = i + 1;'), ('assert(inv[v[i]] == -1);', ''),
                             ('i < n', 'i <= n')]:
                with self.subTest(change=new):
                    self.assertIn(old, original)
                    (scratch / 'changed.hpp').write_text(original.replace(old, new))
                    ir = nested_ir.lower_source(scratch / 'changed.hpp', [scratch])
                    self.assertNotEqual(ir, baseline)

    def test_unsupported_fill_shapes_fail_closed(self):
        with tempfile.TemporaryDirectory(prefix='fill-vector-unsupported-') as directory:
            scratch = Path(directory)
            prelude = '#include <vector>\nnamespace cp {\n'
            cases = {
                'nested fill': 'std::vector<std::vector<int>> f(int n) { std::vector<std::vector<int>> a(n, std::vector<int>()); return a; }',
                'fill from range': 'std::vector<int> f(const std::vector<int> &v) { std::vector<int> a(v.begin(), v.end()); return a; }',
            }
            for name, body in cases.items():
                with self.subTest(name):
                    path = scratch / 'case.hpp'
                    path.write_text(prelude + body + '\n}\n')
                    with self.assertRaises(Exception):
                        nested_ir.lower_source(path, [scratch])


if __name__ == '__main__':
    disable_network()
    unittest.main()
