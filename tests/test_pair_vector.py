"""A vector of std::pair<T, T> is modelled as two rows of T (first, second); its size is the length of row 0."""

from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "verifier"))
sys.path.insert(0, str(ROOT / "tools"))
import nested_ir
from offline import disable_network

DEFINITION = '''#include <utility>
#include <vector>
namespace cp {
inline long long first_sum(const std::vector<std::pair<long long, long long>> &v) {
  long long s = 0;
  for (int i = 0; i < (int)v.size(); i++) {
    s += v[i].first;
  }
  return s;
}
inline long long second_at(const std::vector<std::pair<long long, long long>> &v, int i) { return v[i].second; }
}
'''


class PairVectorTests(unittest.TestCase):
    def model(self, text):
        disable_network()
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "source.hpp"
            source.write_text(text)
            return nested_ir.emit_lean(nested_ir.lower_source(source, [Path(directory)]), "Proofs.PairTest")

    def test_reads_are_row_reads_and_size_is_the_first_row(self):
        model = self.model(DEFINITION)
        # The parameter is a two-row nested vector of signed 64 bit integers.
        self.assertIn("[.nested ⟨64, true, false⟩ false]", model)
        # first reads row 0 and second reads row 1.
        self.assertIn("(.read ⟨64, true, false⟩ (.row (.local 0) (.integer ⟨64, true, false⟩) (.literal ⟨64, false, false⟩ (0)))", model)
        self.assertIn("(.read ⟨64, true, false⟩ (.row (.local 0) (.integer ⟨64, true, false⟩) (.literal ⟨64, false, false⟩ (1)))", model)
        # size() counts the first row, not the two rows.
        self.assertIn("(.size (.integer ⟨64, true, false⟩) (.row (.local 0) (.integer ⟨64, true, false⟩) (.literal ⟨64, false, false⟩ (0))))", model)
        self.assertNotIn("(.size (.vector", model)

    def test_user_pair_namesake_is_rejected(self):
        text = '''#include <vector>
namespace cp {
template <class A, class B> struct pair { A first; B second; };
inline long long f(const std::vector<pair<long long, long long>> &v) { return v[0].first; }
}
'''
        with self.assertRaises(Exception):
            self.model(text)


if __name__ == "__main__":
    unittest.main()
