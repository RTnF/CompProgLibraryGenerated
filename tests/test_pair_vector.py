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

    def test_original_interval_union_shape(self):
        text = '''#include <algorithm>
#include <utility>
#include <vector>
namespace cp {
template <class T>
std::vector<std::pair<T, T>> interval_union_inclusive(std::vector<std::pair<T, T>> &v) {
  std::sort(v.begin(), v.end());
  std::vector<std::pair<T, T>> ret;
  for (auto &&[l, r] : v) {
    if (ret.empty() || ret.back().second < l) {
      ret.emplace_back(l, r);
    } else if (ret.back().second < r) {
      ret.back().second = r;
    }
  }
  return ret;
}
template std::vector<std::pair<long long, long long>> interval_union_inclusive<long long>(std::vector<std::pair<long long, long long>> &);
}
'''
        model = self.model(text)
        row0 = "(.row (.local 0) (.integer ⟨64, true, false⟩) (.literal ⟨64, false, false⟩ (0)))"
        ret_row = lambda which: f"(.row (.local 1) (.integer ⟨64, true, false⟩) (.literal ⟨64, false, false⟩ ({which})))"
        self.assertIn("[.nested ⟨64, true, false⟩ true],.vector (.vector (.integer ⟨64, true, false⟩))", model)
        self.assertIn("(.sortPairs " + row0 + " (.row (.local 0) (.integer ⟨64, true, false⟩) (.literal ⟨64, false, false⟩ (1))) ⟨64, true, false⟩)", model)
        self.assertIn("(.constructRows ⟨64, true, false⟩ true (.literal ⟨64, false, false⟩ (2)))", model)
        # the loop runs over the length of row 0 of v; l and r are read-only copies of rows 0 and 1 at the loop index
        self.assertIn(f"(.size (.integer ⟨64, true, false⟩) {row0})", model)
        self.assertIn("(.declare ⟨64, true, false⟩ false (.read ⟨64, true, false⟩ " + row0, model)
        # emplace_back(l, r) appends to both rows of ret; back().second = r writes the last element of row 1
        self.assertIn(f"(.append {ret_row(0)} ⟨64, true, false⟩ (.variable ⟨64, true, false⟩ 3))", model)
        self.assertIn(f"(.append {ret_row(1)} ⟨64, true, false⟩ (.variable ⟨64, true, false⟩ 4))", model)
        self.assertIn(f"(.write {ret_row(1)} ⟨64, true, false⟩", model)
        self.assertIn("(.retVector 1)", model)

    def test_range_for_body_must_not_use_the_vector(self):
        text = '''#include <utility>
#include <vector>
namespace cp {
inline long long f(std::vector<std::pair<long long, long long>> &v) {
  long long s = 0;
  for (auto &&[a, b] : v) {
    s += v[0].first + a + b;
  }
  return s;
}
}
'''
        with self.assertRaises(ValueError):
            self.model(text)

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
