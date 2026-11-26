"""Check STL queue and value-tuple translation against C++."""

from pathlib import Path
import random
import subprocess
import sys
import tempfile
import unittest
from uuid import uuid4


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "verifier"))
import lean_translate as translator
from diff_harness import lean_environment, run_diff


INCLUDES = "#pragma once\n#include <list>\n#include <queue>\n#include <tuple>\n#include <utility>\n#include <vector>\n"
FIFO = """
std::vector<int> fifo(const std::vector<int> &values) {
  std::queue<int> pending;
  std::vector<int> out;
  for (auto value : values) {
    pending.emplace(value);
    pending.push(-value);
    if (pending.size() > 2) {
      out.emplace_back(pending.front());
      pending.pop();
    }
  }
  while (!pending.empty()) {
    out.emplace_back(pending.front());
    pending.pop();
  }
  return out;
}
"""

TUPLE = """
std::tuple<std::vector<int>, int, bool> pack(const std::vector<int> &values) {
  return {values, 5, !values.empty()};
}

std::vector<int> unpack(const std::vector<int> &values) {
  auto [copy, delta, present] = pack(values);
  auto [upper, lower] = std::pair<int, int>{13, -7};
  if (present) {
    copy.emplace_back(delta + upper);
  }
  copy.emplace_back(lower);
  return copy;
}
"""


class StlValueModelTests(unittest.TestCase):
    def write_fixture(self, path, body):
        path.write_text(INCLUDES + "namespace cp {\n" + body + "\n}\n")

    def check_differential(self, body, function, support=None):
        lake, env = lean_environment()
        module = f"StlValueModelProbe_{uuid4().hex}"
        olean = ROOT / ".lake/build/lib/lean" / f"{module}.olean"
        with tempfile.TemporaryDirectory(prefix="stl-value-model-") as directory:
            source = Path(directory) / "stl_fixture.hpp"
            self.write_fixture(source, body)
            lean = Path(directory) / f"{module}.lean"
            model = translator.translate_file(source, [])
            lean.write_text(model)
            if support is not None:
                self.assertIn(f"import {support}", model)
            subprocess.run([lake, "build", support or "Proofs.Cpp.Prelude"],
                           env=env, cwd=ROOT, check=True, timeout=90)
            try:
                subprocess.run([lake, "env", "lean", "-R", directory, "-o", str(olean), str(lean)],
                               env=env, cwd=ROOT, check=True, timeout=60)
                rng = random.Random(20261126)
                cases = []
                for length in range(48):
                    values = [rng.randrange(-2000, 2001) for _ in range(length)]
                    cases.append(" ".join(map(str, ["call", function, length, *values])))
                self.assertEqual(run_diff(source, {}, module, "\n".join(cases) + "\n", 60, calls=[function]), len(cases))
            finally:
                olean.unlink(missing_ok=True)

    def test_fifo_matches_cpp(self):
        self.check_differential(FIFO, "fifo", "Proofs.Cpp.Lib.Queue")

    def test_value_tuple_matches_cpp(self):
        self.check_differential(TUPLE, "unpack")

    def test_rejects_back_read(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "queue_fixture.hpp"
            self.write_fixture(source, "int back() { std::queue<int> q; q.push(1); return q.back(); }")
            with self.assertRaisesRegex(translator.Unsupported, "queue::back"):
                translator.translate_file(source, [])

    def test_rejects_write_through_front(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "queue_fixture.hpp"
            self.write_fixture(source, "int set_front() { std::queue<int> q; q.push(1); q.front() = 2; return q.front(); }")
            with self.assertRaises(translator.Unsupported):
                translator.translate_file(source, [])

    def test_rejects_alternate_container(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "queue_fixture.hpp"
            self.write_fixture(source, "int first() { std::queue<int, std::list<int>> q; q.push(1); return q.front(); }")
            with self.assertRaisesRegex(translator.Unsupported, "type.*queue"):
                translator.translate_file(source, [])

    def test_rejects_reference_tuple_element(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "tuple_fixture.hpp"
            self.write_fixture(source, "std::tuple<int &, int> tied(int &value) { return {value, 1}; }")
            with self.assertRaisesRegex(translator.Unsupported, "tuple requires at least two value elements"):
                translator.translate_file(source, [])

    def test_rejects_reference_structured_binding(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "tuple_fixture.hpp"
            self.write_fixture(source, "int first() { std::pair<int,int> p{1,2}; auto &[a,b] = p; return a; }")
            with self.assertRaisesRegex(translator.Unsupported, "reference or static structured binding"):
                translator.translate_file(source, [])

    def test_rejects_reference_element_in_pair_binding(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "tuple_fixture.hpp"
            self.write_fixture(source, """
int change(int value) { auto [a, b] = std::pair<int &, int>{value, 2}; a = b; return value; }
""")
            with self.assertRaisesRegex(translator.Unsupported, "reference or static structured binding"):
                translator.translate_file(source, [])

    def test_rejects_calls_inside_tuple_constructor_arguments(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "tuple_fixture.hpp"
            self.write_fixture(source, """
int increment(int value) { return value + 1; }
std::tuple<int, int> make(int x) { return {increment(x), x}; }
""")
            with self.assertRaisesRegex(translator.Unsupported, "effects in tuple constructor arguments"):
                translator.translate_file(source, [])


if __name__ == "__main__":
    unittest.main()
