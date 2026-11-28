"""Check the original TreeSet regressions and the ordered-set translation boundary."""

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "verifier"))
import lean_translate as translator


class OrderedSetTests(unittest.TestCase):
    def test_original_tree_set(self):
        with tempfile.TemporaryDirectory(prefix="tree-set-original-") as directory:
            binary = Path(directory) / "tree_set_source"
            subprocess.run([
                "g++", "-std=c++23", "-O1", "-g", "-Wall", "-Wextra", "-pedantic",
                "-fsanitize=address,undefined", "-fno-sanitize-recover=all",
                "-fno-omit-frame-pointer", "-no-pie", "-I", str(ROOT / "experiments/library/cpp"),
                str(ROOT / "tests/imports/tree_set_source.cpp"), "-o", str(binary),
            ], check=True, timeout=60)
            environment = dict(os.environ, ASAN_OPTIONS="detect_leaks=0:halt_on_error=1",
                               UBSAN_OPTIONS="halt_on_error=1")
            subprocess.run([str(binary)], check=True, env=environment, timeout=30)

    def test_rejects_unmodeled_wrapper_behavior(self):
        header = (ROOT / "tests/fixtures/ordered_set_wrapper.hpp").read_text()
        changes = [
            ("a.key < b.key", "b.key < a.key", "nested records"),
            ("mutable T key", "T key", "nested records"),
            ("explicit Entry(T &value) : key(value) {}", "explicit Entry(T &value) : key(value) { key = value; }",
             "nested records"),
            ("values.erase(Entry(key))", "values.erase(values.begin())", "lookup requires"),
            ("values.emplace(key);", "auto copy = values;", "escapes"),
            ("values.emplace(key);", "values.clear();", "escapes"),
            ("values.emplace(key);", "values.begin()->key = key;", "lvalue UnaryOperator"),
        ]
        with tempfile.TemporaryDirectory(prefix="ordered-set-model-") as directory:
            source = Path(directory) / "tree_set.hpp"
            for before, after, diagnostic in changes:
                with self.subTest(change=after):
                    self.assertEqual(header.count(before), 1)
                    source.write_text(header.replace(before, after))
                    with self.assertRaisesRegex(translator.Unsupported, diagnostic):
                        translator.translate_file(source, [])

    def test_rejects_alternate_comparator(self):
        with tempfile.TemporaryDirectory(prefix="ordered-set-comparator-") as directory:
            source = Path(directory) / "tree_set.hpp"
            source.write_text("""#include <set>
namespace cp {
void insert() { std::set<int, std::greater<int>> values; values.insert(1); }
}
""")
            with self.assertRaisesRegex(translator.Unsupported, "default comparator and allocator"):
                translator.translate_file(source, [])


if __name__ == "__main__":
    unittest.main()
