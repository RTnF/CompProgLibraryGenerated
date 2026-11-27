"""Check the original treap repairs and compare its parent rows with the public header."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "verifier"))
from lean_translate import Unsupported, translate_file


class OriginalTreeMultiSetTests(unittest.TestCase):
    def test_deque_owner_is_used_only_through_checked_operations(self):
        source = (ROOT / "library/set/tree_multiset.hpp").read_text()
        changes = [
            ("(slots.get() == nullptr ? 0 : (*slots).size()) - 1", "(*slots).size() - 1"),
            ("if (slots.get() == nullptr) slots = std::make_unique<std::deque<Slot>>();", ""),
            ("other.slots.get() == nullptr ? 0 : (*other.slots).size()",
             "slots.get() == nullptr ? 0 : (*other.slots).size()"),
        ]
        with tempfile.TemporaryDirectory(prefix="tree-multiset-owner-") as directory:
            fixture = Path(directory) / "tree_multiset.hpp"
            for old, new in changes:
                with self.subTest(expression=old):
                    self.assertIn(old, source)
                    fixture.write_text(source.replace(old, new, 1))
                    with self.assertRaisesRegex(Unsupported, "unsupported use of a private deque owner"):
                        translate_file(fixture, [])

    def test_repairs_and_public_equivalence(self):
        with tempfile.TemporaryDirectory(prefix="tree-multiset-original-") as directory:
            binary = Path(directory) / "tree_multiset"
            subprocess.run([
                "g++", "-std=c++17", "-O1", "-g", "-Wall", "-Wextra", "-pedantic",
                "-fsanitize=address,undefined", "-fno-sanitize-recover=all",
                "-fno-omit-frame-pointer", "-no-pie", "-DTEST_ORIGINAL_TREE_MULTISET",
                "-I", str(ROOT / "experiments/library/cpp"),
                str(ROOT / "tests/tree_multiset.cpp"), "-o", str(binary),
            ], check=True, timeout=60)
            environment = dict(os.environ, ASAN_OPTIONS="detect_leaks=0:halt_on_error=1",
                               UBSAN_OPTIONS="halt_on_error=1")
            subprocess.run([str(binary)], check=True, env=environment, timeout=30)


if __name__ == "__main__":
    unittest.main()
