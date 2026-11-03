"""Regression tests for inventory discovery, not for the C++ algorithms."""

from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import copy
import hashlib
from unittest.mock import patch

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import inventory_imports as inventory


class InventoryTests(unittest.TestCase):
    def test_source_declarations_and_overloads(self):
        with tempfile.TemporaryDirectory() as directory:
            scratch = Path(directory)
            dependency = scratch / "dependency.hpp"
            dependency.write_text("struct Foreign {};\nint foreign(int x) { return x; }\n")
            source = scratch / "subject.hpp"
            source.write_text('''#include "dependency.hpp"
using Number = int;
constexpr int Limit = 4;
template<class T> class Box {
  T value;
  T helper() const { return value; }
public:
  Box(T x): value(x) {}
  T get() const { return helper(); }
};
int choose(int x) { int local = x; return local; }
long choose(long x) { return x; }
namespace detail { int helper(int x) { return x + 1; } }
''')
            completed = subprocess.run(
                inventory.clang_command() + ["-Xclang", "-ast-dump", str(source)],
                check=True, text=True, capture_output=True)
            declarations = inventory.declarations(completed.stdout.splitlines(), source)
            signatures = [d["declaration"] for d in declarations]
            self.assertTrue(any(s.startswith("Number ") for s in signatures))
            self.assertTrue(any("Limit '" in s for s in signatures))
            self.assertEqual(sum(s.startswith("choose '") for s in signatures), 2)
            self.assertTrue(any(s.startswith("helper '") for s in signatures))
            self.assertTrue(any(s.startswith("Box<T> '") for s in signatures))
            self.assertFalse(any("foreign" in s or "Foreign" in s for s in signatures))
            self.assertFalse(any(s.startswith("local '") for s in signatures))
            self.assertEqual([d["line"] for d in declarations if d["kind"] == "FunctionDecl"
                              and d["declaration"].startswith("choose '")], [11, 12])
            self.assertEqual([d["line"] for d in declarations if d["kind"] == "CXXRecordDecl"
                              and "class Box definition" in d["declaration"]], [4])

    def test_coverage_counts_include_manual_ignored_and_templates(self):
        paths = inventory.discover()
        self.assertEqual(len(paths), len(set(paths)))
        self.assertTrue(any("VerifyManually" in p.parts for p in paths))
        self.assertTrue(any("VerifyIgnored" in p.parts for p in paths))
        self.assertTrue(any(p.name == "marathon_template.cpp" for p in paths))
        self.assertTrue(any(p.name.endswith(".test_ac.cpp") for p in paths))

    def test_reviews_are_preserved_only_for_unchanged_source(self):
        declaration = {"kind": "FunctionDecl", "line": 1, "declaration": "f 'int ()'",
                       "status": inventory.pending_status(), "verification_target": None}
        row = {"source": "x.hpp", "source_sha256": "old", "status": inventory.pending_status(),
               "verification_target": None, "declarations": [declaration]}
        prior = {"files": [copy.deepcopy(row)]}
        prior["files"][0]["status"]["cpp_tested"] = True
        prior["files"][0]["declarations"][0]["status"]["cpp_tested"] = True
        current = {"files": [copy.deepcopy(row)]}
        inventory.preserve_reviews(current, prior)
        self.assertTrue(current["files"][0]["status"]["cpp_tested"])
        self.assertTrue(current["files"][0]["declarations"][0]["status"]["cpp_tested"])
        changed = {"files": [copy.deepcopy(row)]}
        changed["files"][0]["source_sha256"] = "new"
        inventory.preserve_reviews(changed, prior)
        self.assertFalse(changed["files"][0]["status"]["cpp_tested"])

    def test_duplicate_candidates_include_same_series_plain_classes(self):
        rows = [{"source": "a.hpp", "declarations": [{"kind": "CXXRecordDecl",
                 "declaration": "class UnionFind definition"}]},
                {"source": "b.hpp", "declarations": [{"kind": "CXXRecordDecl",
                 "declaration": "class UnionFind definition"}]},
                {"source": "c.hpp", "declarations": [{"kind": "CXXRecordDecl",
                 "declaration": "struct Graph definition"}]}]
        inventory.update_duplicate_candidates(rows)
        self.assertEqual(rows[0]["duplicate_candidates"], ["b.hpp"])
        self.assertEqual(rows[2]["duplicate_candidates"], [])

    def test_inventory_rejects_source_drift_and_missing_or_duplicate_files(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tree = root / "imports"
            tree.mkdir()
            source = tree / "source.hpp"
            source.write_text("int f() { return 0; }\n")
            row = {"source": "imports/source.hpp", "dependencies": [],
                   "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest()}
            with patch.object(inventory, "ROOT", root), patch.object(inventory, "TREES", (tree,)):
                inventory.validate_inventory({"files": [row]})
                with self.assertRaisesRegex(RuntimeError, "coverage mismatch"):
                    inventory.validate_inventory({"files": []})
                with self.assertRaisesRegex(RuntimeError, "coverage mismatch"):
                    inventory.validate_inventory({"files": [row, row]})
                invalid = {**row, "verification_target": "missing.hpp"}
                with self.assertRaisesRegex(RuntimeError, "missing inventory reference"):
                    inventory.validate_inventory({"files": [invalid]})
                source.write_text("int f() { return 1; }\n")
                with self.assertRaisesRegex(RuntimeError, "stale inventory"):
                    inventory.validate_inventory({"files": [row]})
                source.write_text("int f() { return 0; }\n")
                (tree / "new.hpp").write_text("struct New {};\n")
                with self.assertRaisesRegex(RuntimeError, "coverage mismatch"):
                    inventory.validate_inventory({"files": [row]})


if __name__ == "__main__":
    inventory.disable_network()
    unittest.main()
