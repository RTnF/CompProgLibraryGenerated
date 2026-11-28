"""Regression tests for read-only strings and constant C arrays."""
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "verifier"))
import lean_translate as translator


class ReadOnlyCollectionsTest(unittest.TestCase):
    def translate(self, body: str) -> str:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "fixture.hpp"
            path.write_text('#include <string>\nnamespace cp { ' + body + ' }\n')
            declarations = translator.source_decls(path, "c++23")
            return translator.Translator(declarations, path.read_bytes(), []).translate()

    def test_reads_size_and_element(self):
        lean = self.translate("int char_at(const std::string &s, int i) { return s[i]; } "
                              "std::size_t length(const std::string &s) { return s.size(); }")
        self.assertIn("Cpp.get s i", lean)
        self.assertIn("UInt64.ofInt (Cpp.size s)", lean)

    def test_rejects_resize(self):
        with self.assertRaisesRegex(translator.Unsupported, "string::resize"):
            self.translate("void resize(std::string &s) { s.resize(2); }")

    def test_rejects_subscript_write(self):
        with self.assertRaises(translator.Unsupported):
            self.translate("void set_char(std::string &s) { s[0] = 'x'; }")

    def test_rejects_substring(self):
        with self.assertRaisesRegex(translator.Unsupported, "string::substr"):
            self.translate("std::string rest(const std::string &s) { return s.substr(1); }")


    def test_namespaced_constants_and_alias(self):
        model = self.translate(
            "struct Record { int value; }; "
            "namespace child { constexpr int bits[] = {2, 3, 5}; using Alias = cp::Record; "
            "int element(int i) { return bits[i]; } } "
            "int lookup(int i) { return child::element(i); }")
        self.assertIn("def cp.child.bits : (Array Int) := ([2, 3, 5] : List Int).toArray", model)
        self.assertIn("abbrev cp.child.Alias", model)
        self.assertIn("Cpp.get cp.child.bits", model)
        self.assertIn("cp.child.element", model)

    def test_rejects_implicit_zero_fill(self):
        with self.assertRaisesRegex(translator.Unsupported, "constant array requires a full literal initializer"):
            self.translate("constexpr int numbers[3] = {2};")

    def test_rejects_non_literal_array_initializer(self):
        with self.assertRaisesRegex(translator.Unsupported, "initializer is not a direct scalar literal"):
            self.translate("constexpr int numbers[2] = {2, 1+2};")

    def test_rejects_mutable_child_state(self):
        with self.assertRaisesRegex(translator.Unsupported, "child namespaces require"):
            self.translate("namespace child { int counter; }")


if __name__ == "__main__":
    unittest.main()
