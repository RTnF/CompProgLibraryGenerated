"""Regression tests for dependent nested-record scopes."""
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "verifier"))
import lean_translate as tr


class NestedScopeTests(unittest.TestCase):
    def test_groups_same_record_names_by_family(self):
        data = self.translate("""
           template<class T> struct First {
             struct Value { T x; Value(T a) : x(a) {} };
           };
           template<class T> struct Second {
             struct Value { T x; Value(T a) : x(a) {} };
             struct Read { T stored; T get(Value v) const { return v.x; } };
           };""")
        self.assertIn("structure cp.First_Value", data)
        self.assertIn("structure cp.Second_Value", data)
        self.assertIn("(v : (cp.Second_Value T))", data)

    def test_rejects_record_model_name_collision(self):
        with self.assertRaisesRegex(tr.Unsupported, "conflicts with a class"):
            self.translate("""
                template<class T> struct Outer { struct Inner {}; };
                template<class T> struct Outer_Inner {};""")

    def test_rejects_type_shadowing(self):
        with self.assertRaisesRegex(tr.Unsupported, "shadowing a nested record type"):
            self.translate("""
                template<class T> struct Family {
                  struct Value {};
                  struct Reader {
                    int get() const { using Value = int; Value v = 3; return v; }
                  };
                };""")

    def test_rejects_enclosing_data_and_private_members(self):
        for text in (
            "template<class T> struct Outer { T storage; struct Inner {}; };",
            "template<class T> class Outer { struct Inner {}; };",
            "template<class T> struct Outer { private: struct Inner {}; };",
        ):
            with self.subTest(text=text), self.assertRaisesRegex(tr.Unsupported, "type-only template family"):
                self.translate(text)

    def translate(self, body):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "family.hpp"
            path.write_text("namespace cp {" + body + "}")
            declarations = tr.source_decls(path, "c++23")
            return tr.Translator(declarations, path.read_bytes(), []).translate()


if __name__ == "__main__":
    unittest.main()
