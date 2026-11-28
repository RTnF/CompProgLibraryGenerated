"""Keep non-const C++ overload resolution for recursive methods with read-only receivers."""
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "verifier"))
import lean_translate as translator


class RecursiveReceiverTest(unittest.TestCase):
    def translate(self, write: str = "", helper: str = "") -> str:
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "fixture.hpp"
            source.write_text(f"""#include <vector>
namespace cp {{
class Search {{
  std::vector<int> data;
  int calls;
  {helper}
  void scan(int depth, int &total) {{
    for (auto &value : data) {{
      if (depth > 0) {{
        {write}
        scan(depth - 1, total);
      }} else {{
        total += value;
      }}
    }}
  }}
public:
  Search() : data(2, 1), calls(0) {{}}
  int run(int depth) {{
    int total = 0;
    scan(depth, total);
    return total;
  }}
}};
}}
""")
            return translator.translate_file(source, [], [], "c++23", [])

    def test_keeps_reference_output_without_writing_back_receiver(self):
        lean = self.translate()
        signature = next(line for line in lean.splitlines() if line.startswith("def cp.Search.scan_rec "))
        self.assertIn(": Cpp.M Int :=", signature)
        self.assertIn("total := t", lean)
        self.assertNotIn("data := t", lean)

    def test_rejects_writing_receiver_field_during_recursion(self):
        with self.assertRaisesRegex(translator.Unsupported, "range for over a vector the body changes"):
            self.translate("calls++;")

    def test_rejects_call_to_mutating_receiver_member(self):
        with self.assertRaisesRegex(translator.Unsupported, "range for over a vector the body changes"):
            self.translate("record();", "void record() { calls++; }")


if __name__ == "__main__":
    unittest.main()
