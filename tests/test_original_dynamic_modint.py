"""Sanitizer regression for arithmetic and persistent factorial caches."""
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "verifier"))
import lean_translate
from lean_env import lean_environment
LAKE, LAKE_ENV = lean_environment()


class OriginalDynamicModIntTests(unittest.TestCase):
    def test_arithmetic_stream_and_cache(self):
        with tempfile.TemporaryDirectory(prefix="dynamic-modint-original-") as directory:
            binary = Path(directory) / "dynamic_modint"
            subprocess.run([
                "g++", "-std=c++23", "-O1", "-fsanitize=address,undefined",
                "-fno-sanitize-recover=all", "-ftrivial-auto-var-init=pattern",
                "-I", str(ROOT / "experiments/library/cpp"),
                str(ROOT / "tests/imports/original_dynamic_modint.cpp"),
                "-o", str(binary),
            ], check=True, timeout=60)
            env = dict(os.environ, ASAN_OPTIONS="detect_leaks=0:halt_on_error=1",
                       UBSAN_OPTIONS="halt_on_error=1")
            subprocess.run([str(binary)], check=True, env=env, timeout=30)

    def test_full_source_model_preserves_and_resets_caches(self):
        tree = ROOT / "experiments/library/cpp"
        source = (tree / "modint/dynamic_modint.hpp").read_text()
        template = tree / "template/small_template.hpp"
        source = source.replace('#include "template/small_template.hpp"',
                                f'#include "{template}"\nnamespace cp {{')
        source = re.sub(r"(?<![\w:])(enable_if_t|is_signed_v)\b", r"std::\1", source)
        source += "\n} // namespace cp\n"
        with tempfile.TemporaryDirectory(prefix="dynamic-modint-model-") as directory:
            header = Path(directory) / "DynamicModInt.hpp"
            header.write_text(source)
            model = lean_translate.translate_file(header, [])
            states = re.findall(r"^structure (cp\.GlobalState_\w+) ", model, re.MULTILINE)
            self.assertEqual(len(states), 1)
            initializers = re.findall(r"^def (cp\.initializeGlobals_\w+) ", model, re.MULTILINE)
            self.assertEqual(len(initializers), 1)
            lean = header.with_suffix(".lean")
            bindings = (
                f"\nopen Proofs.Cpp.Gen\n"
                f"abbrev DynamicModIntState := {states[0]}\n"
                f"abbrev dynamicModIntStartup := {initializers[0]}\n"
            )
            lean_command = [LAKE, "env", "lean"]
            lean_env = dict(LAKE_ENV)
            lean.write_text(model + bindings + """
open Proofs.Cpp.Gen
def main : IO Unit := do
  let some (start, _) := dynamicModIntStartup.run 0 | throw (IO.userError "startup")
  let state := { start with DynamicModInt_m := 7 }
  let some ((a, state), _) := (cp.factorial_inv 2 state).run 0
    | throw (IO.userError "inverse before change")
  IO.println a.x
  let some ((b, state), _) := (cp.C 7 2 state).run 0
    | throw (IO.userError "choose before change")
  IO.println b.x
  let state := { state with DynamicModInt_m := 11 }
  let some ((c, state), _) := (cp.factorial_inv 2 state).run 0
    | throw (IO.userError "inverse after change")
  IO.println c.x
  let some ((d, _), _) := (cp.C 7 2 state).run 0
    | throw (IO.userError "choose after change")
  IO.println d.x
""")
            result = subprocess.run(
                lean_command + ["--run", str(lean)], text=True, capture_output=True,
                cwd=ROOT, timeout=60, env=lean_env,
            )
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout.splitlines(), ["4", "0", "6", "10"])


if __name__ == "__main__":
    unittest.main()
