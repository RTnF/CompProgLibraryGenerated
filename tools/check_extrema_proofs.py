"""Bind extrema proofs to syntax-generated concrete C++ template instances."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "verifier"))
from state_ir import lower_source, emit_lean
from offline import disable_network


def main():
    disable_network()
    generated = emit_lean(lower_source(ROOT / "tests/imports/update_extrema_instantiations.cpp"),
                          "Proofs.ExtremaInstances")
    actual = (ROOT / "Proofs/ExtremaInstances.lean").read_text()
    if actual != generated:
        raise RuntimeError("extrema C++/IR/generated Lean mismatch; regenerate and reprove")
    print("extrema proof input matches common C++ state generator")


if __name__ == "__main__":
    main()
