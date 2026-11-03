"""Tie safe_mod's proofs to the original and candidate syntax-generated IR."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "verifier"))
from state_ir import lower_source, emit_lean
from offline import disable_network


def main():
    disable_network()
    original = lower_source(ROOT / "experiments/library/cpp/number_theory/floor_sum.hpp",
                            "safe_mod", [ROOT / "experiments/library/cpp"])
    candidate = lower_source(ROOT / "library/safe_mod.hpp")
    if original != candidate:
        raise RuntimeError("original/candidate safe_mod common IR mismatch")
    generated = emit_lean(candidate, "Proofs.SafeModInstance")
    if (ROOT / "Proofs/Generated/SafeMod.lean").read_text() != generated:
        raise RuntimeError("safe_mod C++/IR/generated Lean mismatch; regenerate and reprove")
    print("original and candidate safe_mod match the common generated proof input")


if __name__ == "__main__":
    main()
