"""Match the original unsigned floor sum to its syntax-generated Lean model."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "verifier"))
from state_ir import lower_source, emit_lean
from offline import disable_network


def main():
    disable_network()
    ir = lower_source(ROOT / "experiments/library/cpp/number_theory/floor_sum.hpp",
                      "floor_sum_unsigned", [ROOT / "experiments/library/cpp"])
    generated = emit_lean(ir, "Proofs.FloorSumUnsignedInstance")
    if (ROOT / "Proofs/Generated/FloorSumUnsigned.lean").read_text() != generated:
        raise RuntimeError("floor_sum_unsigned source/generated model mismatch; regenerate and reprove")
    print("original floor_sum_unsigned matches the common generated Lean model")


if __name__ == "__main__":
    main()
