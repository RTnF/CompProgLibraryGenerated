"""Differential test commands for countr_zero (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)
lines = [f"call countr_zero_u64 {v}" for v in [0, 1, 2, 2**63, 2**64 - 1, 3 << 40]]
for _ in range(300):
    lines.append(f"call countr_zero_u64 {rng.randint(1, 2**64 - 1) << rng.randint(0, 63) & (2**64 - 1)}")
print("\n".join(lines))
