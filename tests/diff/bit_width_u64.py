"""Differential test commands for bit_width_u64 (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)
lines = [f"call bit_width_u64 {v}" for v in [0, 1, 2, 3, 2**63 - 1, 2**63, 2**64 - 1]]
for _ in range(300):
    lines.append(f"call bit_width_u64 {rng.randint(0, 2**rng.randint(0, 64) - 1)}")
print("\n".join(lines))
