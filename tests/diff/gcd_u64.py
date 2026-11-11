"""Differential test commands for gcd_u64 (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)
lines = ["call gcd_u64 0 0", f"call gcd_u64 {2**64 - 1} {2**63}"]
for _ in range(500):
    a = rng.choice([0, 1, rng.randint(0, 1000), rng.randint(0, 2**64 - 1)])
    b = rng.choice([0, 1, rng.randint(0, 1000), rng.randint(0, 2**64 - 1)])
    lines.append(f"call gcd_u64 {a} {b}")
print("\n".join(lines))
