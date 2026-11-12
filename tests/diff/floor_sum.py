"""Differential test commands for floor_sum (verifier/diff_harness.py)."""
import random

rng = random.Random(20261113)
LO, HI = -2**63, 2**63 - 1
lines = []
for _ in range(400):
    n = rng.choice([0, 1, 2, rng.randrange(100), rng.randrange(2**32)])
    m = rng.choice([1, 2, rng.randrange(1, 100), rng.randrange(1, 2**32)])
    a = rng.choice([0, LO, HI, rng.randrange(-100, 100), rng.randrange(LO, HI + 1)])
    b = rng.choice([0, LO, HI, rng.randrange(-100, 100), rng.randrange(LO, HI + 1)])
    lines.append(f"call floor_sum {n} {m} {a} {b}")
print("\n".join(lines))
