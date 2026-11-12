"""Differential test commands for floor_sum_unsigned (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)
lines = []
for _ in range(400):
    n = rng.choice([0, 1, 2, rng.randrange(100), rng.randrange(2**32)])
    m = rng.choice([1, 2, rng.randrange(1, 100), rng.randrange(1, 2**32)])
    a = rng.choice([0, rng.randrange(100), rng.randrange(2**64)])
    b = rng.choice([0, rng.randrange(100), rng.randrange(2**64)])
    lines.append(f"call floor_sum_unsigned {n} {m} {a} {b}")
print("\n".join(lines))
