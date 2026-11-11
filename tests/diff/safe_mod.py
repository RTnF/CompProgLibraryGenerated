"""Differential test commands for safe_mod (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)
lines = []
for _ in range(500):
    m = rng.choice([1, 2, 3, 7, rng.randint(1, 10**9), rng.randint(1, 2**62)])
    x = rng.choice([0, -1, rng.randint(-10**9, 10**9), rng.randint(-2**63, 2**63 - 1)])
    lines.append(f"call safe_mod {x} {m}")
print("\n".join(lines))
