"""Differential test commands for chmax/chmin (verifier/diff_harness.py)."""
import random

rng = random.Random(20261113)
lines = []
vals = [-2**63, -1, 0, 1, 2**63 - 1]
for _ in range(200):
    a = rng.choice(vals + [rng.randint(-100, 100)])
    b = rng.choice(vals + [rng.randint(-100, 100), a])
    lines.append(f"call {rng.choice(['chmax', 'chmin'])} {a} {b}")
print("\n".join(lines))
