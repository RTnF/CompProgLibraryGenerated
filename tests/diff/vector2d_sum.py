"""Differential test commands for vector2d_sum (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)
lines = ["call vector2d_sum 0", "call vector2d_sum 2 0 0"]
for _ in range(200):
    rows = rng.randint(0, 8)
    tokens = [rows]
    for _ in range(rows):
        cols = rng.randint(0, 8)
        tokens += [cols] + [rng.randint(-1000, 1000) for _ in range(cols)]
    lines.append("call vector2d_sum " + " ".join(map(str, tokens)))
print("\n".join(lines))
