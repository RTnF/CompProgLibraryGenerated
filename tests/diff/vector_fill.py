"""Differential test commands for vector_fill (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)
lines = ["call vector_fill 0 5", "call vector_fill 2 1 2 -2147483648"]
for _ in range(200):
    n = rng.randint(0, 30)
    xs = [rng.randint(-1000, 1000) for _ in range(n)]
    lines.append("call vector_fill " + " ".join(map(str, [n, *xs, rng.randint(-1000, 1000)])))
print("\n".join(lines))
