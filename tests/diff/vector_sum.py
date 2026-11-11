"""Differential test commands for vector_sum (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)
lines = ["call vector_sum 0", "call vector_sum 1 -5", "call vector_sum 3 2147483647 -2147483648 1"]
for _ in range(200):
    n = rng.randint(0, 30)
    xs = [rng.randint(-1000, 1000) for _ in range(n)]
    lines.append("call vector_sum " + " ".join(map(str, [n, *xs])))
print("\n".join(lines))
