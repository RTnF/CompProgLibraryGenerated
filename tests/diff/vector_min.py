"""Differential test commands for vector_min (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)
lines = ["call vector_min 1 -2147483648", "call vector_min 3 2147483647 5 2147483647"]
for _ in range(300):
    n = rng.randint(1, 30)
    xs = [rng.randint(-20, 20) for _ in range(n)]
    lines.append("call vector_min " + " ".join(map(str, [n, *xs])))
print("\n".join(lines))
