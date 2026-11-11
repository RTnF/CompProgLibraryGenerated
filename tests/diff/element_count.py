"""Differential test commands for element_count (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)
lines = ["call element_count 0", "call element_count 1 -2147483648"]
for _ in range(300):
    n = rng.randint(0, 30)
    xs = [rng.randint(-2, 2) for _ in range(n)]
    lines.append("call element_count " + " ".join(map(str, [n, *xs])))
print("\n".join(lines))
