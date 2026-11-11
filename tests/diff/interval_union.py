"""Differential test commands for interval_union_inclusive (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)
lines = ["call interval_union_inclusive 0"]
for _ in range(400):
    n = rng.randint(0, 12)
    tokens = [n]
    for _ in range(n):
        l = rng.randint(-20, 20)
        tokens += [l, l + rng.randint(0, 6)]
    lines.append("call interval_union_inclusive " + " ".join(map(str, tokens)))
print("\n".join(lines))
