"""Differential test commands for run_length (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)
lines = ["call run_length 0 0 0", "call run_length 0 2 5 6 2 7 8"]
for _ in range(300):
    n = rng.randint(0, 20)
    extra = rng.randint(0, 3)
    xs = [rng.randint(-2, 2) for _ in range(n)]
    vals = [rng.randint(-9, 9) for _ in range(n + extra)]
    cnts = [rng.randint(-9, 9) for _ in range(n + extra)]
    lines.append("call run_length " + " ".join(map(str, [n, *xs, n + extra, *vals, n + extra, *cnts])))
print("\n".join(lines))
