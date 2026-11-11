"""Differential test commands for CumulativeSum and CumulativeSum2D (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)
lines = []
k1 = k2 = 0
for _ in range(40):
    n = rng.randint(0, 12)
    xs = [rng.randint(-1000, 1000) for _ in range(n)]
    lines.append("new CumulativeSum.init " + " ".join(map(str, [n, *xs])))
    for _ in range(10):
        a = rng.randint(0, n)
        b = rng.randint(a, n)
        lines.append(f"do CumulativeSum.sum_int {k1} {rng.randint(0, n)}")
        lines.append(f"do CumulativeSum.sum_int_int {k1} {a} {b}")
    k1 += 1
    rows, cols = rng.randint(1, 6), rng.randint(1, 6)
    tokens = [rows] + sum(([cols] + [rng.randint(-100, 100) for _ in range(cols)] for _ in range(rows)), [])
    lines.append("new CumulativeSum2D.init " + " ".join(map(str, tokens)))
    for _ in range(10):
        a1 = rng.randint(0, rows); a2 = rng.randint(a1, rows)
        b1 = rng.randint(0, cols); b2 = rng.randint(b1, cols)
        lines.append(f"do CumulativeSum2D.sum_int_int {k2} {rng.randint(0, rows)} {rng.randint(0, cols)}")
        lines.append(f"do CumulativeSum2D.sum_int_int_int_int {k2} {a1} {b1} {a2} {b2}")
    k2 += 1
print("\n".join(lines))
