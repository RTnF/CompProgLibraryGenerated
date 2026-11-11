"""Differential test commands for count and lower_bound_index (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)
lines = ["call count 0 5 0 -1", "call lower_bound_index 0 7"]
for _ in range(300):
    n = rng.randint(0, 20)
    xs = [rng.randint(-3, 3) for _ in range(n)]
    b = rng.randint(0, n)
    e = rng.choice([-1, rng.randint(b, n)])
    lines.append("call count " + " ".join(map(str, [n, *xs, rng.randint(-3, 3), b, e])))
    ys = sorted(rng.randint(-50, 50) for _ in range(n))
    lines.append("call counts " + " ".join(map(str, [n, *sorted(xs)])))
    lines.append("call counts " + " ".join(map(str, [n, *xs])))
    lines.append("call lower_bound_index " + " ".join(map(str, [n, *ys, rng.randint(-60, 60)])))
print("\n".join(lines))
