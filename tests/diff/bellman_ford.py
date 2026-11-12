"""Differential test commands for bellman_ford (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)
INF = 2**62


def vec(xs):
    return " ".join(map(str, [len(xs), *xs]))


lines = []
for case in range(300):
    n = rng.randint(1, 7)
    m = rng.randint(0, 3 * n)
    fr = [rng.randrange(n) for _ in range(m)]
    to = [rng.randrange(n) for _ in range(m)]
    lo = 0 if case % 2 == 0 else -5
    cost = [rng.randint(lo, 9) for _ in range(m)]
    s = rng.randrange(n)
    dist = [INF] * n
    dist[s] = 0
    par = [-1] * n
    lines.append(f"call bellman_ford {vec(fr)} {vec(to)} {vec(cost)} {vec(dist)} {vec(par)} {n} {INF}")
print("\n".join(lines))
