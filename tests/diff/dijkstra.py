"""Differential test commands for dijkstra (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)
INF = 2**62


def vec(xs):
    return " ".join(map(str, [len(xs), *xs]))


lines = []
for _ in range(300):
    n = rng.randint(1, 9)
    adj = [[] for _ in range(n)]
    for _ in range(rng.randint(0, 3 * n)):
        adj[rng.randrange(n)].append((rng.randrange(n), rng.randint(0, 20)))
    head, target, cost = [0], [], []
    for row in adj:
        for w, c in row:
            target.append(w)
            cost.append(c)
        head.append(len(target))
    dist = [INF] * n
    for s in rng.sample(range(n), rng.randint(1, min(2, n))):
        dist[s] = rng.randint(0, 5)
    lines.append(f"call dijkstra {vec(head)} {vec(target)} {vec(cost)} {vec(dist)} {vec([0] * n)} {vec([-1] * n)} {n} {INF}")
print("\n".join(lines))
