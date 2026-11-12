"""Differential test commands for prim (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)
INF = 2**62


def vec(xs):
    return " ".join(map(str, [len(xs), *xs]))


lines = []
for _ in range(300):
    n = rng.randint(1, 9)
    adj = [[] for _ in range(n)]
    for _ in range(rng.randint(0, 2 * n)):
        u, v, c = rng.randrange(n), rng.randrange(n), rng.randint(0, 20)
        adj[u].append((v, c))
        adj[v].append((u, c))
    head, target, cost = [0], [], []
    for row in adj:
        rng.shuffle(row)
        for w, c in row:
            target.append(w)
            cost.append(c)
        head.append(len(target))
    lines.append(f"call prim {vec(head)} {vec(target)} {vec(cost)} {vec([INF] * n)} {vec([0] * n)} {n} {INF}")
print("\n".join(lines))
