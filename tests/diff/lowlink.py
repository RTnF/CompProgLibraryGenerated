"""Differential test commands for lowlink (verifier/diff_harness.py)."""
import random

rng = random.Random(20261113)


def vec(xs):
    return " ".join(map(str, [len(xs), *xs]))


lines = []
for case in range(300):
    n = rng.randint(0, 12)
    edges = set()
    if n > 1:
        for _ in range(rng.randint(0, 2 * n)):
            u, v = rng.randrange(n), rng.randrange(n)
            if u != v:
                edges.add((min(u, v), max(u, v)))
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    for row in adj:
        rng.shuffle(row)
    head, target = [0], []
    for row in adj:
        target += row
        head.append(len(target))
    scratch = [rng.randint(-5, 5) for _ in range(n)]
    lines.append(f"call lowlink {vec(head)} {vec(target)} {vec([-1] * n)} {vec(scratch)} {vec([-1] * n)} "
                 f"{vec([0] * n)} {vec(scratch)} {vec(scratch)} {n}")
print("\n".join(lines))
