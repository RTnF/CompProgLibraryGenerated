"""Differential test commands for tree_order (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)


def vec(xs):
    return " ".join(map(str, [len(xs), *xs]))


lines = []
for _ in range(300):
    n = rng.randint(1, 14)
    labels = list(range(n))
    rng.shuffle(labels)
    edges = [(labels[rng.randrange(v)], labels[v]) for v in range(1, n)]
    adj = [[] for _ in range(n)]
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    for row in adj:
        rng.shuffle(row)
    head, target = [0], []
    for row in adj:
        target += row
        head.append(len(target))
    root = rng.randrange(n)
    parent = [-1] * n
    parent[root] = root
    stack = [root]
    while stack:
        v = stack.pop()
        for w in adj[v]:
            if parent[w] < 0:
                parent[w] = v
                stack.append(w)
    ord_ = [rng.randint(-9, 9) for _ in range(n)]
    lines.append(f"call tree_order {vec(head)} {vec(target)} {vec(parent)} {vec(ord_)} {root} {n}")
print("\n".join(lines))
