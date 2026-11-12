"""Differential test commands for tree_root (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)


def vec(xs):
    return " ".join(map(str, [len(xs), *xs]))


lines = []
for case in range(300):
    n = rng.randint(1, 12)
    adj = [[] for _ in range(n)]
    if case % 2 == 0:
        # a symmetric tree
        for v in range(1, n):
            u = rng.randrange(v)
            adj[u].append(v)
            adj[v].append(u)
    else:
        # an arbitrary directed graph (the theorem does not need a tree)
        for _ in range(rng.randint(0, 3 * n)):
            adj[rng.randrange(n)].append(rng.randrange(n))
    for row in adj:
        rng.shuffle(row)
    head, target = [0], []
    for row in adj:
        target += row
        head.append(len(target))
    cost = [rng.randint(-10**6, 10**6) for _ in target]
    parent = [-1] * n
    depth = [rng.randint(-9, 9) for _ in range(n)]
    cd = [rng.randint(-9, 9) for _ in range(n)]
    stk = [rng.randint(-9, 9) for _ in range(n + 1)]
    root = rng.randrange(n)
    lines.append(f"call tree_root {vec(head)} {vec(target)} {vec(cost)} {vec(parent)} {vec(depth)} {vec(cd)} "
                 f"{vec(stk)} {root} {n}")
print("\n".join(lines))
