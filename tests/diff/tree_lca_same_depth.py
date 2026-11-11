"""Differential test commands for tree_lca_same_depth (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)


def vec(xs):
    return " ".join(map(str, [len(xs), *xs]))


lines = []
for _ in range(300):
    # A random rooted tree with root 0 (its own parent) and parent[v] < v.
    n = rng.randint(1, 40)
    parent = [0] + [rng.randrange(max(0, v - rng.randint(1, 3)), v) for v in range(1, n)]
    depth = [0] * n
    for v in range(1, n):
        depth[v] = depth[parent[v]] + 1
    d = rng.choice(depth)
    same = [v for v in range(n) if depth[v] == d]
    u, w = rng.choice(same), rng.choice(same)
    levels = max(1, d.bit_length())
    rows = [parent]
    for _ in range(levels - 1):
        prev = rows[-1]
        rows.append([prev[prev[x]] for x in range(n)])
    anc = " ".join([str(len(rows))] + [vec(r) for r in rows])
    lines.append(f"call tree_lca_same_depth {anc} {u} {w} {d}")
print("\n".join(lines))
