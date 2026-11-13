"""Differential test commands for tree_full_dp with P = DpHeight<long long> (verifier/diff_harness.py)."""
import random

rng = random.Random(20261113)


def vec(xs):
    return " ".join(map(str, [len(xs), *xs]))


lines = []
for _ in range(200):
    n = rng.randint(1, 12)
    par = [-1] + [rng.randrange(i) for i in range(1, n)]
    adj = [[] for _ in range(n)]
    for v in range(1, n):
        adj[par[v]].append(v)
        adj[v].append(par[v])
    for row in adj:
        rng.shuffle(row)
    labels = list(range(n))
    rng.shuffle(labels)
    # relabel the vertices so that the root and the order vary
    inv = {old: new for new, old in enumerate(labels)}
    nadj = [[] for _ in range(n)]
    for old in range(n):
        nadj[inv[old]] = [inv[w] for w in adj[old]]
    root = inv[0]
    parent = [0] * n
    parent[root] = root
    for v in range(1, n):
        parent[inv[v]] = inv[par[v]]
    order, seen = [root], {root}
    for v in order:
        for w in nadj[v]:
            if w not in seen:
                seen.add(w)
                order.append(w)
    head, target = [0], []
    for row in nadj:
        target += row
        head.append(len(target))
    m = len(target)
    lines.append(f"call tree_full_dp {vec(head)} {vec(target)} {vec(parent)} {vec(order)} {vec([0] * n)} "
                 f"{vec([0] * m)} {vec([0] * m)} {vec([0] * n)} {vec([0] * n)} {root} {n}")
print("\n".join(lines))
