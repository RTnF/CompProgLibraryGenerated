"""Differential test commands for tree_path (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)


def vec(xs):
    return " ".join(map(str, [len(xs), *xs]))


lines = []
for _ in range(300):
    # A random rooted tree: parent[v] < v for v > 0, parent[root] arbitrary; `to` lies below `from`.
    n = rng.randint(1, 12)
    parent = [rng.randint(-1, 0)] + [rng.randrange(v) for v in range(1, n)]
    to = rng.randrange(n)
    chain = [to]
    while chain[-1] != 0:
        chain.append(parent[chain[-1]])
    frm = rng.choice(chain)
    m = chain.index(frm)
    out = [rng.randint(-9, 9) for _ in range(m + 1 + rng.randint(0, 3))]
    lines.append(f"call tree_path {vec(parent)} {vec(out)} {frm} {to}")
print("\n".join(lines))
