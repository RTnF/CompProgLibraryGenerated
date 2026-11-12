"""Differential test commands for UnionFind (verifier/diff_harness.py)."""
import random

rng = random.Random(20261113)
lines = []
sizes = []


def new(command, n):
    lines.append(command)
    sizes.append(n)


new("new UnionFind.init_0", 0)
for _ in range(30):
    n = rng.randint(0, 30)
    new(f"new UnionFind.init_int {n}", n)
for _ in range(3000):
    k = rng.randrange(len(sizes))
    n = sizes[k]
    op = rng.random()
    if n == 0 or op < 0.1:
        lines.append(f"do UnionFind.num_groups {k}")
    elif op < 0.45:
        lines.append(f"do UnionFind.unite {k} {rng.randrange(n)} {rng.randrange(n)}")
    elif op < 0.65:
        lines.append(f"do UnionFind.same {k} {rng.randrange(n)} {rng.randrange(n)}")
    elif op < 0.85:
        lines.append(f"do UnionFind.root {k} {rng.randrange(n)}")
    else:
        lines.append(f"do UnionFind.size_ {k} {rng.randrange(n)}")
print("\n".join(lines))
