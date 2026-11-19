"""Differential test commands for SegmentTree<M> (verifier/diff_harness.py).

M is bound to MonoidMax, MonoidMin and MonoidMul of algebraic_structure/monoid.hpp (one instance per run, chosen in
library/segment_tree/segment_tree.toml); the values stay small so that products of MonoidMul fit in 64 bits after
reduction is not needed: every value is -1, 0, 1 or 2 and at most 40 leaves take part in a product.
"""
import random

rng = random.Random(20261119)
lines = []
sizes = []


def value():
    return rng.choice([-1, 0, 1, 1, 2])


def new(command, n):
    lines.append(command)
    sizes.append(n)


new("new SegmentTree.init_0", 0)
for _ in range(40):
    n = rng.randint(0, 40)
    r = rng.random()
    if r < 0.3:
        new(f"new SegmentTree.init_int {n}", n)
    else:
        new("new SegmentTree.init_vec " + " ".join(map(str, [n, *[value() for _ in range(n)]])), n)
for _ in range(2000):
    k = rng.randrange(len(sizes))
    n = sizes[k]
    op = rng.random()
    if op < 0.3 and n > 0:
        lines.append(f"do SegmentTree.set_ {k} {rng.randrange(n)} {value()}")
    elif op < 0.45 and n > 0:
        lines.append(f"do SegmentTree.get_ {k} {rng.randrange(n)}")
    elif op < 0.55 and n > 0:
        lines.append(f"do SegmentTree.product_all {k}")
    else:
        l = rng.randint(0, n)
        lines.append(f"do SegmentTree.product {k} {l} {rng.randint(l, n)}")
print("\n".join(lines))
