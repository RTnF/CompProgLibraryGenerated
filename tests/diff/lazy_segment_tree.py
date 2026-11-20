"""Differential test commands for LazySegmentTree<M, F> (verifier/diff_harness.py).

M and F are bound to the nested value and action classes of algebraic_structure/monoid_lazy.hpp (RangeAddRangeSum and
RangeSetRangeSum; one instance per run, chosen in library/segment_tree/lazy_segment_tree.toml). A value is a pair
(sum, size) and an action is read from its public fields: RangeAdd has one field v, RangeSet has v and noop. The two
action families read the same number of fields, so the commands give two fields when the instance is RangeSet; the
generator prints both variants, selected by the first line of the run (docs/lazy_segment_tree.md). The values stay
small so that the sums fit in 64 bits.
"""
import random
import sys

rng = random.Random(20261120)
lines = []
sizes = []


def value():
    return f"{rng.randint(-3, 3)} 1"


def action(kind):
    if kind == "add":
        return str(rng.randint(-2, 2))
    return f"{rng.randint(-3, 3)} {rng.choice([0, 0, 1])}"


def new(command, n):
    lines.append(command)
    sizes.append(n)


kind = sys.argv[1] if len(sys.argv) > 1 else "add"
new("new LazySegmentTree.init_0", 0)
for _ in range(30):
    n = rng.randint(0, 33)
    if rng.random() < 0.3:
        new(f"new LazySegmentTree.init_int {n}", n)
    else:
        new("new LazySegmentTree.init_vec " + " ".join([str(n), *[value() for _ in range(n)]]), n)
for _ in range(1500):
    k = rng.randrange(len(sizes))
    n = sizes[k]
    op = rng.random()
    if op < 0.15 and n > 0:
        lines.append(f"do LazySegmentTree.set_ {k} {rng.randrange(n)} {value()}")
    elif op < 0.3 and n > 0:
        lines.append(f"do LazySegmentTree.get_ {k} {rng.randrange(n)}")
    elif op < 0.37 and n > 0:
        lines.append(f"do LazySegmentTree.product_all {k}")
    elif op < 0.5 and n > 0:
        lines.append(f"do LazySegmentTree.update_int_F {k} {rng.randrange(n)} {action(kind)}")
    elif op < 0.75:
        l = rng.randint(0, n)
        r = rng.randint(l, n)
        lines.append(f"do LazySegmentTree.update_int_int_F {k} {l} {r} {action(kind)}")
    else:
        l = rng.randint(0, n)
        r = rng.randint(l, n)
        lines.append(f"do LazySegmentTree.product {k} {l} {r}")
print("\n".join(lines))
