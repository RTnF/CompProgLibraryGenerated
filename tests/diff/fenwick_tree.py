"""Differential test commands for FenwickTree (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)
lines = []
sizes = []


def new(command, n):
    lines.append(command)
    sizes.append(n)


new("new FenwickTree.init_0", 0)
for _ in range(40):
    n = rng.randint(0, 20)
    if rng.random() < 0.5:
        new(f"new FenwickTree.init_int {n}", n)
    else:
        xs = [rng.randint(-1000, 1000) for _ in range(n)]
        new("new FenwickTree.init_vec " + " ".join(map(str, [n, *xs])), n)
for _ in range(2000):
    k = rng.randrange(len(sizes))
    n = sizes[k]
    op = rng.random()
    if op < 0.4:
        i = rng.randint(0, n + 2)
        lines.append(f"do FenwickTree.add {k} {i} {rng.randint(-1000, 1000)}")
    elif op < 0.7:
        lines.append(f"do FenwickTree.sum_int {k} {rng.randint(0, n)}")
    else:
        l = rng.randint(0, n)
        lines.append(f"do FenwickTree.sum_int_int {k} {l} {rng.randint(l, n)}")
print("\n".join(lines))
