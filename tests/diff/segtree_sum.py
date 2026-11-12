"""Differential test commands for segtree_sum (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)
M = 2**64


def vec(xs):
    return " ".join(map(str, [len(xs), *xs]))


def tree(n):
    node = [0] * (2 * n)
    for i in range(n):
        node[n + i] = rng.choice([0, 1, M - 1, rng.randrange(M)])
    for i in range(n - 1, 0, -1):
        node[i] = (node[2 * i] + node[2 * i + 1]) % M
    node[0] = rng.randrange(M)
    return node


lines = []
for _ in range(200):
    n = rng.randint(1, 13)
    node = tree(n)
    l = rng.randint(0, n)
    r = rng.randint(l, n)
    lines.append(f"call segtree_sum_product {vec(node)} {l} {r}")
    lines.append(f"call segtree_sum_set {vec(node)} {rng.randrange(n)} {rng.randrange(M)}")
print("\n".join(lines))
