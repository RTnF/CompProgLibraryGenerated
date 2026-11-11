"""Differential test commands for tree_edges (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)


def vec(xs):
    return " ".join(map(str, [len(xs), *xs]))


lines = []
for _ in range(300):
    n = rng.randint(0, 10)
    parent = [rng.randint(-2, n + 1) for _ in range(n + rng.randint(0, 2))]
    fr = [rng.randint(-9, 9) for _ in range(2 * n + rng.randint(0, 3))]
    to = [rng.randint(-9, 9) for _ in range(2 * n + rng.randint(0, 3))]
    lines.append(f"call tree_edges_from_parent {vec(parent)} {vec(fr)} {vec(to)} {n}")
print("\n".join(lines))
