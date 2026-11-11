"""Differential test commands for tree_find_root (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)


def vec(xs):
    return " ".join(map(str, [len(xs), *xs]))


lines = []
for _ in range(300):
    n = rng.randint(0, 10)
    parent = [rng.randint(-2, n) for _ in range(n + rng.randint(0, 2))]
    lines.append(f"call tree_find_root {vec(parent)} {n}")
print("\n".join(lines))
