"""Differential test commands for tree_distance (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)


def vec(xs):
    return " ".join(map(str, [len(xs), *xs]))


lines = []
for _ in range(300):
    n = rng.randint(1, 10)
    cd = [rng.randint(-10**12, 10**12) for _ in range(n)]
    u, v, w = (rng.randrange(n) for _ in range(3))
    lines.append(f"call tree_distance {vec(cd)} {u} {v} {w}")
print("\n".join(lines))
