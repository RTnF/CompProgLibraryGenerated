"""Differential test commands for tree_height (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)


def vec(xs):
    return " ".join(map(str, [len(xs), *xs]))


lines = []
for _ in range(300):
    n = rng.randint(0, 10)
    d0 = [rng.randint(-10**12, 10**12) for _ in range(n + rng.randint(0, 2))]
    d1 = [rng.choice([d0[i] if i < len(d0) else 0, rng.randint(-10**12, 10**12)]) for i in range(n + rng.randint(0, 2))]
    h = [rng.randint(-9, 9) for _ in range(n + rng.randint(0, 3))]
    lines.append(f"call tree_height {vec(d0)} {vec(d1)} {vec(h)} {n}")
print("\n".join(lines))
