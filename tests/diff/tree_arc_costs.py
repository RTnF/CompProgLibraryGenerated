"""Differential test commands for tree_arc_costs (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)


def vec(xs):
    return " ".join(map(str, [len(xs), *xs]))


lines = []
for _ in range(300):
    m = rng.randint(0, 12)
    cost = [rng.randint(-10**12, 10**12) for _ in range(m + rng.randint(0, 2))]
    ac = [rng.randint(-9, 9) for _ in range(2 * m + rng.randint(0, 3))]
    lines.append(f"call tree_arc_costs {vec(cost)} {vec(ac)} {m}")
print("\n".join(lines))
