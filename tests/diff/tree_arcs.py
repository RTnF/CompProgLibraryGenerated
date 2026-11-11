"""Differential test commands for tree_arcs (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)


def vec(xs):
    return " ".join(map(str, [len(xs), *xs]))


lines = []
for _ in range(300):
    m = rng.randint(0, 12)
    fr = [rng.randint(-9, 9) for _ in range(m + rng.randint(0, 2))]
    to = [rng.randint(-9, 9) for _ in range(m + rng.randint(0, 2))]
    af = [rng.randint(-9, 9) for _ in range(2 * m + rng.randint(0, 3))]
    at = [rng.randint(-9, 9) for _ in range(2 * m + rng.randint(0, 3))]
    lines.append(f"call tree_arcs_from_list {vec(fr)} {vec(to)} {vec(af)} {vec(at)} {m}")
print("\n".join(lines))
