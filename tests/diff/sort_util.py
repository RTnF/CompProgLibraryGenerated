"""Differential test commands for sort_util (verifier/diff_harness.py)."""
import random

rng = random.Random(20261113)


def vec(xs):
    return " ".join(map(str, [len(xs), *xs]))


lines = []
for _ in range(150):
    n = rng.randint(0, 12)
    p = list(range(n))
    rng.shuffle(p)
    lines.append(f"call inv_perm {vec(p)}")
    xs = [rng.randint(-5, 5) for _ in range(n)]
    lines.append(f"call compress {vec(xs)} {vec([0] * n)} {vec([0] * n)}")
    lines.append(f"call sort_vector {vec(xs)}")
    lines.append(f"call dedup_vector {vec(sorted(xs) if rng.random() < 0.5 else xs)}")
print("\n".join(lines))
