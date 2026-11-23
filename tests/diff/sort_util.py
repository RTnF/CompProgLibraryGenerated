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
    off = rng.randint(-3, 3)
    lines.append(f"call compress_vec_vec_int {vec(xs)} {vec([9] * rng.randint(0, 3))} {off}")
    lines.append(f"call compress_vec_int {vec(xs)} {off}")
    lines.append(f"call arg_sort {vec(xs)}")
    lines.append(f"call inv_arg_sort {vec(xs)}")
    lines.append(f"call sort_vector {vec(xs)}")
    lines.append(f"call dedup_vector {vec(sorted(xs) if rng.random() < 0.5 else xs)}")
print("\n".join(lines))
