"""Differential test commands for square_matrix (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)


def vec(xs):
    return " ".join(map(str, [len(xs), *xs]))


def mat(n, extra=0):
    return [rng.choice([0, 1, 2**64 - 1, rng.randrange(2**64)]) for _ in range(n * n + extra)]


lines = []
for _ in range(60):
    n = rng.randint(0, 4)
    a, b, c = mat(n, rng.randint(0, 2)), mat(n, rng.randint(0, 2)), mat(n, rng.randint(0, 2))
    lines.append(f"call mat_mul {vec(a)} {vec(b)} {vec(c)} {n}")
    lines.append(f"call mat_add_assign {vec(a)} {vec(b)} {n}")
    lines.append(f"call mat_sub_assign {vec(a)} {vec(b)} {n}")
    lines.append(f"call mat_zero {vec(a)} {n}")
    lines.append(f"call mat_negate {vec(a)} {n}")
    lines.append(f"call mat_identity {vec(a)} {n}")
    lines.append(f"call mat_equal {vec(a)} {vec(a if rng.random() < 0.5 else b)} {n}")
    e = rng.choice([0, 1, 2, 3, rng.randrange(100), rng.randrange(2**64)])
    lines.append(f"call mat_pow {vec(a)} {vec(mat(n))} {vec(mat(n))} {vec(mat(n))} {n} {e}")
print("\n".join(lines))
