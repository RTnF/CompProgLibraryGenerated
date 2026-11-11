"""Differential test commands for csr_build (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)


def vec(xs):
    return " ".join(map(str, [len(xs), *xs]))


lines = []
for _ in range(300):
    n = rng.randint(1, 8)
    m = rng.randint(0, 20)
    fr = [rng.randrange(n) for _ in range(m)]
    to = [rng.randrange(n) for _ in range(m)]
    target = [rng.randint(-9, 9) for _ in range(m)]
    pos = [rng.randint(-9, 9) for _ in range(n)]
    lines.append(f"call csr_build {vec(fr)} {vec(to)} {vec([0] * (n + 1))} {vec(target)} {vec(pos)} {n}")
print("\n".join(lines))
