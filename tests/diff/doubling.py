"""Differential test commands for doubling (verifier/diff_harness.py)."""
import random

rng = random.Random(20261113)


def vec(xs):
    return " ".join(map(str, [len(xs), *xs]))


lines = []
for _ in range(200):
    n = rng.randint(0, 12)
    v = [rng.randrange(n) for _ in range(n)] if n else []
    k = rng.choice([1, 2, 3, rng.randint(1, 1000), rng.randint(1, 2**20)])
    lines.append(f"call doubling {vec(v)} {k}")
print("\n".join(lines))
