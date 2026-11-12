"""Differential test commands for floyd_warshall (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)
BIG = 10**15


def vec(xs):
    return " ".join(map(str, [len(xs), *xs]))


lines = []
for _ in range(150):
    n = rng.randint(0, 7)
    w = [[0 if i == j else rng.choice([BIG, rng.randint(0, 100)]) for j in range(n)] for i in range(n)]
    lines.append(f"call floyd_warshall_vec_int {vec([x for row in w for x in row])} {n}")
    rows = " ".join([str(n)] + [vec(row) for row in w])
    lines.append(f"call floyd_warshall_vec {rows}")
print("\n".join(lines))
