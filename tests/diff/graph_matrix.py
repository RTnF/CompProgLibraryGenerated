"""Differential test commands for MatrixGraph<long long> (verifier/diff_harness.py).

Random graphs with nonnegative and negative costs; `distance`, `get_shortest_path` and `has_negative_cycle` are called
after `warshall_floyd` (their precondition). `get_shortest_path` is called only on graphs without a negative cycle
(with one, following the parents need not stop), which the generator decides by running the same in-place loop."""
import random

rng = random.Random(20261125)
U = (2 ** 63 - 1) >> 2
lines = []
count = 0


def negative_cycle(n, mat):
    d = [row[:] for row in mat]
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if d[i][k] + d[k][j] < d[i][j]:
                    d[i][j] = d[i][k] + d[k][j]
    return any(d[i][i] < 0 for i in range(n))


for _ in range(60):
    n = rng.randint(0, 7)
    lines.append(f"new MatrixGraph.init {n}")
    k = count
    count += 1
    mat = [[0 if i == j else U for j in range(n)] for i in range(n)]
    low = rng.choice([0, 0, -3, -8])
    for _ in range(rng.randint(0, n * n + 2) if n else 0):
        a, b = rng.randrange(n), rng.randrange(n)
        c = rng.randint(low, 20)
        if a == b and rng.random() < 0.8:
            continue
        lines.append(f"do MatrixGraph.add_edge {k} {a} {b} {c}")
        mat[a][b] = c
    lines.append(f"do MatrixGraph.warshall_floyd {k}")
    lines.append(f"do MatrixGraph.has_negative_cycle {k}")
    neg = negative_cycle(n, mat)
    for _ in range(2 * n * n):
        a, b = rng.randrange(n), rng.randrange(n)
        lines.append(f"do MatrixGraph.distance {k} {a} {b}")
        if not neg:
            lines.append(f"do MatrixGraph.get_shortest_path {k} {a} {b}")
    # a second call keeps the computed result
    if n:
        lines.append(f"do MatrixGraph.add_edge {k} 0 {n - 1} -100")
        lines.append(f"do MatrixGraph.warshall_floyd {k}")
        lines.append(f"do MatrixGraph.distance {k} 0 {n - 1}")
print("\n".join(lines))
