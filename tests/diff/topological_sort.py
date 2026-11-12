"""Differential test commands for topological_sort (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)


def vec(xs):
    return " ".join(map(str, [len(xs), *xs]))


lines = []
for case in range(300):
    n = rng.randint(0, 10)
    adj = [[] for _ in range(n)]
    if n > 0:
        dag = case % 2 == 0
        for _ in range(rng.randint(0, 3 * n)):
            u, v = rng.randrange(n), rng.randrange(n)
            if dag and u >= v:
                continue
            adj[u].append(v)
    head, target = [0], []
    for row in adj:
        target += row
        head.append(len(target))
    order = [rng.randint(-9, 9) for _ in range(n)]
    lines.append(f"call topological_sort {vec(head)} {vec(target)} {vec([0] * n)} {vec(order)} {n}")
print("\n".join(lines))
