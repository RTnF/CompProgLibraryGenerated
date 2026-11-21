"""Differential test commands for find_cycle (verifier/diff_harness.py)."""
import random

rng = random.Random(20261121)


def vec(xs):
    return " ".join(map(str, [len(xs), *xs]))


lines = []
for case in range(400):
    n = rng.randint(0, 10)
    adj = [[] for _ in range(n)]
    if n > 0:
        for _ in range(rng.randint(0, 2 * n)):
            adj[rng.randrange(n)].append(rng.randrange(n))
    head, target = [0], []
    for row in adj:
        target += row
        head.append(len(target))
    scratch = [rng.randint(-5, 5) for _ in range(n)]
    lines.append(f"call find_cycle {vec(head)} {vec(target)} {vec([0] * n)} {vec(scratch)} {vec(scratch)} "
                 f"{vec(scratch)} {n}")
print("\n".join(lines))
