"""Differential test commands for tree_ancestor (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)


def vec(xs):
    return " ".join(map(str, [len(xs), *xs]))


def table(f, levels):
    rows = [f]
    for _ in range(levels - 1):
        prev = rows[-1]
        rows.append([prev[prev[x]] for x in range(len(f))])
    return rows


lines = []
for _ in range(300):
    n = rng.randint(1, 10)
    f = [rng.randrange(n) for _ in range(n)]
    i = rng.choice([0, 1, 2, 3, rng.randint(0, 40), rng.randint(0, 2000)])
    levels = max(1, i.bit_length())
    rows = table(f, levels)
    anc = " ".join([str(len(rows))] + [vec(r) for r in rows])
    lines.append(f"call tree_ancestor {anc} {rng.randrange(n)} {i}")
print("\n".join(lines))
