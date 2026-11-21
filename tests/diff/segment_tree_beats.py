"""Differential test commands for SegmentTreeBeats (verifier/diff_harness.py).

Every run respects the preconditions of docs/segment_tree_beats.md: 1 <= n, the values and the chmin/chmax/update
arguments are at most M in absolute value, the adds of one object sum to far less than 4e18 - M, and update_val and
add_val use b <= n (chmin, chmax and the queries also get ranges outside [0, n)).
"""
import random

rng = random.Random(20261121)
lines = []
sizes = []
for M in (5, 10 ** 9, 10 ** 17):
    for _ in range(10):
        n = rng.randint(1, 33)
        lines.append("new SegmentTreeBeats.init " + " ".join([str(n), *[str(rng.randint(-M, M)) for _ in range(n)]]))
        sizes.append((n, M))
for _ in range(1500):
    k = rng.randrange(len(sizes))
    n, M = sizes[k]
    a = rng.randint(-1, n + 1)
    b = rng.randint(a, n + 2)
    a2 = rng.randint(0, n)
    b2 = rng.randint(a2, n)
    op = rng.random()
    if op < 0.2:
        lines.append(f"do SegmentTreeBeats.chmin {k} {a} {b} {rng.randint(-M, M)}")
    elif op < 0.4:
        lines.append(f"do SegmentTreeBeats.chmax {k} {a} {b} {rng.randint(-M, M)}")
    elif op < 0.55:
        lines.append(f"do SegmentTreeBeats.add_val {k} {a2} {b2} {rng.randint(-1000, 1000)}")
    elif op < 0.7:
        lines.append(f"do SegmentTreeBeats.update_val {k} {a2} {b2} {rng.randint(-M, M)}")
    elif op < 0.85:
        lines.append(f"do SegmentTreeBeats.calc_max {k} {a} {b}")
    else:
        lines.append(f"do SegmentTreeBeats.calc_min {k} {a} {b}")
print("\n".join(lines))
