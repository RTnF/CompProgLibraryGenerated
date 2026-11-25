"""Differential test commands for ListGraph<long long, Edge<long long>> (verifier/diff_harness.py).

Graphs built with both constructors, add_node, add_edge and add_bidirectional_edge with and without a cost (the
pack variants @0 = (), @1 = (long long)); the rows are read with operator[] (the edges with their ids, which come
from the Edge<long long> counter shared by all graphs). distance(from) on a graph without computed distances
returns an empty vector."""
import random

rng = random.Random(20261125)
lines = []
for k in range(40):
    if rng.random() < 0.2:
        lines.append("new ListGraph.init_0")
        n = 0
    else:
        n = rng.randint(1, 6)
        lines.append(f"new ListGraph.init_int {n}")
    for _ in range(rng.randint(0, 25)):
        r = rng.random()
        if r < 0.1 or n == 0:
            lines.append(f"do ListGraph.add_node {k}")
            n += 1
            continue
        a, b = rng.randrange(n), rng.randrange(n)
        c = rng.randint(-10**9, 10**9)
        if r < 0.4:
            lines.append(f"do ListGraph.add_edge@0 {k} {a} {b}")
        elif r < 0.7:
            lines.append(f"do ListGraph.add_edge@1 {k} {a} {b} {c}")
        elif r < 0.8:
            lines.append(f"do ListGraph.add_bidirectional_edge@0 {k} {a} {b}")
        elif r < 0.9:
            lines.append(f"do ListGraph.add_bidirectional_edge@1 {k} {a} {b} {c}")
        else:
            lines.append(f"do ListGraph.distance_int {k} {rng.randrange(n)}")
            lines.append(f"do ListGraph.reset_shortest {k}")
    for i in range(n):
        lines.append(f"do ListGraph.op_index {k} {i}")
print("\n".join(lines))
