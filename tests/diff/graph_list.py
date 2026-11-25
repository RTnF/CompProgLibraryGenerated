"""Differential test commands for ListGraph<long long, Edge<long long>> (verifier/diff_harness.py).

Graphs built with both constructors, add_node, add_edge and add_bidirectional_edge with and without a cost (the
pack variants @0 = (), @1 = (long long)); the rows are read with operator[] (the edges with their ids, which come
from the Edge<long long> counter shared by all graphs). distance(from) on a graph without computed distances
returns an empty vector. On graphs with nonnegative costs, dijkstra (twice: the second call keeps the cache),
both distance members and shortest_path for every target (an unreachable target gives the one-vertex chain)."""
import random

rng = random.Random(20261125)
lines = []
count = 0


def new(line):
    global count
    lines.append(line)
    count += 1
    return count - 1


for _ in range(40):
    if rng.random() < 0.2:
        k = new("new ListGraph.init_0")
        n = 0
    else:
        n = rng.randint(1, 6)
        k = new(f"new ListGraph.init_int {n}")
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

for _ in range(60):
    n = rng.randint(1, 8)
    k = new(f"new ListGraph.init_int {n}")
    for _ in range(rng.randint(0, 3 * n)):
        a, b = rng.randrange(n), rng.randrange(n)
        if rng.random() < 0.3:
            lines.append(f"do ListGraph.add_edge@0 {k} {a} {b}")
        else:
            lines.append(f"do ListGraph.add_bidirectional_edge@1 {k} {a} {b} {rng.randint(0, 30)}"
                         if rng.random() < 0.2 else f"do ListGraph.add_edge@1 {k} {a} {b} {rng.randint(0, 30)}")
    for src in rng.sample(range(n), min(n, 3)):
        lines.append(f"do ListGraph.dijkstra {k} {src}")
        lines.append(f"do ListGraph.dijkstra {k} {src}")
        lines.append(f"do ListGraph.distance_int {k} {src}")
        for t in range(n):
            lines.append(f"do ListGraph.distance_int_int {k} {src} {t}")
            lines.append(f"do ListGraph.shortest_path {k} {src} {t}")
    if rng.random() < 0.5:
        lines.append(f"do ListGraph.add_edge@0 {k} 0 0")
        lines.append(f"do ListGraph.distance_int {k} 0")
# bellman_ford with negative costs (and negative cycles): distance and shortest_path for every target
for _ in range(60):
    n = rng.randint(1, 7)
    k = new(f"new ListGraph.init_int {n}")
    for _ in range(rng.randint(0, 2 * n)):
        a, b = rng.randrange(n), rng.randrange(n)
        lines.append(f"do ListGraph.add_edge@1 {k} {a} {b} {rng.randint(-6, 14)}")
    for src in rng.sample(range(n), min(n, 3)):
        lines.append(f"do ListGraph.bellman_ford {k} {src}")
        lines.append(f"do ListGraph.bellman_ford {k} {src}")
        lines.append(f"do ListGraph.distance_int {k} {src}")
        for t in range(n):
            lines.append(f"do ListGraph.shortest_path {k} {src} {t}")
# prim on undirected graphs with nonnegative costs
for _ in range(60):
    n = rng.randint(0, 8)
    k = new(f"new ListGraph.init_int {n}")
    for _ in range(rng.randint(0, 2 * n)):
        a, b = rng.randrange(n), rng.randrange(n)
        lines.append(f"do ListGraph.add_bidirectional_edge@1 {k} {a} {b} {rng.randint(0, 40)}")
    lines.append(f"do ListGraph.prim {k}")
print("\n".join(lines))
