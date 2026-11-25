"""Differential test commands for FlowEdge<T> (verifier/diff_harness.py).

Edges built with the three constructors, interleaved, with negative and positive capacities (clamped to 0);
every public field is read back. The ids are 0, 1, 2, ... in construction order."""
import random

rng = random.Random(20261125)
lines = []
for k in range(300):
    a, b, r = rng.randint(-5, 1000), rng.randint(-5, 1000), rng.randint(-1, 50)
    cap, cost = rng.randint(-10**9, 10**9), rng.randint(-10**9, 10**9)
    kind = rng.randrange(3)
    if kind == 0:
        lines.append(f"new FlowEdge.init_int_int_int_T_T {a} {b} {r} {cap} {cost}")
    elif kind == 1:
        lines.append(f"new FlowEdge.init_int_int_int_T {a} {b} {r} {cap}")
    else:
        lines.append(f"new FlowEdge.init_int_int_int {a} {b} {r}")
    for field in ("from", "to", "rev", "id", "cap", "cost"):
        lines.append(f"field FlowEdge.{field} {k}")
print("\n".join(lines))
