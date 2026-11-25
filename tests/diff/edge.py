"""Differential test commands for Edge<T> (verifier/diff_harness.py).

Edges built with both constructors, interleaved; every public field is read back. The ids come from the counter
of the specialization, so they are 0, 1, 2, ... in construction order."""
import random

rng = random.Random(20261125)
lines = []
for k in range(300):
    a, b = rng.randint(-5, 1000), rng.randint(-5, 1000)
    if rng.random() < 0.5:
        lines.append(f"new Edge.init_int_int_T {a} {b} {rng.randint(-10**9, 10**9)}")
    else:
        lines.append(f"new Edge.init_int_int {a} {b}")
    for field in ("from", "to", "id", "cost"):
        lines.append(f"field Edge.{field} {k}")
print("\n".join(lines))
