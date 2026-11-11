"""Differential test commands for Interval (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)
lines = ["new Interval.init_0"]
count = 1
for _ in range(60):
    s = rng.randint(-5, 5)
    lines.append(f"new Interval.init_T_T {s} {s + rng.randint(0, 4)}")
    count += 1
for _ in range(600):
    a, b = rng.randrange(count), rng.randrange(count)
    op = rng.choice(["start", "end_", "is_null", "length", "op_eq", "op_ne", "op_lt", "op_gt", "op_le", "op_ge",
                     "intersection"])
    if op in ("start", "end_", "is_null", "length"):
        lines.append(f"do Interval.{op} {a}")
    else:
        lines.append(f"do Interval.{op} {a} {b}")
        if op == "intersection":
            lines.append(f"do Interval.start {count}")
            lines.append(f"do Interval.end_ {count}")
            lines.append(f"do Interval.is_null {count}")
            count += 1
print("\n".join(lines))
