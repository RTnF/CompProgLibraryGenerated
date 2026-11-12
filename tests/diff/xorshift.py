"""Differential test commands for xorshift (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)
lines = []
for _ in range(100):
    s = rng.choice([0, 1, 2**64 - 1, 2**63, rng.randrange(2**64)])
    lines.append(f"new Xor64.init {s}")
for k in range(100):
    for _ in range(rng.randint(1, 5)):
        lines.append(f"do Xor64.get_ {k}")
print("\n".join(lines))
