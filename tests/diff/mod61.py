"""Differential test commands for mod61 (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)
M = 2**61 - 1
special = [0, 1, M - 1, M, M + 1, 2**61, 2**62, 2**64 - 1, 2 * M, 2 * M - 1]
lines = [f"call mod61 {x}" for x in special]
lines += [f"call mod61 {rng.randrange(2**64)}" for _ in range(200)]
small = [0, 1, M - 1, M, 2**61 - 1, 2**60, 2**31, 2**31 - 1]
lines += [f"call mul61 {a} {b}" for a in small for b in small]
lines += [f"call mul61 {rng.randrange(2**61)} {rng.randrange(2**61)}" for _ in range(200)]
print("\n".join(lines))
