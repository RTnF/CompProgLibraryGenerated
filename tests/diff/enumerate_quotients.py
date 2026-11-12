"""Differential test commands for enumerate_quotients (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)
ns = list(range(0, 40)) + [k * (k + 1) + d for k in (5, 31, 1000) for d in (-1, 0, 1)]
ns += [rng.randrange(10**4) for _ in range(40)] + [rng.randrange(10**7) for _ in range(10)]
print("\n".join(f"call enumerate_quotients {n}" for n in ns))
