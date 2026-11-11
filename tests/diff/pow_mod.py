"""Differential test commands for pow_mod (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)
lines = ["call pow_mod 0 0 1", "call pow_mod 5 0 7", f"call pow_mod {2**64 - 1} {2**64 - 1} {2**32}",
         f"call pow_mod 3 {2**64 - 1} {2**32 - 5}"]
for _ in range(400):
    m = rng.choice([1, 2, rng.randint(1, 1000), rng.randint(1, 2**32)])
    lines.append(f"call pow_mod {rng.randint(0, 2**64 - 1)} {rng.randint(0, 2**rng.randint(0, 64) - 1)} {m}")
print("\n".join(lines))
