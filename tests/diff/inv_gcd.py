"""Differential test commands for inv_gcd (verifier/diff_harness.py)."""
import random

rng = random.Random(20261112)
lines = ["call inv_gcd 0 1", "call inv_gcd -7 1", f"call inv_gcd {-2**63} {2**63 - 1}"]
for _ in range(500):
    b = rng.choice([rng.randint(1, 100), rng.randint(1, 2**63 - 1)])
    a = rng.choice([rng.randint(-200, 200), rng.randint(-2**63, 2**63 - 1)])
    lines.append(f"call inv_gcd {a} {b}")
print("\n".join(lines))
