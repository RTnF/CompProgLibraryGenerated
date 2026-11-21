"""Differential test commands for factorize (verifier/diff_harness.py)."""
import random

rng = random.Random(20261122)
lines = []
for _ in range(60):
    n = rng.choice([1, 7, rng.randint(1, 1000), rng.randint(1, 2**64 - 1)])
    lines.append(f"call factorize_f {rng.randrange(n)} {rng.randint(1, 3)} {n}")
for n in [9, 15, 21, 91, 561, 8051, 10403, 1000004000003, 4294967291 * 3]:
    for c in (1, 2, 3):
        lines.append(f"call factorize_rho {n} {c} {n}")
ns = list(range(1, 80)) + [561, 1729, 8051, 10403, 2**31 - 1, 2**32 + 15, 2**61 - 1, 2**63, 2**64 - 1, 2**64 - 59,
                           1000000007 * 998244353, 4294967291 * 4294967291, 600851475143, 3 ** 40]
ns += [rng.randint(1, 10**12) for _ in range(40)] + [rng.randint(1, 2**64 - 1) for _ in range(20)]
for n in ns:
    lines.append(f"call factorize_unsorted {n}")
    lines.append(f"call factorize {n}")
    lines.append(f"call factorize_count {n}")
for n in ns:
    if n <= 10**12:
        lines.append(f"call divisors {n}")
print("\n".join(lines))
