"""Differential test commands for is_prime (verifier/diff_harness.py)."""
import random

rng = random.Random(20261113)
lines = []
for _ in range(100):
    m = rng.choice([1, 2, rng.randint(1, 1000), rng.randint(1, 2**64 - 1)])
    lines.append(f"call mul_mod_u64 {rng.randrange(m)} {rng.randint(0, 2**64 - 1)} {m}")
for _ in range(60):
    m = rng.choice([2, rng.randint(2, 1000), rng.randint(2, 2**64 - 1)])
    lines.append(f"call pow_mod_u64 {rng.randrange(m)} {rng.randint(0, 2**rng.randint(0, 64) - 1)} {m}")
for i in range(14):
    lines.append(f"call mr_base {i}")
for n in [3, 5, 9, 15, 561, 1105, 2**61 - 1, 3215031751, 2**64 - 59]:
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in [2, 3, 37 if 37 <= n - 2 else 2]:
        if a <= n - 2:
            lines.append(f"call mr_witness {n} {d} {r} {a}")
ns = list(range(0, 60)) + [561, 1105, 1729, 2**31 - 1, 2**61 - 1, 3215031751, 2152302898747, 3474749660383,
                           341550071728321, 3825123056546413051, 2**64 - 59, 2**64 - 1, 2**63 + 1]
ns += [rng.randint(0, 2**64 - 1) | 1 for _ in range(30)]
lines += [f"call is_prime {n}" for n in ns]
print("\n".join(lines))
