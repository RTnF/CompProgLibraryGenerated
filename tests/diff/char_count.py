"""Differential test commands for char_count (verifier/diff_harness.py). A string is its length and its char values."""
import random

rng = random.Random(20261123)
lines = ["call char_count 0", "call char_count 1 -128", "call char_count 4 0 0 -1 0", "call char_count 3 127 127 127"]
for _ in range(300):
    n = rng.randint(0, 30)
    xs = [rng.choice([97, 98, 99, -128, 0, 127]) if rng.random() < 0.2 else rng.randint(97, 99) for _ in range(n)]
    lines.append("call char_count " + " ".join(map(str, [n, *xs])))
print("\n".join(lines))
