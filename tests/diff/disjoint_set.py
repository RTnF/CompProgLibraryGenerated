"""Differential commands for the generated DisjointSet model."""

import random


print("new DisjointSet.init 0")
print("do DisjointSet.getNum 0")
print("new DisjointSet.init 16")
for width in (1, 2, 4, 8):
    for a in range(0, 16, 2 * width):
        print(f"do DisjointSet.unite 1 {a} {a + width}")
print("do DisjointSet.root 1 15")
print("do DisjointSet.size_ 1 15")
print("do DisjointSet.same 1 0 15")
print("do DisjointSet.unite 1 15 0")
print("do DisjointSet.getNum 1")

rng = random.Random(104)
sizes = (1, 2, 31, 64)
for n in sizes:
    print(f"new DisjointSet.init {n}")
for _ in range(600):
    index = rng.randrange(len(sizes))
    n = sizes[index]
    method = rng.choice(("unite", "same", "root", "size_"))
    keys = [rng.randrange(n) for _ in range(2 if method in ("unite", "same") else 1)]
    print(f"do DisjointSet.{method}", index + 2, *keys)
    print(f"do DisjointSet.getNum {index + 2}")
