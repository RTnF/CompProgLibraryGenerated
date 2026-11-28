import random

random_keys = random.Random(20261126)
values = [set(), set()]
print("new TreeSet.init")
print("do TreeSet.rank 0 0")
print("do TreeSet.find_lower 0 0")
print("do TreeSet.find_upper 0 0")
print("new TreeSet.init")

for step in range(360):
    index = step % len(values)
    present = values[index]
    key = random_keys.randrange(-60, 61)
    if random_keys.randrange(5) < 3:
        print(f"do TreeSet.add {index} {key}")
        present.add(key)
    else:
        print(f"do TreeSet.remove {index} {key}")
        present.discard(key)
    for operation in ("find", "rank", "find_lower", "find_upper"):
        print(f"do TreeSet.{operation} {index} {key}")
    print(f"do TreeSet.size_ {index}")
    if present:
        print(f"do TreeSet.get_kth {index} {random_keys.randrange(len(present))}")
        print(f"do TreeSet.min_ {index}")
        print(f"do TreeSet.max_ {index}")

for case in (
    "new TreeSet.init_copy 0",
    "do TreeSet.add 2 -200",
    "new TreeSet.init_move 2",
    "do TreeSet.size_ 2",
    "do TreeSet.rank 3 -200",
    "do TreeSet.op_assign_copy 2 3",
    "do TreeSet.rank 2 -200",
    "do TreeSet.op_assign_move 1 2",
    "do TreeSet.rank 1 -200",
    "do TreeSet.rank 2 -200",
    "do TreeSet.rank 3 -200",
):
    print(case)
