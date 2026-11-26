import random

random_keys = random.Random(20261126)
values = set()
print("new TreeSet.init")
for _ in range(400):
    key = random_keys.randrange(-16, 17)
    if random_keys.getrandbits(1):
        print(f"do TreeSet.add 0 {key}")
        values.add(key)
    else:
        print(f"do TreeSet.remove 0 {key}")
        values.discard(key)
    print(f"do TreeSet.find 0 {key}")
    print("do TreeSet.size_ 0")
    if values:
        print("do TreeSet.min_ 0")
        print("do TreeSet.max_ 0")
