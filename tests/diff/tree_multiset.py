import random


def cases():
    yield "new TreeMultiSet.init"
    yield "new TreeMultiSet.init"
    rng = random.Random(277)
    live = [{}, {}]
    for _ in range(360):
        index = rng.randrange(len(live))
        counts = live[index]
        key, count, method = rng.randrange(-12, 13), rng.randrange(7), rng.randrange(4)
        old = counts.get(key, 0)
        if method < 2:
            yield f"do TreeMultiSet.add {index} {key} {count}"
            if count:
                counts[key] = old + count
        elif method == 2:
            yield f"do TreeMultiSet.remove {index} {key} {count}"
            if old == count:
                counts.pop(key, None)
            elif old > count:
                counts[key] = old - count
        else:
            yield f"do TreeMultiSet.remove_all {index} {key}"
            counts.pop(key, None)

        for name in ("count", "find_lower", "find_upper", "rank"):
            yield f"do TreeMultiSet.{name} {index} {key}"
        for name in ("size_", "enumerate_all", "verify"):
            yield f"do TreeMultiSet.{name} {index}"
        yield f"do TreeMultiSet.enumerate {index} {key - 3} {key + 4}"
        yield f"do TreeMultiSet.aoj_dump {index} {key - 3} {key + 4}"
        if counts:
            yield f"do TreeMultiSet.min_ {index}"
            yield f"do TreeMultiSet.max_ {index}"
            yield f"do TreeMultiSet.get_kth {index} {rng.randrange(sum(counts.values()))}"

    yield "new TreeMultiSet.init"
    yield "do TreeMultiSet.add 2 -2147483648 2"
    yield "do TreeMultiSet.add 2 2147483647 5"
    yield "do TreeMultiSet.add 2 5 3"
    yield "do TreeMultiSet.remove_all 2 5"
    yield "new TreeMultiSet.init_copy 2"
    yield "do TreeMultiSet.remove 3 -2147483648 2"
    yield "do TreeMultiSet.add 3 17 3"
    yield "do TreeMultiSet.enumerate_all 2"
    yield "new TreeMultiSet.init_move 3"
    for index in (2, 3, 4):
        yield f"do TreeMultiSet.enumerate_all {index}"
        yield f"do TreeMultiSet.enumerate {index} 2147483647 -2147483648"
        yield f"do TreeMultiSet.aoj_dump {index} 2147483647 2147483647"
        yield f"do TreeMultiSet.verify {index}"
    yield "do TreeMultiSet.add 3 8 2"
    yield "do TreeMultiSet.count 4 8"
    yield "new TreeMultiSet.init"
    yield "new TreeMultiSet.init_copy 5"
    yield "new TreeMultiSet.init_move 5"
    yield "do TreeMultiSet.size_ 5"
    yield "do TreeMultiSet.size_ 6"
    yield "do TreeMultiSet.size_ 7"


print("\n".join(cases()))
