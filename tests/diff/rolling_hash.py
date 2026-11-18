"""Command cases for the rolling hash C++/Lean comparison."""

cases = []
queries = [[], [1], [-1], [0, 1], [-128, 0], [126], [-128, 0, 1, -1, -128, 0, 126]]
for cls in ("MultiRollingHash", "SimpleRollingHash"):
    extra = " 3" if cls == "MultiRollingHash" else ""
    constructor = "init_string_int" if cls == "MultiRollingHash" else "init_string"
    for k, original in enumerate(([1, -1, 0, 1, -1, -128, 0, 126], [])):
        source = " ".join(map(str, [len(original), *original]))
        cases.append(f"new {cls}.{constructor} {source}{extra}")
        for query in queries:
            tokens = " ".join(map(str, [len(query), *query]))
            valid = list(range(max(0, len(original) - len(query) + 1)))[::-1]
            indices = " ".join(map(str, [len(valid), *valid]))
            for name in ("match__string", "starts_with_string", "ends_with_string"):
                cases.append(f"do {cls}.{name} {k} {tokens}")
            cases.append(f"do {cls}.match_custom_string_vec {k} {tokens} {indices}")
    # The trailing invalid index is after a guaranteed repeated one-symbol match.
    cases.append(f"do {cls}.match_custom_string_vec 0 1 -1 2 4 -1")
cases += [
    "new RollingHash.init 6 1 2 3 1 2 3",
    "do RollingHash.hash_int_int 0 0 3",
    "do RollingHash.hash_int_int 0 3 6",
    "do RollingHash.hash_int 0 3",
    "call rh_in.mul 131 199",
    "call rh_in.mod 18446744073709551615",
]

for strength in (0, 1, 16):
    k = 2 + (0 if strength == 0 else 1 if strength == 1 else 2)
    cases.append(f"new MultiRollingHash.init_vec_int 7 -2147483648 -1 0 1 2147483647 -1 0 {strength}")
    cases.append(f"do MultiRollingHash.hash_int_int {k} 1 5")
    cases.append(f"do MultiRollingHash.hash_int {k} 4")
    cases.append(f"do MultiRollingHash.match__vec {k} 2 -1 0")
    cases.append(f"do MultiRollingHash.match_custom_vec_vec {k} 2 -1 0 3 5 1 -1")
cases += [
    "new SimpleRollingHash.init_vec 5 -2147483648 -1 0 1 2147483647",
    "do SimpleRollingHash.hash_int_int 2 1 5",
    "do SimpleRollingHash.hash_int 2 5",
    "do SimpleRollingHash.match__vec 2 2 -1 0",
    "do SimpleRollingHash.starts_with_vec 2 2 -2147483648 -1",
    "do SimpleRollingHash.ends_with_vec 2 2 1 2147483647",
]
print("\n".join(cases))
