"""Complete Ratio API on a common nonoverflowing domain for all registered types."""
# Object IDs follow constructor and object-returning calls in the differential protocol.
count = 0

def new(n, d=None):
    global count
    i = count
    count += 1
    print(f"new Ratio.init_T {n}" if d is None else f"new Ratio.init_T_T {n} {d}")
    return i

def obj_call(command):
    global count
    i = count
    count += 1
    print(command)
    return i

a, b = new(3, 2), new(1, 2)
new(2)
new(0, 5)
for op in ('add', 'sub', 'mul', 'div'):
    obj_call(f"call op_{op}_Ratio_Ratio {a} {b}")
    obj_call(f"call op_{op}_Ratio_T {a} 1")
    obj_call(f"call op_{op}_T_Ratio 1 {b}")
    r = new(3, 2)
    obj_call(f"do Ratio.op_{op}_assign {r} {b}")
    print(f"do Ratio.op_cmp {r} {a}")
    print(f"do Ratio.op_eq {r} {a}")
r = new(3, 2)
obj_call(f"do Ratio.op_div_assign {r} {r}")
for op, tag in [('inc_0', ''), ('inc_int', ' 0'), ('dec_0', ''), ('dec_int', ' 0')]:
    obj_call(f"do Ratio.op_{op} {r}{tag}")
obj_call(f"do Ratio.op_add {a}")
z = new(0, 1)
obj_call(f"do Ratio.op_sub {z}")
for tokens in [[], ['2'], ['2', '4'], ['x'], ['2', 'x'], ['0', '0'], ['-1', '2']]:
    r = new(7, 3)
    print(' '.join(['call op_shr_istream_Ratio', str(len(tokens)), *tokens, str(r)]))
    print(f"call op_shl_ostream_Ratio {r}")
