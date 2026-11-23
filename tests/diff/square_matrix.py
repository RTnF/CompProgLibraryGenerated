"""Differential test commands for SquareMatrix (verifier/diff_harness.py).

Objects come from O() and I() and the arithmetic operations; element writes go through the row reference, which the
command language does not express, so general matrices are covered by tests/square_matrix.cpp."""

lines = []
count = 0


def obj(command):
    """A command that appends one object; returns its number."""
    global count
    lines.append(command)
    count += 1
    return count - 1


o = obj("call SquareMatrix.O")
i = obj("call SquareMatrix.I")
two = obj(f"call op_add_SquareMatrix_SquareMatrix {i} {i}")
neg = obj(f"do SquareMatrix.op_sub {i}")
three = obj(f"call op_sub_SquareMatrix_SquareMatrix {two} {neg}")
six = obj(f"call op_mul_SquareMatrix_SquareMatrix {two} {three}")
mix = obj(f"call op_add_SquareMatrix_SquareMatrix {six} {neg}")
pos = obj(f"do SquareMatrix.op_add {mix}")
for k in (o, i, two, neg, three, six, mix, pos):
    lines.append(f"field SquareMatrix.mat {k}")
    for row in (0, 1):
        lines.append(f"do SquareMatrix.op_index_int_const {k} {row}")
for a in (o, i, two, six):
    for b in (o, i, two, six):
        lines.append(f"call op_eq_SquareMatrix_SquareMatrix {a} {b}")
        lines.append(f"call op_ne_SquareMatrix_SquareMatrix {a} {b}")
for e in (0, 1, 2, 3, 5, 10, 31):
    k = obj(f"do SquareMatrix.pow {three} {e}")
    lines.append(f"field SquareMatrix.mat {k}")
for k in (two, three, neg):
    lines.append(f"do SquareMatrix.op_mul_assign {k} {k}")
    lines.append(f"field SquareMatrix.mat {k}")
    lines.append(f"do SquareMatrix.op_add_assign {k} {i}")
    lines.append(f"do SquareMatrix.op_sub_assign {k} {two}")
    lines.append(f"field SquareMatrix.mat {k}")
print("\n".join(lines))
