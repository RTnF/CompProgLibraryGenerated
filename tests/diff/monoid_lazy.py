"""Differential commands for the nested monoid records and the flat API."""

print("""new RangeSum.init_T_int 7 -3
new RangeSum.init_T_int -5 11
new RangeSum.init_0
new RangeSum.init_0
new RangeAdd.init_T 7
new RangeAdd.init_T -5
new RangeAdd.init_0
new RangeAdd.init_0
new RangeSet.init_T 7
new RangeSet.init_T -5
new RangeSet.init_T_bool 7 0
new RangeSet.init_T_bool -5 1
new RangeSet.init_0
new RangeSet.init_0
new RangeAddRangeMaxMin_RangeMax.init_T 7
new RangeAddRangeMaxMin_RangeMax.init_T -5
new RangeAddRangeMaxMin_RangeMax.init_0
new RangeAddRangeMaxMin_RangeMax.init_0
new RangeAddRangeMaxMin_RangeMin.init_T 7
new RangeAddRangeMaxMin_RangeMin.init_T -5
new RangeAddRangeMaxMin_RangeMin.init_0
new RangeAddRangeMaxMin_RangeMin.init_0
new RangeAddRangeMaxMin_RangeAdd.init 7
new RangeAddRangeMaxMin_RangeAdd.init -5
new RangeAddRangeSum_RangeSum.init_T_int 7 -3
new RangeAddRangeSum_RangeSum.init_T_int -5 11
new RangeAddRangeSum_RangeSum.init_0
new RangeAddRangeSum_RangeSum.init_0
new RangeAddRangeSum_RangeAdd.init 7
new RangeAddRangeSum_RangeAdd.init -5
new RangeSetRangeMaxMin_RangeMax.init_T 7
new RangeSetRangeMaxMin_RangeMax.init_T -5
new RangeSetRangeMaxMin_RangeMax.init_0
new RangeSetRangeMaxMin_RangeMax.init_0
new RangeSetRangeMaxMin_RangeMin.init_T 7
new RangeSetRangeMaxMin_RangeMin.init_T -5
new RangeSetRangeMaxMin_RangeMin.init_0
new RangeSetRangeMaxMin_RangeMin.init_0
new RangeSetRangeMaxMin_RangeSet.init_T 7
new RangeSetRangeMaxMin_RangeSet.init_T -5
new RangeSetRangeMaxMin_RangeSet.init_0
new RangeSetRangeMaxMin_RangeSet.init_0
new RangeSetRangeSum_RangeSum.init_T_int 7 -3
new RangeSetRangeSum_RangeSum.init_T_int -5 11
new RangeSetRangeSum_RangeSum.init_0
new RangeSetRangeSum_RangeSum.init_0
new RangeSetRangeSum_RangeSet.init_T 7
new RangeSetRangeSum_RangeSet.init_T -5
new RangeSetRangeSum_RangeSet.init_0
new RangeSetRangeSum_RangeSet.init_0
call op_RangeSum_RangeSum 0 1
do RangeAdd.applyExtremum 0 7
do RangeAdd.applyExtremum 1 7
do RangeAdd.applySumX 0 7 11
do RangeAdd.applySumX 1 7 11
call compose_RangeAdd_RangeAdd 0 1
do RangeSet.applyExtremum 0 7
do RangeSet.applyExtremum 1 7
do RangeSet.applySumX 0 7 11
do RangeSet.applySumX 1 7 11
call compose_RangeSet_RangeSet 0 1
call op_RangeAddRangeMaxMin_RangeMax_RangeAddRangeMaxMin_RangeMax 0 1
call op_RangeAddRangeMaxMin_RangeMin_RangeAddRangeMaxMin_RangeMin 0 1
call compose_RangeAddRangeMaxMin_RangeAdd_RangeAddRangeMaxMin_RangeAdd 0 1
call op_RangeAddRangeSum_RangeSum_RangeAddRangeSum_RangeSum 0 1
call compose_RangeAddRangeSum_RangeAdd_RangeAddRangeSum_RangeAdd 0 1
call op_RangeSetRangeMaxMin_RangeMax_RangeSetRangeMaxMin_RangeMax 0 1
call op_RangeSetRangeMaxMin_RangeMin_RangeSetRangeMaxMin_RangeMin 0 1
call compose_RangeSetRangeMaxMin_RangeSet_RangeSetRangeMaxMin_RangeSet 0 1
call op_RangeSetRangeSum_RangeSum_RangeSetRangeSum_RangeSum 0 1
call compose_RangeSetRangeSum_RangeSet_RangeSetRangeSum_RangeSet 0 1
field RangeSum.size 0
field RangeSum.size 1
field RangeSum.x 0
field RangeSum.x 1
field RangeAdd.v 0
field RangeAdd.v 1
field RangeSet.noop 0
field RangeSet.noop 1
field RangeSet.v 0
field RangeSet.v 1
field RangeAddRangeMaxMin_RangeMax.x 0
field RangeAddRangeMaxMin_RangeMax.x 1
field RangeAddRangeMaxMin_RangeMin.x 0
field RangeAddRangeMaxMin_RangeMin.x 1
field RangeAddRangeMaxMin_RangeAdd.v 0
field RangeAddRangeMaxMin_RangeAdd.v 1
field RangeAddRangeSum_RangeSum.size 0
field RangeAddRangeSum_RangeSum.size 1
field RangeAddRangeSum_RangeSum.x 0
field RangeAddRangeSum_RangeSum.x 1
field RangeAddRangeSum_RangeAdd.v 0
field RangeAddRangeSum_RangeAdd.v 1
field RangeSetRangeMaxMin_RangeMax.x 0
field RangeSetRangeMaxMin_RangeMax.x 1
field RangeSetRangeMaxMin_RangeMin.x 0
field RangeSetRangeMaxMin_RangeMin.x 1
field RangeSetRangeMaxMin_RangeSet.noop 0
field RangeSetRangeMaxMin_RangeSet.noop 1
field RangeSetRangeMaxMin_RangeSet.v 0
field RangeSetRangeMaxMin_RangeSet.v 1
field RangeSetRangeSum_RangeSum.size 0
field RangeSetRangeSum_RangeSum.size 1
field RangeSetRangeSum_RangeSum.x 0
field RangeSetRangeSum_RangeSum.x 1
field RangeSetRangeSum_RangeSet.noop 0
field RangeSetRangeSum_RangeSet.noop 1
field RangeSetRangeSum_RangeSet.v 0
field RangeSetRangeSum_RangeSet.v 1""")
