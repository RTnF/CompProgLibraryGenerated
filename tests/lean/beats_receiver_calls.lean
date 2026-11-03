namespace BeatsReceiverCallsExamples
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppNestedEval
open Proofs.CppNestedVectorStore Proofs.CppVector
open Proofs.BeatsReceiverCalls Proofs.BeatsPrepare Proofs.BeatsInstance
open Proofs.IntSim Proofs.DoublingNested
open BeatsConstructCallExamples

def queryArgs (qa qb : Nat) : List NArgument :=
  vargs (fun i => aliasCaller.slots.length+i) 0 15 ++
    [.value (infExpr aliasCaller.slots.length),.value (sizeExpr aliasCaller.slots.length),
      .value (.literal i32 qa),.value (.literal i32 qb)]
def updateArgs (qa qb : Nat) (x : Int) : List NArgument := queryArgs qa qb ++ [.value (.literal s64 x)]

def query (program : NProgram) (state : NState) (qa qb : Nat) : Option (NState × Int) :=
  match program.callFuel 1024 state (queryArgs qa qb) with
  | .finished (out,.scalar value) => some (out,value)
  | _ => none

def update (program : NProgram) (state : NState) (qa qb : Nat) (x : Int) : Option NState :=
  match program.callFuel 1024 state (updateArgs qa qb x) with
  | .finished (out,.unit) => some out
  | _ => none

-- One object, followed by all six actual generated methods. Every later call
-- reads INF/n from the fields and consumes the state returned by the last call.
def trace : Option (List Int × Bool) := do
  let (initial,_) ← match closed aliasCaller with | .finished result => some result | _ => none
  let (s,a) ← query SegmentTreeBeats_calc_max initial 1 3
  let (s,b) ← query SegmentTreeBeats_calc_min s 1 3
  let s ← update SegmentTreeBeats_chmin s 0 3 5
  let (s,c) ← query SegmentTreeBeats_calc_max s 0 3
  let s ← update SegmentTreeBeats_chmax s 0 2 6
  let (s,d) ← query SegmentTreeBeats_calc_min s 0 3
  let s ← update SegmentTreeBeats_add_val s 1 3 2
  let (s,e) ← query SegmentTreeBeats_calc_max s 0 3
  let s ← update SegmentTreeBeats_update_val s 0 2 3
  let (s,f) ← query SegmentTreeBeats_calc_min s 0 3
  let (s,g) ← query SegmentTreeBeats_calc_max s 0 3
  some ([a,b,c,d,e,f,g],s.scope == initial.scope && s.slots == initial.slots &&
    s.scalars.memory == initial.scalars.memory && s.scalars.bindings == initial.scalars.bindings &&
    s.frame.bindings == initial.frame.bindings && s.frame.state.storage.lookup 2 == initial.frame.state.storage.lookup 2 &&
    s.frame.state.wellFormed && (sizeExpr aliasCaller.slots.length).denote (envOf s) == some 3)
#guard trace == some ([6,5,5,5,8,3,7],true)

-- An actual write to the scalar changes the expression result. This detects
-- accidentally replacing field reads with their constructor-time constants.
def changedSize : Option Int := do
  let (state,_) ← match closed aliasCaller with | .finished result => some result | _ => none
  let step ← (NStmt.assign (aliasCaller.slots.length+16) i32 (.literal i32 2)).run state
  (sizeExpr aliasCaller.slots.length).denote (envOf step.state)
#guard changedSize == some 2

end BeatsReceiverCallsExamples
