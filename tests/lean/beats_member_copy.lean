namespace GeneratedBeatsMemberCopyExamples
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop
abbrev i32 : Ty := ⟨32,true,false⟩
abbrev i64 : Ty := ⟨64,true,false⟩
abbrev Object := Proofs.CppConstructorMultiFinish.ObjectRef

def caller : NState := ⟨⟨[],[],0,0,0⟩,
  ⟨⟨⟨[some ⟨.integer i64,none,some 0,[]⟩]⟩,
      {objects := [some ⟨0,[.integer 4,.integer 6,.integer 5],3,
        Proofs.CppVectorBindings.sizeLimit i64,0⟩],work := 0,peak := 4,baseSpace := 0}⟩,
    [false],[⟨0,.integer i64,false,.root 0⟩]⟩,[.vector 0],0,4⟩

def query (state : NState) (object : Object) : Option (NState × Int) :=
  match BeatsMemberBundle.Calls.SegmentTreeBeats_calc_max_callFuel 1024 state object false
      [.value (.literal i32 0),.value (.literal i32 3)] with
  | .finished (out,.scalar value) => some (out,value)
  | _ => none

def update (state : NState) (object : Object) : Option NState :=
  match BeatsMemberBundle.Calls.SegmentTreeBeats_chmin_callFuel 1024 state object false
      [.value (.literal i32 0),.value (.literal i32 3),.value (.literal i64 5)] with
  | .finished (out,.unit) => some out
  | _ => none

-- All fifteen vectors and the scalar fields are copied through actual source
-- descriptors, and a subsequent update must leave the original object intact.
def trace : Option (List Int × Bool) := do
  let (initial,original) ← match BeatsMemberBundle.Construction.SegmentTreeBeats_construct0_exportFuel
      1024 caller [.vectorReference 0] with
    | .finished result => some result | _ => none
  let (copied,object) ← match BeatsMemberBundle.Construction.copyFuel 64 initial original false with
    | .finished result => some result | _ => none
  let (first,a) ← query copied object
  let second ← update first object
  let (third,b) ← query second object
  let (last,c) ← query third original
  pure ([a,b,c],last.frame.state.wellFormed && last.scope == caller.scope &&
    original.vectorSlots != object.vectorSlots)

#guard caller.frame.state.wellFormed
#guard trace == some ([6,5,6],true)
end GeneratedBeatsMemberCopyExamples
