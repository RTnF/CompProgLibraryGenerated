namespace BeatsBindingCycleExamples
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppNestedVectorStore Proofs.BeatsBindingCycle
open BeatsSlotEvalExamples

def saved : Reference := ⟨0,i32,true,⟨0,0,1⟩⟩
#guard flat.frame.read saved == some 100
#guard (rebind flat.frame).read (reference saved) == some 100
-- Merely rotating the binding table invalidates this saved grant. Both
-- reference indices and vector slots must be transformed consistently.
#guard (rebind flat.frame).grant saved == none
#guard (rebind flat.frame).elementRef 15 i32 1 == some (reference saved)
#guard ((rebind flat.frame).write (reference saved) 444) == (flat.frame.write saved 444).map rebind
#guard ((rebind flat.frame).write (reference saved) 444).bind (fun f =>
  (f.state.storage.lookup 0).map (·.items)) == some [.integer 0,.integer 444]
#guard ((rebind flat.frame).write (reference saved) 444).bind (fun f =>
  (f.state.storage.lookup 1).map (·.items)) == some [.integer 1,.integer 101]

def readonlyRef : Reference := {saved with writable := false}
def stale : Reference := {saved with address := ⟨0,1,1⟩}
def wrongOwner : Reference := {saved with address := ⟨2,0,1⟩}
#guard (rebind flat.frame).read (reference readonlyRef) == some 100
#guard flat.frame.write readonlyRef 444 == none
#guard (rebind flat.frame).write (reference readonlyRef) 444 == none
#guard flat.frame.read stale == none
#guard (rebind flat.frame).read (reference stale) == none
#guard (rebind flat.frame).write (reference stale) 444 == none
#guard (rebind flat.frame).grant (reference wrongOwner) == none
#guard (rebind flat.frame).elementRef 15 i32 2 == none

def extra : Frame := {flat.frame with bindings := flat.frame.bindings++[⟨0,atom,true,.root 0⟩]}
#guard (rebind extra).resolve 16 atom == extra.resolve 16 atom
#guard (rebind flat.frame).addBinding ⟨0,atom,true,.root 0⟩ == (rebind extra,16)
#guard restore (rebind extra) == extra
#guard rebind (restore extra) == extra
#guard (view flat).vectorSlot 0 == some 15
#guard (view flat).scalarCell 16 i32 == flat.scalarCell 16 i32
#guard (view flat).work == flat.work
#guard view (flat.charge 7 3) == (view flat).charge 7 3
#guard (view (Proofs.BeatsSlotCycle.permute flat)).slots == flat.slots
#guard (view (Proofs.BeatsSlotCycle.permute flat)).frame.bindings.map (·.owner) == List.range' 1 15 ++ [0]

example (s : NState) (long : 16 ≤ s.frame.bindings.length) (i : Nat)
    (element : Proofs.CppVectorOwnership.Element) :
    ((view s).vectorSlot i).bind (fun index => (view s).frame.resolve index element) =
      (s.vectorSlot i).bind (fun index => s.frame.resolve index element) := vector_resolve s long i element

example (f : Frame) (long : 16 ≤ f.bindings.length) (r : Reference) (x : Int) :
    (rebind f).write (reference r) x = (f.write r x).map rebind := write f long r x

end BeatsBindingCycleExamples
