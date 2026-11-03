namespace ConstructorRootsExamples
open Proofs.CppScalar Proofs.CppVectorOwnership Proofs.CppVector Proofs.CppVectorStore
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppRootModel
open Proofs.CppConstructorRoots Proofs.DynamicTransfer Proofs.DynamicRetire

abbrev i32 : Ty := ⟨32,true,false⟩
def flatBuffer (owner : Nat) : Buffer Value := ⟨owner,[.integer owner],1,64,7⟩
def tags : List (Option Tag) := ((List.range 16).map fun j =>
  some ⟨.integer i32,none,some (if j = 0 then 2 else 3),[]⟩) ++
  [some ⟨.vector (.integer i32),none,some 3,[17]⟩,
   some ⟨.integer i32,some 16,none,[]⟩,
   some ⟨.integer i32,none,some 3,[]⟩,
   some ⟨.integer i32,none,some 8,[]⟩]
def buffers : List (Option (Buffer Value)) := ((List.range 16).map fun j => some (flatBuffer j)) ++
  [some ⟨16,[.child 17],1,64,11⟩,some ⟨17,[.integer 42],1,64,9⟩,
   some (flatBuffer 18),some (flatBuffer 19)]
def frame : Frame := ⟨⟨⟨tags⟩,{objects := buffers,work := 13,baseSpace := 5,peak := 100}⟩,
  (List.range 20).map (fun j => j % 2 == 0),
  [⟨0,.integer i32,false,.root 2⟩,⟨16,.vector (.integer i32),true,.root 3⟩]⟩
def nested : View := .rows i32 3 [17] 11 [[42]]
def roots : List Root := [(1,.flat i32 3 [1]),(16,nested)]
def fifteen : List Root := (List.range 15).map fun j => (j+1,.flat i32 3 [Int.ofNat (j+1)])
def result := retiredFrame (movedAll frame roots 2) 3

#guard frame.state.wellFormed
#guard transferAll frame (specs roots) 3 2 == some (movedAll frame roots 2)
#guard finishRoots frame (specs roots) 3 2 == some result
#guard result.state.forest.context 1 == some 2
#guard result.state.forest.context 16 == some 2
#guard result.state.forest.context 17 == some 2
#guard result.state.storage.lookup 17 == frame.state.storage.lookup 17
#guard result.state.storage.lookup 18 == none
#guard result.state.forest.lookup 18 == none
#guard result.state.storage.lookup 0 == frame.state.storage.lookup 0
#guard result.state.storage.lookup 19 == frame.state.storage.lookup 19
#guard result.rootWritable == frame.rootWritable
#guard result.bindings == frame.bindings
#guard (movedAll frame roots 2).state.storage == frame.state.storage
#guard result.state.wellFormed
#guard finishRoots frame [(1,.integer i32),(1,.integer i32)] 3 2 == none
#guard transferAll frame (specs roots) 2 1 == none
#guard transferAll frame [(17,.integer i32)] 3 2 == none
#guard transferAll frame [(1,.integer ⟨64,true,false⟩)] 3 2 == none
#guard finishRoots frame [] 3 2 == some (retiredFrame frame 3)
#guard (retiredFrame frame 3).state.storage.lookup 1 == none
-- In the fifteen-field case, all selected payloads survive the one retirement.
def many := (finishRoots frame (specs fifteen) 3 2).getD frame
#guard (List.range 15).all (fun j => many.state.forest.context (j+1) == some 2 &&
  many.state.storage.lookup (j+1) == frame.state.storage.lookup (j+1))
#guard many.state.storage.lookup 16 == none
#guard many.state.storage.lookup 17 == none
#guard many.state.wellFormed

theorem flatModel : Models frame.state 1 (.flat i32 3 [1]) :=
  ⟨by decide +kernel,by decide +kernel,flatBuffer 1,by decide +kernel,rfl⟩
theorem nestedModel : Models frame.state 16 nested := by
  refine ⟨⟨by decide +kernel,by decide +kernel,⟨16,[.child 17],1,64,11⟩,
    by decide +kernel,rfl,rfl⟩,rfl,?_⟩
  intro k owner lookup
  cases k with
  | zero =>
    have same : owner = 17 := by simpa using lookup.symm
    subst owner
    exact ⟨⟨17,[.integer 42],1,64,9⟩,by decide +kernel,rfl⟩
  | succ k => simp at lookup

theorem models : HaveModels frame roots 3 := by
  intro root member
  simp only [roots,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with same | same
  · subst root; exact ⟨flatModel,rfl⟩
  · subst root; exact ⟨nestedModel,rfl⟩

example : finishRoots frame (specs roots) 3 2 = some result ∧
    (∀ root ∈ roots, Models result.state root.1 (inScope root.2 2)) ∧
    (∀ owner view, Models frame.state owner view → owner ∉ roots.map Prod.fst →
      view.scope ≠ 3 → Models result.state owner view) :=
  finishRoots_ok frame roots 3 2 (by decide +kernel) (by decide) (by decide) models

-- Arbitrary owner IDs, element types, vector counts, scopes and payloads.
example (f : Frame) (members : List Root) (sc : Nat)
    (valid : f.state.wellFormed = true) (distinct : (members.map Prod.fst).Nodup)
    (models : HaveModels f members (sc+1)) :
    finishRoots f (specs members) (sc+1) sc = some (retiredFrame (movedAll f members sc) (sc+1)) :=
  (finishRoots_ok f members (sc+1) sc valid (by omega) distinct models).1

end ConstructorRootsExamples
