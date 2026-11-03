import Proofs.CppVectorCopy
import Proofs.CppNestedConstruct

namespace Proofs.CppNestedCopy
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedConstruct Proofs.CppVectorCopy

-- Copy a scalar vector, which may itself be a child, into a new root.
-- Nested parent headers contribute differently to liveSpace than flat Store.
def cloned (s : State) (source : Buffer Value) (ty : Ty) (scope : Nat) : State :=
  ⟨s.forest.declareRoot ty scope,
    {s.storage with
      objects := s.storage.objects ++ [some (copied source s.storage.objects.length)],
      work := s.storage.work+source.items.length+1,
      peak := max s.storage.peak (s.liveSpace+source.items.length+2-s.storage.baseSpace)}⟩

def copyRoot (s : State) (owner : Nat) (ty : Ty) (scope : Nat) : Option State := do
  if s.wellFormed = true ∧ CppVectorBindings.supported ty then
    let tag ← s.forest.lookup owner
    let source ← s.storage.lookup owner
    if tag.element = .integer ty then some (cloned s source ty scope) else none
  else none

theorem clone_storage_old (s : State) (source : Buffer Value) (ty : Ty) (scope owner : Nat)
    (old : owner < s.storage.objects.length) :
    (cloned s source ty scope).storage.lookup owner = s.storage.lookup owner := by
  simp [cloned,Store.lookup,List.getElem?_append_left old]

theorem clone_storage_new (s : State) (source : Buffer Value) (ty : Ty) (scope : Nat) :
    (cloned s source ty scope).storage.lookup s.storage.objects.length =
      some (copied source s.storage.objects.length) := by
  simp [cloned,Store.lookup]

theorem clone_wellFormed (s : State) (source : Buffer Value) (ty : Ty) (scope : Nat)
    (valid : s.wellFormed = true) (supported : CppVectorBindings.supported ty)
    (payload : source.Valid (accepts (.integer ty))) :
    (cloned s source ty scope).wellFormed = true := by
  obtain ⟨lengths,forest,checks⟩ := wellFormed_parts s valid
  have forestLength := declareRoot_length s.forest ty scope
  simp only [State.wellFormed,Bool.and_eq_true,decide_eq_true_eq]
  refine ⟨⟨?_,declareRoot_wellFormed s.forest ty scope forest supported⟩,?_⟩
  · simp only [cloned,List.length_append,List.length_singleton]
    omega
  · apply List.all_eq_true.mpr
    intro i member
    have inRange := List.mem_range.mp member
    simp only [cloned,List.length_append,List.length_singleton] at inRange
    by_cases old : i < s.storage.objects.length
    · have good := List.all_eq_true.mp checks i (List.mem_range.mpr old)
      have forestOld : i < s.forest.objects.length := by omega
      simpa [State.check,cloned,declareRoot_old s.forest ty scope i forestOld,
        Store.lookup,List.getElem?_append_left old] using good
    · have isNew : i = s.storage.objects.length := by omega
      subst i
      have rootLookup := declareRoot_new s.forest ty scope
      rw [lengths] at rootLookup
      simp only [State.check,cloned,rootLookup,Store.lookup,
        List.getElem?_append_right (Nat.le_refl _),Nat.sub_self,
        List.getElem?_cons_zero,Option.join_some]
      simp only [payloadOK,flatTag]
      apply decide_eq_true
      exact ⟨rfl,copied_valid source _ _ payload,trivial⟩

theorem copy_runs (s : State) (source : Buffer Value) (tag : Tag) (owner : Nat)
    (ty : Ty) (scope : Nat) (valid : s.wellFormed = true)
    (supported : CppVectorBindings.supported ty)
    (forest : s.forest.lookup owner = some tag)
    (storage : s.storage.lookup owner = some source) (typed : tag.element = .integer ty) :
    copyRoot s owner ty scope = some (cloned s source ty scope) := by
  simp [copyRoot,valid,supported,forest,storage,typed]

theorem copied_root_valid (s : State) (source : Buffer Value) (tag : Tag) (owner : Nat)
    (ty : Ty) (scope : Nat) (valid : s.wellFormed = true)
    (supported : CppVectorBindings.supported ty)
    (forest : s.forest.lookup owner = some tag)
    (storage : s.storage.lookup owner = some source) (typed : tag.element = .integer ty) :
    (cloned s source ty scope).wellFormed = true := by
  obtain ⟨actual,found,_,payload⟩ := wellFormed_buffer s owner source valid storage
  have same : actual = tag := Option.some.inj (found.symm.trans forest)
  subst actual
  have sourceValid : source.Valid (accepts (.integer ty)) := by
    simpa only [typed] using payload.1
  exact clone_wellFormed s source ty scope valid supported sourceValid

theorem clone_lengths (s : State) (source : Buffer Value) (ty : Ty) (scope : Nat) :
    (cloned s source ty scope).storage.objects.length = s.storage.objects.length+1 := by
  simp [cloned]

theorem clone_node_old (s : State) (source : Buffer Value) (ty : Ty) (scope owner : Nat)
    (lengths : s.forest.objects.length = s.storage.objects.length)
    (old : owner < s.storage.objects.length) :
    (cloned s source ty scope).nodeSpace owner = s.nodeSpace owner := by
  have forestOld : owner < s.forest.objects.length := by omega
  simp only [State.nodeSpace]
  rw [show (cloned s source ty scope).forest.lookup owner = s.forest.lookup owner from
    declareRoot_old s.forest ty scope owner forestOld, clone_storage_old s source ty scope owner old]

theorem clone_node_new (s : State) (source : Buffer Value) (ty : Ty) (scope : Nat)
    (lengths : s.forest.objects.length = s.storage.objects.length) :
    (cloned s source ty scope).nodeSpace s.storage.objects.length = source.items.length+1 := by
  have tag := declareRoot_new s.forest ty scope
  rw [lengths] at tag
  simp only [State.nodeSpace,show (cloned s source ty scope).forest.lookup s.storage.objects.length =
    some (flatTag ty scope) from tag,clone_storage_new]
  rfl

theorem clone_cost (s : State) (source : Buffer Value) (ty : Ty) (scope : Nat)
    (lengths : s.forest.objects.length = s.storage.objects.length) :
    (cloned s source ty scope).storage.work = s.storage.work+source.items.length+1 ∧
    (cloned s source ty scope).liveSpace = s.liveSpace+source.items.length+1 ∧
    (cloned s source ty scope).storage.peak =
      max s.storage.peak (s.liveSpace+source.items.length+2-s.storage.baseSpace) := by
  refine ⟨rfl,?_,rfl⟩
  have old : (List.range s.storage.objects.length).map (cloned s source ty scope).nodeSpace =
      (List.range s.storage.objects.length).map s.nodeSpace := by
    apply List.map_congr_left
    intro i inside
    exact clone_node_old s source ty scope i lengths (List.mem_range.mp inside)
  simp only [State.liveSpace,clone_lengths,List.range_succ,List.map_append,List.sum_append,
    List.map_singleton,List.sum_singleton]
  rw [old,clone_node_new s source ty scope lengths]
  omega

end Proofs.CppNestedCopy
