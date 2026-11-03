import Proofs.CppNestedVectorBindings
import Proofs.CppVectorStoreGrowth

namespace Proofs.CppNestedGrowth
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings

-- Only integer payloads may be appended here. Adding a child vector also
-- changes the ownership forest and needs a separate construction operation.
def _root_.Proofs.CppNestedVectorBindings.Frame.appendGrowing (f : Frame)
    (slot : Nat) (ty : Ty) (value : Int) : Option Frame := do
  let (binding,buffer) ← f.resolve slot (.integer ty)
  let result ← CppVectorGrowth.append buffer (accepts (.integer ty)) binding.writable (.integer value)
  f.commit binding.owner (.integer ty) result

theorem append_readonly (f : Frame) (slot : Nat) (ty : Ty) (value : Int)
    (binding : Binding) (buffer : Buffer Value)
    (resolved : f.resolve slot (.integer ty) = some (binding,buffer))
    (readonly : binding.writable = false) : f.appendGrowing slot ty value = none := by
  simp [Frame.appendGrowing, resolved, readonly, CppVectorGrowth.append_readonly]

theorem append_reserved (f : Frame) (slot : Nat) (ty : Ty) (value : Int)
    (binding : Binding) (buffer : Buffer Value) (r : Result Value Unit)
    (resolved : f.resolve slot (.integer ty) = some (binding,buffer))
    (run : CppVector.appendReserved buffer (accepts (.integer ty)) binding.writable (.integer value) = some r) :
    f.appendGrowing slot ty value = f.commit binding.owner (.integer ty) r := by
  have grown := CppVectorGrowth.append_reserved_success _ _ _ _ _ run
  simp [Frame.appendGrowing, resolved, grown]

theorem append_ok (f : Frame) (slot : Nat) (ty : Ty) (value : Int)
    (binding : Binding) (buffer : Buffer Value) (tag : Tag)
    (resolved : f.resolve slot (.integer ty) = some (binding,buffer))
    (writable : binding.writable = true) (valid : f.state.wellFormed = true)
    (object : f.object binding.owner (.integer ty) = some (buffer,tag))
    (tagFound : f.state.forest.lookup binding.owner = some tag)
    (found : f.state.storage.lookup binding.owner = some buffer)
    (type : tag.element = .integer ty) (owns : buffer.owner = binding.owner)
    (bv : buffer.Valid (accepts (.integer ty)))
    (accepted : ty.valid value = true) (room : buffer.items.length < buffer.limit) :
    ∃ r, f.appendGrowing slot ty value = some (f.updated binding.owner buffer r) ∧
      (f.updated binding.owner buffer r).state.wellFormed = true ∧
      r.buffer.items = buffer.items ++ [.integer value] ∧
      r.buffer.owner = binding.owner ∧ r.buffer.limit = buffer.limit ∧
      r.work + CppVectorGrowth.potential r.buffer ≤ CppVectorGrowth.potential buffer + 5 ∧
      r.peak ≤ 3 * buffer.capacity + 3 ∧
      (if buffer.items.length < buffer.capacity then r.buffer.epoch = buffer.epoch
       else r.buffer.epoch = buffer.epoch + 1) := by
  obtain ⟨r, run, rv, ri, ro, rl, amort, peak, epoch⟩ :=
    CppVectorGrowth.append_spec buffer (accepts (.integer ty)) (.integer value) bv accepted room
  have same : r.buffer.owner = binding.owner := ro.trans owns
  have payload : payloadOK tag r.buffer := by simp [payloadOK, type, rv]
  have peaks := CppVectorStoreGrowth.append_peak buffer (accepts (.integer ty)) (.integer value) r run
  have commit := commit_runs f binding.owner (.integer ty) buffer tag r valid object tagFound found
    same payload peaks.1 peaks.2
  refine ⟨r, ?_, commit_success_valid f _ _ _ _ commit, ri, same, rl, amort, peak, epoch⟩
  simp [Frame.appendGrowing, resolved, writable, run, commit]

-- This accounting uses the nested forest: child headers are already inside
-- their parent's capacity, so they must not be counted once more here.
theorem updated_node_other (f : Frame) (owner other : Nat) (old : Buffer Value)
    (r : Result Value Unit) (different : owner ≠ other) :
    (f.updated owner old r).state.nodeSpace other = f.state.nodeSpace other := by
  simp [State.nodeSpace, Frame.updated, Store.lookup, List.getElem?_set_ne different]

theorem sum_range_replace (before after : Nat → Nat) (owner n old new : Nat)
    (inside : owner < n) (same : after owner + old = before owner + new)
    (other : ∀ i, owner ≠ i → after i = before i) :
    ((List.range n).map after).sum + old = ((List.range n).map before).sum + new := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases last : owner = n
    · subst owner
      have equal : (List.range n).map after = (List.range n).map before := by
        apply List.map_congr_left
        intro i hi
        apply other i
        have := List.mem_range.mp hi
        omega
      rw [equal]
      omega
    · have recursion := ih (by omega)
      have atLast := other n last
      omega

theorem updated_space (f : Frame) (owner : Nat) (old : Buffer Value) (tag : Tag)
    (r : Result Value Unit) (found : f.state.storage.lookup owner = some old)
    (tagFound : f.state.forest.lookup owner = some tag) :
    (f.updated owner old r).state.liveSpace + old.capacity = f.state.liveSpace + r.buffer.capacity := by
  have inside := lookup_bound f.state.storage owner old found
  have self : (f.updated owner old r).state.storage.lookup owner = some r.buffer := by
    simp [Frame.updated, Store.lookup, List.getElem?_set_self inside]
  have same : (f.updated owner old r).state.nodeSpace owner + old.capacity =
      f.state.nodeSpace owner + r.buffer.capacity := by
    have forest : (f.updated owner old r).state.forest = f.state.forest := rfl
    simp only [State.nodeSpace, forest, self, found, tagFound]
    omega
  have sums := sum_range_replace f.state.nodeSpace (f.updated owner old r).state.nodeSpace owner
    f.state.storage.objects.length old.capacity r.buffer.capacity inside same
    (fun i hi => updated_node_other f owner i old r hi)
  simpa [State.liveSpace, Frame.updated] using sums

theorem updated_peak (f : Frame) (owner : Nat) (old : Buffer Value) (tag : Tag)
    (r : Result Value Unit) (found : f.state.storage.lookup owner = some old)
    (tagFound : f.state.forest.lookup owner = some tag)
    (oldPeak : old.capacity + 1 ≤ r.peak) (newPeak : r.buffer.capacity + 1 ≤ r.peak) :
    (f.updated owner old r).state.liveSpace - f.state.storage.baseSpace ≤
      (f.updated owner old r).state.storage.peak := by
  have space := updated_space f owner old tag r found tagFound
  have live : old.capacity ≤ f.state.liveSpace := by
    have member : owner ∈ List.range f.state.storage.objects.length := List.mem_range.mpr
      (lookup_bound f.state.storage owner old found)
    have node : old.capacity ≤ f.state.nodeSpace owner := by
      simp [State.nodeSpace, found, tagFound]
    have sumBound : ∀ (xs : List Nat) (i : Nat), i ∈ xs →
        f.state.nodeSpace i ≤ (xs.map f.state.nodeSpace).sum := by
      intro xs
      induction xs with
      | nil => simp
      | cons a xs ih =>
        intro i hi
        simp only [List.mem_cons] at hi
        simp only [List.map_cons, List.sum_cons]
        rcases hi with equal | member
        · subst i; omega
        · have := ih i member; omega
    exact Nat.le_trans node (sumBound _ owner member)
  have peak := Nat.le_max_right f.state.storage.peak
    (f.state.liveSpace + (r.peak - (old.capacity + 1)) - f.state.storage.baseSpace)
  change _ ≤ max f.state.storage.peak
    (f.state.liveSpace + (r.peak - (old.capacity + 1)) - f.state.storage.baseSpace)
  omega

end Proofs.CppNestedGrowth
