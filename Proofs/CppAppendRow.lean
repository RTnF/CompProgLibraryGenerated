import Proofs.CppForestAppend
import Proofs.CppNestedGrowth

namespace Proofs.CppAppendRow
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedConstruct
open Proofs.CppForestAppend

-- The new row has a fresh lifetime even when old slots contain tombstones.
-- Its header lives in the parent's capacity; its initially empty buffer
-- contributes zero additional capacity to the nested live-space sum.
def added (s : State) (parent : Nat) (tag : Tag) (ty : Ty) (old : Buffer Value)
    (r : Result Value Unit) : State :=
  ⟨s.forest.appendChild parent tag (.integer ty),
    {s.storage with
      objects := s.storage.objects.set parent (some r.buffer) ++ [some (rowBuffer ty s.storage.objects.length)],
      work := s.storage.work + r.work + 1,
      peak := max s.storage.peak (s.liveSpace + (r.peak - (old.capacity + 1)) - s.storage.baseSpace)}⟩

def _root_.Proofs.CppNestedVectorStore.State.appendRow (s : State) (parent : Nat) (ty : Ty) : Option State := do
  if s.wellFormed then
    let old ← s.storage.lookup parent
    let tag ← s.forest.lookup parent
    if tag.element = .vector (.integer ty) then
      let r ← CppVectorGrowth.append old (accepts tag.element) true (.child s.storage.objects.length)
      some (added s parent tag ty old r)
    else none
  else none

theorem storage_parent (s : State) (parent : Nat) (tag : Tag) (ty : Ty) (old : Buffer Value)
    (r : Result Value Unit) (inside : parent < s.storage.objects.length) :
    (added s parent tag ty old r).storage.lookup parent = some r.buffer := by
  simp only [added, Store.lookup]
  rw [List.getElem?_append_left (by simpa using inside), List.getElem?_set_self inside]
  rfl

theorem storage_old (s : State) (parent : Nat) (tag : Tag) (ty : Ty) (old : Buffer Value)
    (r : Result Value Unit) (i : Nat) (inside : i < s.storage.objects.length) (other : parent ≠ i) :
    (added s parent tag ty old r).storage.lookup i = s.storage.lookup i := by
  simp only [added, Store.lookup]
  rw [List.getElem?_append_left (by simpa using inside), List.getElem?_set_ne other]

theorem storage_fresh (s : State) (parent : Nat) (tag : Tag) (ty : Ty) (old : Buffer Value)
    (r : Result Value Unit) :
    (added s parent tag ty old r).storage.lookup s.storage.objects.length =
      some (rowBuffer ty s.storage.objects.length) := by
  simp [added, Store.lookup]

theorem added_wellFormed (s : State) (parent : Nat) (tag : Tag) (ty : Ty) (old : Buffer Value)
    (r : Result Value Unit) (valid : s.wellFormed = true)
    (found : s.storage.lookup parent = some old) (tagFound : s.forest.lookup parent = some tag)
    (type : tag.element = .vector (.integer ty))
    (run : CppVectorGrowth.append old (accepts tag.element) true (.child s.storage.objects.length) = some r) :
    (added s parent tag ty old r).wellFormed = true := by
  obtain ⟨lengths, forest, checks⟩ := wellFormed_parts s valid
  obtain ⟨t, ht, owns, payload⟩ := wellFormed_buffer s parent old valid found
  have equal : t = tag := Option.some.inj (ht.symm.trans tagFound)
  subst t
  have oldItems : old.items = tag.children.map Value.child := by simpa [type] using payload.2
  have bv : old.Valid (accepts tag.element) := payload.1
  have room : old.items.length < old.limit := by
    unfold CppVectorGrowth.append at run
    split at run
    · rename_i h; exact h.2.2.2
    · contradiction
  obtain ⟨next, hn, nv, ni, no, _, _, _, _⟩ :=
    CppVectorGrowth.append_spec old (accepts tag.element) (.child s.storage.objects.length)
      bv (by simp [type, accepts]) room
  have same : next = r := Option.some.inj (hn.symm.trans run)
  subst next
  have inside := CppVectorStore.lookup_bound s.storage parent old found
  simp only [State.wellFormed, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨?_, append_wellFormed s.forest parent tag (.integer ty) forest tagFound type⟩, ?_⟩
  · simp only [added, append_length, List.length_append, List.length_set,
      List.length_cons, List.length_nil]
    omega
  · apply List.all_eq_true.mpr
    intro i member
    have bound : i < s.storage.objects.length + 1 := by
      have := List.mem_range.mp member
      simpa [added] using this
    by_cases fresh : i = s.storage.objects.length
    · subst i
      have newTag := append_fresh s.forest parent tag (.integer ty)
      rw [lengths] at newTag
      unfold State.check
      rw [show (added s parent tag ty old r).forest.lookup s.storage.objects.length = _ from newTag,
        storage_fresh]
      simp [childTag, rowBuffer, payloadOK, Buffer.Valid]
    · have oldBound : i < s.storage.objects.length := by omega
      by_cases isParent : parent = i
      · subst i
        have parentTag := append_parent s.forest parent tag (.integer ty) (by omega)
        unfold State.check
        rw [show (added s parent tag ty old r).forest.lookup parent = _ from parentTag,
          storage_parent s parent tag ty old r inside]
        simp only [decide_eq_true_eq]
        refine ⟨no.trans owns, ?_⟩
        simp only [payloadOK, type]
        refine ⟨by simpa [type] using nv, ?_⟩
        simpa [oldItems, List.map_append, lengths] using ni
      · have good := List.all_eq_true.mp checks i (List.mem_range.mpr oldBound)
        have tags := append_old s.forest parent tag (.integer ty) i (by omega) isParent
        change (match (added s parent tag ty old r).forest.lookup i,
          (added s parent tag ty old r).storage.lookup i with
          | none, none => true
          | some tag, some buffer => decide (buffer.owner = i ∧ payloadOK tag buffer)
          | _, _ => false) = true
        rw [show (added s parent tag ty old r).forest.lookup i = _ from tags,
          storage_old s parent tag ty old r i oldBound isParent]
        exact good

theorem appendRow_runs (s : State) (parent : Nat) (tag : Tag) (ty : Ty) (old : Buffer Value)
    (valid : s.wellFormed = true) (found : s.storage.lookup parent = some old)
    (tagFound : s.forest.lookup parent = some tag) (type : tag.element = .vector (.integer ty))
    (room : old.items.length < old.limit) :
    ∃ r, s.appendRow parent ty = some (added s parent tag ty old r) ∧
      (added s parent tag ty old r).wellFormed = true ∧
      r.buffer.items = old.items ++ [.child s.storage.objects.length] ∧
      r.buffer.limit = old.limit ∧
      r.work + 1 + CppVectorGrowth.potential r.buffer ≤ CppVectorGrowth.potential old + 6 := by
  obtain ⟨t, ht, _, payload⟩ := wellFormed_buffer s parent old valid found
  have equal : t = tag := Option.some.inj (ht.symm.trans tagFound)
  subst t
  obtain ⟨r, run, _, items, _, limit, amort, _, _⟩ :=
    CppVectorGrowth.append_spec old (accepts tag.element) (.child s.storage.objects.length)
      payload.1 (by simp [accepts, type]) room
  refine ⟨r, ?_, added_wellFormed s parent tag ty old r valid found tagFound type run,
    items, limit, by omega⟩
  have runTyped := run
  rw [type] at runTyped
  simp [State.appendRow, valid, found, tagFound, type, runTyped]

theorem appendRow_inv (s next : State) (parent : Nat) (ty : Ty)
    (ran : s.appendRow parent ty = some next) :
    ∃ old tag r, s.wellFormed = true ∧ s.storage.lookup parent = some old ∧
      s.forest.lookup parent = some tag ∧ tag.element = .vector (.integer ty) ∧
      CppVectorGrowth.append old (accepts tag.element) true (.child s.storage.objects.length) = some r ∧
      next = added s parent tag ty old r := by
  unfold State.appendRow at ran
  split at ran
  · rename_i valid
    cases found : s.storage.lookup parent with
    | none => simp [found] at ran
    | some old =>
      cases tagFound : s.forest.lookup parent with
      | none => simp [found, tagFound] at ran
      | some tag =>
        simp only [found, tagFound, Bind.bind, Option.bind] at ran
        split at ran
        · rename_i type
          cases step : CppVectorGrowth.append old (accepts tag.element) true (.child s.storage.objects.length) with
          | none => simp [step] at ran
          | some r =>
            simp only [step, Option.some.injEq] at ran
            exact ⟨old, tag, r, valid, rfl, rfl, type, step, ran.symm⟩
        · contradiction
  · contradiction

theorem appendRow_valid (s next : State) (parent : Nat) (ty : Ty)
    (ran : s.appendRow parent ty = some next) : next.wellFormed = true := by
  obtain ⟨old, tag, r, valid, found, tagFound, type, run, rfl⟩ := appendRow_inv s next parent ty ran
  exact added_wellFormed s parent tag ty old r valid found tagFound type run

def _root_.Proofs.CppNestedVectorBindings.Frame.appendRow (f : Frame) (slot : Nat) (ty : Ty) : Option Frame := do
  let (binding,_) ← f.resolve slot (.vector (.integer ty))
  if binding.writable then
    let state ← f.state.appendRow binding.owner ty
    some {f with state := state, rootWritable := f.rootWritable ++ [false]}
  else none

theorem appendRow_readonly (f : Frame) (slot : Nat) (ty : Ty) (binding : Binding) (buffer : Buffer Value)
    (resolved : f.resolve slot (.vector (.integer ty)) = some (binding,buffer))
    (readonly : binding.writable = false) : f.appendRow slot ty = none := by
  simp [Frame.appendRow, resolved, readonly]

theorem frame_appendRow_runs (f : Frame) (slot : Nat) (ty : Ty) (binding : Binding)
    (buffer : Buffer Value) (next : State)
    (resolved : f.resolve slot (.vector (.integer ty)) = some (binding,buffer))
    (writable : binding.writable = true) (run : f.state.appendRow binding.owner ty = some next) :
    f.appendRow slot ty = some {f with state := next, rootWritable := f.rootWritable ++ [false]} := by
  simp [Frame.appendRow, resolved, writable, run]

theorem frame_appendRow_valid (f next : Frame) (slot : Nat) (ty : Ty)
    (ran : f.appendRow slot ty = some next) : next.state.wellFormed = true := by
  unfold Frame.appendRow at ran
  cases resolved : f.resolve slot (.vector (.integer ty)) with
  | none => simp [resolved] at ran
  | some pair =>
    obtain ⟨binding,buffer⟩ := pair
    simp only [resolved, Bind.bind, Option.bind] at ran
    split at ran
    · cases step : f.state.appendRow binding.owner ty with
      | none => simp [step] at ran
      | some state =>
        simp only [step, Option.some.injEq] at ran
        cases ran
        exact appendRow_valid f.state state binding.owner ty step
    · contradiction

-- A comparison state with just the parent buffer replaced. It need not be
-- well formed: its purpose is to reuse the proven nested space equation.
def bufferUpdated (s : State) (parent : Nat) (old : Buffer Value) (r : Result Value Unit) : State :=
  ((⟨s,[],[]⟩ : Frame).updated parent old r).state

theorem added_node_old (s : State) (parent : Nat) (tag : Tag) (ty : Ty) (old : Buffer Value)
    (r : Result Value Unit) (valid : s.wellFormed = true)
    (found : s.storage.lookup parent = some old) (tagFound : s.forest.lookup parent = some tag)
    (i : Nat) (inside : i < s.storage.objects.length) :
    (added s parent tag ty old r).nodeSpace i = (bufferUpdated s parent old r).nodeSpace i := by
  have lengths := (wellFormed_parts s valid).1
  have parentBound := CppVectorStore.lookup_bound s.storage parent old found
  have baseForest : (bufferUpdated s parent old r).forest = s.forest := rfl
  by_cases same : parent = i
  · subst i
    have tagNext := append_parent s.forest parent tag (.integer ty) (by omega)
    have tagAdded : (added s parent tag ty old r).forest.lookup parent = _ := tagNext
    have bufAdded := storage_parent s parent tag ty old r parentBound
    have bufBase : (bufferUpdated s parent old r).storage.lookup parent = some r.buffer := by
      simp [bufferUpdated, Frame.updated, Store.lookup, List.getElem?_set_self parentBound]
    simp only [State.nodeSpace, tagAdded, bufAdded, baseForest, tagFound, bufBase]
  · have tags := append_old s.forest parent tag (.integer ty) i (by omega) same
    have tagAdded : (added s parent tag ty old r).forest.lookup i = s.forest.lookup i := tags
    have bufAdded := storage_old s parent tag ty old r i inside same
    have bufBase : (bufferUpdated s parent old r).storage.lookup i = s.storage.lookup i := by
      simp [bufferUpdated, Frame.updated, Store.lookup, List.getElem?_set_ne same]
    simp only [State.nodeSpace, tagAdded, bufAdded, baseForest, bufBase]

theorem added_node_fresh (s : State) (parent : Nat) (tag : Tag) (ty : Ty) (old : Buffer Value)
    (r : Result Value Unit) (lengths : s.forest.objects.length = s.storage.objects.length) :
    (added s parent tag ty old r).nodeSpace s.storage.objects.length = 0 := by
  have ht := append_fresh s.forest parent tag (.integer ty)
  rw [lengths] at ht
  have tagAdded : (added s parent tag ty old r).forest.lookup s.storage.objects.length = _ := ht
  simp [State.nodeSpace, tagAdded, storage_fresh, childTag, rowBuffer]

theorem added_live (s : State) (parent : Nat) (tag : Tag) (ty : Ty) (old : Buffer Value)
    (r : Result Value Unit) (valid : s.wellFormed = true)
    (found : s.storage.lookup parent = some old) (tagFound : s.forest.lookup parent = some tag) :
    (added s parent tag ty old r).liveSpace = (bufferUpdated s parent old r).liveSpace := by
  have lengths := (wellFormed_parts s valid).1
  have addedLength : (added s parent tag ty old r).storage.objects.length = s.storage.objects.length + 1 := by
    simp [added]
  have baseLength : (bufferUpdated s parent old r).storage.objects.length = s.storage.objects.length := by
    simp [bufferUpdated, Frame.updated]
  simp only [State.liveSpace, addedLength, baseLength, List.range_succ, List.map_append,
    List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    added_node_fresh s parent tag ty old r lengths, Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro i member
  exact added_node_old s parent tag ty old r valid found tagFound i (List.mem_range.mp member)

theorem added_space (s : State) (parent : Nat) (tag : Tag) (ty : Ty) (old : Buffer Value)
    (r : Result Value Unit) (valid : s.wellFormed = true)
    (found : s.storage.lookup parent = some old) (tagFound : s.forest.lookup parent = some tag) :
    (added s parent tag ty old r).liveSpace + old.capacity = s.liveSpace + r.buffer.capacity := by
  rw [added_live s parent tag ty old r valid found tagFound]
  exact CppNestedGrowth.updated_space ⟨s,[],[]⟩ parent old tag r found tagFound

theorem added_peak (s : State) (parent : Nat) (tag : Tag) (ty : Ty) (old : Buffer Value)
    (r : Result Value Unit) (valid : s.wellFormed = true)
    (found : s.storage.lookup parent = some old) (tagFound : s.forest.lookup parent = some tag)
    (run : CppVectorGrowth.append old (accepts tag.element) true (.child s.storage.objects.length) = some r) :
    (added s parent tag ty old r).liveSpace - s.storage.baseSpace ≤
      (added s parent tag ty old r).storage.peak := by
  have peaks := CppVectorStoreGrowth.append_peak old (accepts tag.element) (.child s.storage.objects.length) r run
  rw [added_live s parent tag ty old r valid found tagFound]
  exact CppNestedGrowth.updated_peak ⟨s,[],[]⟩ parent old tag r found tagFound peaks.1 peaks.2

end Proofs.CppAppendRow
