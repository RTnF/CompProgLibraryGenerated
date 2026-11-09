import Proofs.VecWrite

namespace Proofs.SortPairsFrame
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.VecWrite

/-- The components of the sorted pairs are the components of the original pairs. -/
theorem sortedPairs_mem_fst (xs ys : List Int) (x : Int) (h : x ∈ (sortedPairs (xs.zip ys)).map Prod.fst) : x ∈ xs := by
  simp only [List.mem_map, sortedPairs] at h
  obtain ⟨p, hp, rfl⟩ := h
  exact (List.of_mem_zip ((List.mem_mergeSort).mp hp)).1

theorem sortedPairs_mem_snd (xs ys : List Int) (y : Int) (h : y ∈ (sortedPairs (xs.zip ys)).map Prod.snd) : y ∈ ys := by
  simp only [List.mem_map, sortedPairs] at h
  obtain ⟨p, hp, rfl⟩ := h
  exact (List.of_mem_zip ((List.mem_mergeSort).mp hp)).2

theorem sortedPairs_length (xs ys : List Int) (h : xs.length = ys.length) :
    (sortedPairs (xs.zip ys)).length = xs.length := by
  simp [sortedPairs, List.length_mergeSort, List.length_zip, h]

/-- Replacing the items by integers drawn from the old ones, in the same number, keeps a buffer valid. -/
theorem valid_of_components (buffer : Buffer Value) (ty : Ty) (xs zs : List Int)
    (hi : buffer.items = xs.map Value.integer) (hv : buffer.Valid (accepts (.integer ty)))
    (hlen : zs.length = xs.length) (hmem : ∀ z ∈ zs, z ∈ xs) :
    ({buffer with items := zs.map Value.integer} : Buffer Value).Valid (accepts (.integer ty)) := by
  obtain ⟨h1, h2, h3⟩ := hv
  refine ⟨?_, h2, ?_⟩
  · simp only [List.length_map]
    rw [hi] at h1; simpa [hlen] using h1
  · simp only [List.all_eq_true, List.mem_map] at h3 ⊢
    intro v hv
    obtain ⟨z, hz, rfl⟩ := hv
    exact h3 (Value.integer z) (by rw [hi]; exact List.mem_map.mpr ⟨z, hmem z hz, rfl⟩)

/-- The first row of the sorted pairs, as the buffer result of the sort. -/
def resultA (bufA : Buffer Value) (xs ys : List Int) : Result Value Unit :=
  ⟨{bufA with items := (sortedPairs (xs.zip ys)).map fun p => Value.integer p.1},(),
    Proofs.StlContracts.sortComparisons xs.length + xs.length,bufA.capacity+2⟩

/-- The second row of the sorted pairs. -/
def resultB (bufB : Buffer Value) (xs ys : List Int) : Result Value Unit :=
  ⟨{bufB with items := (sortedPairs (xs.zip ys)).map fun p => Value.integer p.2},(),xs.length,bufB.capacity+2⟩

/-- `std::sort` of a vector of pairs (two rows of equal length) replaces both rows by the components of the sorted pairs. -/
theorem sortPairs_ok (f : Frame) (a b : Nat) (ty : Ty)
    (bindingA bindingB : Binding) (bufA bufB : Buffer Value) (tagA tagB : Tag)
    (resolvedA : f.resolve a (.integer ty) = some (bindingA,bufA))
    (resolvedB : f.resolve b (.integer ty) = some (bindingB,bufB))
    (objectA : f.object bindingA.owner (.integer ty) = some (bufA,tagA))
    (objectB : f.object bindingB.owner (.integer ty) = some (bufB,tagB))
    (different : bindingA.owner ≠ bindingB.owner)
    (writableA : bindingA.writable = true) (writableB : bindingB.writable = true)
    (xs ys : List Int) (hx : bufA.items.mapM Value.intOf = some xs) (hy : bufB.items.mapM Value.intOf = some ys)
    (hlen : xs.length = ys.length) :
    f.sortPairsAll a b ty = some
      ((f.updated bindingA.owner bufA (resultA bufA xs ys)).updated bindingB.owner bufB (resultB bufB xs ys)) := by
  obtain ⟨validA,ownsA,bufferValidA,tagFoundA,elementA⟩ := Proofs.CppNestedRows.buffer_facts f bindingA.owner ty bufA tagA objectA
  obtain ⟨validB,ownsB,bufferValidB,tagFoundB,elementB⟩ := Proofs.CppNestedRows.buffer_facts f bindingB.owner ty bufB tagB objectB
  obtain ⟨_,foundA,_,_⟩ := Proofs.CppNestedFacts.object_buffer f bindingA.owner _ bufA tagA objectA
  obtain ⟨_,foundB,_,_⟩ := Proofs.CppNestedFacts.object_buffer f bindingB.owner _ bufB tagB objectB
  have itemsA := mapM_intOf _ _ hx
  have itemsB := mapM_intOf _ _ hy
  have lenS := sortedPairs_length xs ys hlen
  have newValidA : (resultA bufA xs ys).buffer.Valid (accepts (.integer ty)) := by
    have := valid_of_components bufA ty xs ((sortedPairs (xs.zip ys)).map Prod.fst) itemsA bufferValidA
      (by simp [lenS]) (fun z hz => sortedPairs_mem_fst xs ys z hz)
    simpa [resultA, List.map_map, Function.comp_def] using this
  have newValidB : (resultB bufB xs ys).buffer.Valid (accepts (.integer ty)) := by
    have := valid_of_components bufB ty ys ((sortedPairs (xs.zip ys)).map Prod.snd) itemsB bufferValidB
      (by simp [lenS, hlen]) (fun z hz => sortedPairs_mem_snd xs ys z hz)
    simpa [resultB, List.map_map, Function.comp_def] using this
  have commitA := commit_runs f bindingA.owner (.integer ty) bufA tagA (resultA bufA xs ys) validA objectA
    tagFoundA foundA (by simpa [resultA] using ownsA) (by simp [payloadOK, elementA, newValidA])
    (by simp [resultA]) (by simp [resultA])
  have validA' : (f.updated bindingA.owner bufA (resultA bufA xs ys)).state.wellFormed = true :=
    commit_success_valid f _ bindingA.owner _ _ commitA
  have foundB' : (f.updated bindingA.owner bufA (resultA bufA xs ys)).state.storage.lookup bindingB.owner = some bufB := by
    rw [CppNestedOps.updated_lookup_other f bindingA.owner bindingB.owner bufA _ different]; exact foundB
  have tagFoundB' : (f.updated bindingA.owner bufA (resultA bufA xs ys)).state.forest.lookup bindingB.owner = some tagB := by
    rw [CppNestedOps.updated_forest]; exact tagFoundB
  have objectB' := object_runs (f.updated bindingA.owner bufA (resultA bufA xs ys)) bindingB.owner (.integer ty) bufB tagB
    validA' foundB' tagFoundB' elementB
  have commitB := commit_runs (f.updated bindingA.owner bufA (resultA bufA xs ys)) bindingB.owner (.integer ty) bufB tagB
    (resultB bufB xs ys) validA' objectB' tagFoundB' foundB' (by simpa [resultB] using ownsB)
    (by simp [payloadOK, elementB, newValidB]) (by simp [resultB]) (by simp [resultB])
  unfold Frame.sortPairsAll
  simp only [resolvedA, resolvedB, Bind.bind, Option.bind]
  rw [if_pos ⟨different, writableA, writableB, bufferValidA, bufferValidB⟩]
  simp only [hx, hy, if_pos hlen]
  show (f.commit bindingA.owner (.integer ty) (resultA bufA xs ys)).bind
      (fun committed => committed.commit bindingB.owner (.integer ty) (resultB bufB xs ys)) = _
  rw [commitA]
  exact commitB

end Proofs.SortPairsFrame
