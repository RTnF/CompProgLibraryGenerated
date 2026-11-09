import Proofs.VecWrite

namespace Proofs.SortPairsFrame
open Proofs.CppNestedProgram
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

theorem pairLE_trans (a b c : Int × Int) (h1 : pairLE a b = true) (h2 : pairLE b c = true) : pairLE a c = true := by
  simp only [pairLE, decide_eq_true_eq] at *
  omega

theorem pairLE_total (a b : Int × Int) : (pairLE a b || pairLE b a) = true := by
  simp only [pairLE, Bool.or_eq_true, decide_eq_true_eq]
  omega

/-- The sorted pairs are in lexicographic order. -/
theorem sortedPairs_sorted (ps : List (Int × Int)) :
    (sortedPairs ps).Pairwise (fun p q => pairLE p q = true) := by
  have := List.pairwise_mergeSort (le := pairLE) pairLE_trans pairLE_total ps
  simpa [sortedPairs] using this

/-- The sorted pairs are a permutation of the input pairs. -/
theorem sortedPairs_perm (ps : List (Int × Int)) : (sortedPairs ps).Perm ps := by
  simpa [sortedPairs] using List.mergeSort_perm ps pairLE

/-- `std::sort` of a vector of pairs as a statement: the two row containers are evaluated in order, both rows are
resolved, and the frame becomes the one of `sortPairsAll`; the cost is `charge 1 1` after the release. -/
theorem run_sortPairs (s s1 s2 : NState) (first second : Container) (ty : Ty) (a b : Nat) (fr : Frame)
    (e1 : first.eval (s.charge 0 (first.nodes+second.nodes+3)) = some (s1,a))
    (e2 : second.eval s1 = some (s2,b))
    (sorted : s2.frame.sortPairsAll a b ty = some fr) :
    (NStmt.sortPairs first second ty).run s =
      some ⟨((({s2 with frame := fr} : NState).release s).charge 1 1),none,false⟩ := by
  simp [NStmt.run, e1, e2, sorted]

/-- The effect of the statement on the frame: both rows hold the components of the sorted pairs. -/
theorem run_sortPairs_frame (s s1 s2 : NState) (first second : Container) (ty : Ty) (a b : Nat)
    (e1 : first.eval (s.charge 0 (first.nodes+second.nodes+3)) = some (s1,a))
    (e2 : second.eval s1 = some (s2,b))
    (bindingA bindingB : Binding) (bufA bufB : Buffer Value) (tagA tagB : Tag)
    (resolvedA : s2.frame.resolve a (.integer ty) = some (bindingA,bufA))
    (resolvedB : s2.frame.resolve b (.integer ty) = some (bindingB,bufB))
    (objectA : s2.frame.object bindingA.owner (.integer ty) = some (bufA,tagA))
    (objectB : s2.frame.object bindingB.owner (.integer ty) = some (bufB,tagB))
    (different : bindingA.owner ≠ bindingB.owner)
    (writableA : bindingA.writable = true) (writableB : bindingB.writable = true)
    (xs ys : List Int) (hx : bufA.items.mapM Value.intOf = some xs) (hy : bufB.items.mapM Value.intOf = some ys)
    (hlen : xs.length = ys.length) :
    ∃ t, (NStmt.sortPairs first second ty).run s = some ⟨t,none,false⟩ ∧
      t.frame.state = ((s2.frame.updated bindingA.owner bufA (resultA bufA xs ys)).updated bindingB.owner bufB
        (resultB bufB xs ys)).state ∧
      t.frame.rootWritable = ((s2.frame.updated bindingA.owner bufA (resultA bufA xs ys)).updated bindingB.owner bufB
        (resultB bufB xs ys)).rootWritable ∧
      t.frame.bindings = (((s2.frame.updated bindingA.owner bufA (resultA bufA xs ys)).updated bindingB.owner bufB
        (resultB bufB xs ys)).bindings).take s.frame.bindings.length := by
  have sorted := sortPairs_ok s2.frame a b ty bindingA bindingB bufA bufB tagA tagB resolvedA resolvedB objectA objectB
    different writableA writableB xs ys hx hy hlen
  refine ⟨_, run_sortPairs s s1 s2 first second ty a b _ e1 e2 sorted, ?_, ?_, ?_⟩ <;> simp [NState.release]

end Proofs.SortPairsFrame
