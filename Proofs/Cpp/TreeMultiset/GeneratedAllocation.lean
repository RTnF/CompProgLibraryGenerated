import Proofs.Cpp.TreeMultiset.GeneratedLayout

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

private theorem decode_of_fits {code : UInt64} (fits : code.toNat < 2 ^ 63) :
    decode code = some code.toNat := by
  have notEnd : code ≠ endIndex := by
    intro same
    rw [same] at fits
    change 18446744073709551615 < 9223372036854775808 at fits
    omega
  simp [decode, notEnd]

theorem generated_allocate_reuse_spec {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K)
    (key : K) (count priority : UInt64) (index : Nat) (rest : List Nat)
    (freeList : FreeSlots (storageView arena) (decode arena.free_head) (index :: rest))
    (fits : arena.slots.size ≤ 2 ^ 63) (start : Nat) :
    ∃ out, (cp.TreeMultiSet.allocate arena key count priority).run start =
      some ((arena.free_head, out), start + 4) ∧
      out.root = arena.root ∧ out.slots.size = arena.slots.size ∧
      Realizes (storageView out) (decode arena.free_head) (.node key priority count.toNat .empty .empty) [index] ∧
      FreeSlots (storageView out) (decode out.free_head) rest ∧
      ∀ i, i ≠ index → (storageView out)[i]? = (storageView arena)[i]? := by
  generalize headEq : decode arena.free_head = head at freeList
  cases freeList with
  | @cons _ next _ old reads vacant link tail fresh =>
    obtain ⟨notEnd, _⟩ := decode_some arena.free_head index headEq
    obtain ⟨codeNat, inside, row⟩ := modelCell_view arena arena.free_head index old headEq reads fits
    have signed : Cpp.toSigned 64 arena.free_head.toNat = (index : Int) := by
      rw [signed_model_index (by omega), codeNat]
    let newSlot : cp.TreeMultiSet_Slot K := ⟨some key, priority, count, count, endIndex, endIndex⟩
    let out : cp.TreeMultiSet K := ⟨Cpp.set arena.slots (index : Int) newSlot, arena.root,
      (modelCell arena arena.free_head).left⟩
    have outView : storageView out = (storageView arena).setIfInBounds index (slotView newSlot) :=
      storageView_set arena index newSlot
    have outReads : (storageView out)[index]? = some (slotView newSlot) := by
      rw [outView]
      simp [storageView, inside]
    have outFrame (i : Nat) (other : i ≠ index) :
        (storageView out)[i]? = (storageView arena)[i]? := by
      rw [outView, Array.getElem?_setIfInBounds_ne other.symm]
    refine ⟨out, ?_, rfl, Cpp.size_set _ _ _, ?_, ?_, outFrame⟩
    · rw [generated_reuse_run arena key count priority notEnd (by simpa only [signed, Int.toNat_natCast])]
      rw [signed]
    · refine .node ?_ .empty .empty (by simp) (by simp) (by simp)
      simpa [newSlot, slotView, Tree.weight, (decode_none _).2 rfl] using outReads
    · have nextEq : decode out.free_head = next := (congrArg StoredNode.left row).trans link
      rw [nextEq]
      exact tail.frame fun i mem => outFrame i fun same => fresh (same ▸ mem)

theorem generated_allocate_append_spec {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K)
    (key : K) (count priority : UInt64) (noFree : arena.free_head = endIndex)
    (fits : arena.slots.size < 2 ^ 63) (start : Nat) :
    ∃ code out, (cp.TreeMultiSet.allocate arena key count priority).run start = some ((code, out), start + 6) ∧
      decode code = some arena.slots.size ∧ out.root = arena.root ∧
      out.slots.size = arena.slots.size + 1 ∧
      Realizes (storageView out) (decode code) (.node key priority count.toNat .empty .empty) [arena.slots.size] ∧
      FreeSlots (storageView out) (decode out.free_head) [] ∧
      ∀ i < arena.slots.size, (storageView out)[i]? = (storageView arena)[i]? := by
  let code := UInt64.ofNat arena.slots.size
  let newSlot : cp.TreeMultiSet_Slot K := ⟨some key, priority, count, count, endIndex, endIndex⟩
  let out : cp.TreeMultiSet K := ⟨arena.slots.push newSlot, arena.root, endIndex⟩
  have codeNat : code.toNat = arena.slots.size := UInt64.toNat_ofNat_of_lt'
    (by change arena.slots.size < 2 ^ 64; omega)
  have decoded : decode code = some arena.slots.size := by
    rw [decode_of_fits (by rwa [codeNat]), codeNat]
  have outView : storageView out = (storageView arena).push (slotView newSlot) :=
    storageView_push arena newSlot
  have viewSize : (storageView arena).size = arena.slots.size := Array.size_map
  have outReads : (storageView out)[arena.slots.size]? = some (slotView newSlot) := by
    rw [outView, ← viewSize, Array.getElem?_push_size]
  refine ⟨code, out, generated_append_run arena key count priority noFree fits start,
    decoded, rfl, Array.size_push newSlot, ?_, ?_, ?_⟩
  · rw [decoded]
    refine .node ?_ .empty .empty (by simp) (by simp) (by simp)
    simpa [newSlot, slotView, Tree.weight, (decode_none _).2 rfl] using outReads
  · exact (decode_none endIndex).2 rfl ▸ FreeSlots.empty
  · intro i bounded
    rw [outView, Array.getElem?_push]
    have below : i < (storageView arena).size := by rwa [viewSize]
    simp [Nat.ne_of_lt below]

theorem generated_release_spec {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K)
    (code : UInt64) (index : Nat) (row : StoredNode K) (rest : List Nat)
    (decoded : decode code = some index) (reads : (storageView arena)[index]? = some row)
    (live : row.key.isSome = true)
    (freeList : FreeSlots (storageView arena) (decode arena.free_head) rest)
    (fits : arena.slots.size ≤ 2 ^ 63) (start : Nat) :
    ∃ out, (cp.TreeMultiSet.release arena code).run start = some (out, start + 1) ∧
      out.root = arena.root ∧ out.free_head = code ∧ out.slots.size = arena.slots.size ∧
      FreeSlots (storageView out) (decode out.free_head) (index :: rest) ∧
      ∀ i, i ≠ index → (storageView out)[i]? = (storageView arena)[i]? := by
  obtain ⟨codeNat, inside, _⟩ := modelCell_view arena code index row decoded reads fits
  have signed : Cpp.toSigned 64 code.toNat = (index : Int) := by
    rw [signed_model_index (by omega), codeNat]
  have signedInside : (Cpp.toSigned 64 code.toNat).toNat < arena.slots.size := by
    simpa only [signed, Int.toNat_natCast]
  have fresh : index ∉ rest := by
    intro mem
    obtain ⟨vacantRow, vacantReads, vacantKey⟩ := freeList.vacant index mem
    have same := Option.some.inj (reads.symm.trans vacantReads)
    cases same
    simp [vacantKey] at live
  let newSlot : cp.TreeMultiSet_Slot K := { modelCell arena code with key := none, left := arena.free_head }
  let out : cp.TreeMultiSet K := ⟨Cpp.set arena.slots (index : Int) newSlot, arena.root, code⟩
  have outView : storageView out = (storageView arena).setIfInBounds index (slotView newSlot) :=
    storageView_set arena index newSlot
  have outReads : (storageView out)[index]? = some (slotView newSlot) := by
    rw [outView]
    simp [storageView, inside]
  have outFrame (i : Nat) (other : i ≠ index) :
      (storageView out)[i]? = (storageView arena)[i]? := by
    rw [outView, Array.getElem?_setIfInBounds_ne other.symm]
  refine ⟨out, ?_, rfl, rfl, Cpp.size_set _ _ _, ?_, outFrame⟩
  · rw [generated_release_run arena code signedInside, signed]
  · change FreeSlots (storageView out) (decode code) (index :: rest)
    rw [decoded]
    exact .cons outReads rfl rfl (freeList.frame fun i mem => outFrame i fun same => fresh (same ▸ mem)) fresh

end Proofs.Cpp.TreeMultiset
