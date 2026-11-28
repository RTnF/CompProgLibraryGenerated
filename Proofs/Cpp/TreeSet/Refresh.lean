import Proofs.Cpp.TreeSet.Frame
import Proofs.Cpp.TreeSet.Kth

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeSet

def slotOffset (index : UInt64) : Int := Cpp.toSigned 64 index.toNat

def putCell {K : Type} (arena : cp.TreeSet K) (index : UInt64) (row : cp.TreeSet_Slot K) :
    cp.TreeSet K := { arena with slots := Cpp.set arena.slots (slotOffset index) row }

theorem slotOffset_nat (index : UInt64) (fits : index.toNat < 2 ^ 63) :
    (slotOffset index).toNat = index.toNat := by
  unfold slotOffset Cpp.toSigned
  rw [Nat.mod_eq_of_lt (by omega), ite_eq_left fits, Int.toNat_natCast]

@[simp] theorem putCell_size {K : Type} (arena : cp.TreeSet K) (i : UInt64) (row : cp.TreeSet_Slot K) :
    (putCell arena i row).slots.size = arena.slots.size := by simp [putCell, Cpp.set]

theorem cell_written {K : Type} [Inhabited K]
    (arena : cp.TreeSet K) (i : UInt64) (row : cp.TreeSet_Slot K)
    (inside : (slotOffset i).toNat < arena.slots.size) : cell (putCell arena i row).slots i = row := by
  change Cpp.get (Cpp.set arena.slots (slotOffset i) row) (slotOffset i) = row
  rw [Cpp.get_eq, Cpp.getElemBang_set _ _ _ _ inside, ite_eq_left rfl]

theorem cell_other {K : Type} [Inhabited K]
    (arena : cp.TreeSet K) (i j : UInt64) (row : cp.TreeSet_Slot K)
    (inside : (slotOffset i).toNat < arena.slots.size)
    (apart : (slotOffset j).toNat ≠ (slotOffset i).toNat) :
    cell (putCell arena i row).slots j = cell arena.slots j := by
  change Cpp.get (Cpp.set arena.slots (slotOffset i) row) (slotOffset j) = Cpp.get arena.slots (slotOffset j)
  rw [Cpp.get_eq, Cpp.getElemBang_set _ _ _ _ inside, ite_eq_right apart, Cpp.get_eq]

theorem putCell_overwrite {K : Type} (arena : cp.TreeSet K) (i : UInt64) (row next : cp.TreeSet_Slot K) :
    putCell (putCell arena i row) i next = putCell arena i next := by
  unfold putCell Cpp.set
  congr 1
  apply Array.ext_getElem?
  intro j
  by_cases same : j = (slotOffset i).toNat
  · subst j
    simp [Array.getElem?_setIfInBounds_self]
  · simp [Ne.symm same]

theorem Layout.putCell_away {K : Type} [Inhabited K] {arena : cp.TreeSet K}
    {index : UInt64} {tree : Tree K} {used : List Nat} (layout : Layout arena.slots index tree used)
    (i : UInt64) (row : cp.TreeSet_Slot K) (inside : i.toNat < arena.slots.size)
    (fits : arena.slots.size ≤ 2 ^ 63) (outside : i.toNat ∉ used) :
    Layout (putCell arena i row).slots index tree used := by
  apply layout.frame
  · simpa using layout.in_range
  · intro j member
    symm
    exact cell_other arena i j row (by rwa [slotOffset_nat i (by omega)])
      (by rw [slotOffset_nat i (by omega), slotOffset_nat j (by have := layout.in_range _ member; omega)]
          exact fun same => outside (same ▸ member))

def refreshRow {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i : UInt64) :
    cp.TreeSet_Slot K :=
  let row := cell arena.slots i
  let leftHeight := modelHeight arena row.left
  let rightHeight := modelHeight arena row.right
  { row with
    height := 1 + if leftHeight < rightHeight then rightHeight else leftHeight
    size_ := 1 + modelSize arena row.left + modelSize arena row.right
    first := if row.left = endIndex then i else (cell arena.slots row.left).first
    last := if row.right = endIndex then i else (cell arena.slots row.right).last }

private theorem some_bind {A B : Type} (value : A) (next : A → Option B) :
    (some value >>= next) = next value := rfl

private theorem pure_run {A : Type} (value : A) (clock : Nat) :
    (pure value : Cpp.M A).run clock = some (value, clock) := rfl

private theorem tick_run (clock : Nat) : Cpp.tick.run clock = some ((), clock + 1) := rfl
private theorem sentinel_run {K : Type} (clock : Nat) :
    (cp.TreeSet.none (T := K)).run clock = some (endIndex, clock + 1) := rfl

theorem generated_refresh_run {K : Type} [Inhabited K] (arena : cp.TreeSet K)
    (i : UInt64) (inside : (slotOffset i).toNat < arena.slots.size)
    (leftApart : (cell arena.slots i).left = endIndex ∨
      (slotOffset (cell arena.slots i).left).toNat ≠ (slotOffset i).toNat)
    (rightApart : (cell arena.slots i).right = endIndex ∨
      (slotOffset (cell arena.slots i).right).toNat ≠ (slotOffset i).toNat)
    (start : Nat) :
    (cp.TreeSet.refresh arena i).run start = some (putCell arena i (refreshRow arena i), start + 11) := by
  cases arena with
  | mk storage root free =>
    let arena : cp.TreeSet K := ⟨storage, root, free⟩
    let original := cell storage i
    let a := modelHeight arena original.left
    let b := modelHeight arena original.right
    let withHeight := { original with height := 1 + if decide (a < b) then b else a }
    let one := putCell arena i withHeight
    let withSize := { cell one.slots i with
      size_ := 1 + modelSize one original.left + modelSize one original.right }
    let two := putCell one i withSize
    let withFirst := { cell two.slots i with
      first := if decide (original.left = endIndex) then i else (cell two.slots original.left).first }
    let three := putCell two i withFirst
    let withLast := { cell three.slots i with
      last := if decide (original.right = endIndex) then i else (cell three.slots original.right).last }
    simp only [cp.TreeSet.refresh, StateT.run_bind, tick_run, sentinel_run, generated_height_run,
      generated_size_run, some_bind, pure_run]
    change some (putCell three i withLast, start + 11) = _
    have read1 : cell one.slots i = withHeight := cell_written arena i withHeight inside
    have read2 : cell two.slots i = withSize := cell_written one i withSize (by simpa [one] using inside)
    have read3 : cell three.slots i = withFirst := cell_written two i withFirst (by simpa [three, two, one] using inside)
    have stayed (row : cp.TreeSet_Slot K) (j : UInt64)
        (apart : j = endIndex ∨ (slotOffset j).toNat ≠ (slotOffset i).toNat) :
        modelSize (putCell arena i row) j = modelSize arena j ∧
          ((if decide (j = endIndex) then i else (cell (putCell arena i row).slots j).first) =
            (if j = endIndex then i else (cell arena.slots j).first)) ∧
          ((if decide (j = endIndex) then i else (cell (putCell arena i row).slots j).last) =
            (if j = endIndex then i else (cell arena.slots j).last)) := by
      rcases apart with sentinel | other
      · simp [sentinel, modelSize]
      · simp [modelSize, cell_other arena i j row inside other]
    have leftSize := (stayed withHeight original.left leftApart).1
    have rightSize := (stayed withHeight original.right rightApart).1
    have leftFirst := (stayed withSize original.left leftApart).2.1
    have rightLast := (stayed withFirst original.right rightApart).2.2
    have twoSimple : two = putCell arena i withSize := putCell_overwrite _ _ _ _
    have threeSimple : three = putCell arena i withFirst := by
      dsimp only [three]
      rw [twoSimple, putCell_overwrite]
    rw [threeSimple, putCell_overwrite]
    congr 2
    dsimp only [withLast]
    rw [read3, threeSimple, rightLast]
    dsimp only [withFirst]
    rw [read2, twoSimple, leftFirst]
    dsimp only [withSize]
    rw [read1, leftSize, rightSize]
    unfold refreshRow
    dsimp only [withHeight, a, b]
    simp [arena, original]

theorem generated_refresh_layout {K : Type} [Inhabited K] (arena : cp.TreeSet K)
    (i : UInt64) (left : Tree K) (key : K) (right : Tree K) (ls rs : List Nat)
    (pending : Pending arena i left key right ls rs)
    (fits : arena.slots.size ≤ 2 ^ 63) (start : Nat) :
    let next := putCell arena i (refreshRow arena i)
    (cp.TreeSet.refresh arena i).run start = some (next, start + 11) ∧
    Layout next.slots i (.node left key right) (i.toNat :: (ls ++ rs)) := by
  let row := cell arena.slots i
  let updated := refreshRow arena i
  let next := putCell arena i updated
  have indexFits : i.toNat < 2 ^ 63 := by have := pending.allocated; omega
  have inside : (slotOffset i).toNat < arena.slots.size := by
    simpa only [slotOffset_nat i indexFits] using pending.allocated
  have apart {c : UInt64} {tree : Tree K} {used : List Nat}
      (layout : Layout arena.slots c tree used) (different : i.toNat ∉ used) :
      c = endIndex ∨ (slotOffset c).toNat ≠ (slotOffset i).toNat := by
    rcases layout.index_used with sentinel | member
    · exact Or.inl sentinel
    · have cFits : c.toNat < 2 ^ 63 := by have := layout.in_range _ member; omega
      right
      rw [slotOffset_nat _ cFits, slotOffset_nat _ indexFits]
      exact fun same => different (same ▸ member)
  have ll := pending.leftLayout.putCell_away i updated pending.allocated fits pending.leftApart
  have rr := pending.rightLayout.putCell_away i updated pending.allocated fits pending.rightApart
  have read : cell next.slots i = updated := cell_written arena i updated inside
  have lh : (modelHeight arena row.left).toNat = left.height := pending.leftLayout.model_height
  have rh : (modelHeight arena row.right).toNat = right.height := pending.rightLayout.model_height
  have ln : (modelSize arena row.left).toNat = left.size := pending.leftLayout.model_size
  have rn : (modelSize arena row.right).toNat = right.size := pending.rightLayout.model_size
  have unique : (i.toNat :: (ls ++ rs)).Nodup := by
    refine List.nodup_cons.mpr ⟨by simp [pending.leftApart, pending.rightApart],
      List.nodup_append.mpr ⟨pending.leftLayout.distinct, pending.rightLayout.distinct, ?_⟩⟩
    intro a ha b hb eq
    subst b
    exact pending.disjoint ha hb
  have capacity := unique.length_le_of_subset (l₂ := List.range arena.slots.size) (by
    intro j member
    apply List.mem_range.mpr
    rcases List.mem_cons.mp member with rfl | below
    · exact pending.allocated
    · exact (List.mem_append.mp below).elim
        (pending.leftLayout.in_range j) (pending.rightLayout.in_range j))
  simp only [List.length_cons, List.length_append, List.length_range, pending.leftLayout.node_count,
    pending.rightLayout.node_count] at capacity
  have layoutSize : left.size + right.size + 1 < 2 ^ 64 := by omega
  have chosen : (if modelHeight arena row.left < modelHeight arena row.right
      then modelHeight arena row.right else modelHeight arena row.left).toNat =
        max left.height right.height := by
    by_cases shorter : modelHeight arena row.left < modelHeight arena row.right
    · have less : left.height < right.height := by rwa [UInt64.lt_iff_toNat_lt, lh, rh] at shorter
      simp [shorter, rh, max_eq_right (le_of_lt less)]
    · have le : right.height ≤ left.height := by
        rw [UInt64.lt_iff_toNat_lt, lh, rh] at shorter
        omega
      simp [shorter, lh, max_eq_left le]
  have counts : updated.size_.toNat = (Tree.node left key right).size := by
    change (1 + modelSize arena row.left + modelSize arena row.right).toNat = _
    rw [UInt64.toNat_add, UInt64.toNat_add, ln, rn]
    change ((1 + left.size) % (2 ^ 64) + right.size) % (2 ^ 64) = _
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp only [Tree.size]
    omega
  have heights : updated.height.toNat = (Tree.node left key right).height := by
    change (1 + (if modelHeight arena row.left < modelHeight arena row.right
      then modelHeight arena row.right else modelHeight arena row.left)).toNat = _
    rw [UInt64.toNat_add, chosen]
    change (1 + max left.height right.height) % (2 ^ 64) = _
    have boundsL := left.height_le_size
    have boundsR := right.height_le_size
    rw [Nat.mod_eq_of_lt (by omega)]
    simp only [Tree.height]
    omega
  refine ⟨generated_refresh_run arena i inside (apart pending.leftLayout pending.leftApart)
    (apart pending.rightLayout pending.rightApart) start, ?_⟩
  change Layout next.slots i (.node left key right) (i.toNat :: (ls ++ rs))
  refine .node (by simpa [next] using pending.allocated) pending.nonnull ?_ ?_ ?_ ?_ ?_ ?_ ?_
    pending.leftApart pending.rightApart pending.disjoint
  · rw [read]
    exact pending.value
  · exact read ▸ heights
  · exact read ▸ counts
  · rw [read]
    change cachedFirst arena.slots i row.left = cachedFirst next.slots i row.left
    rcases pending.leftLayout.index_used with endCode | usedCode
    · simp [cachedFirst, row, endCode]
    · have childIndex := pending.leftLayout.in_range _ usedCode
      have different : row.left.toNat ≠ i.toNat := by
        intro eq
        exact pending.leftApart (eq ▸ usedCode)
      have word : (slotOffset row.left).toNat ≠ (slotOffset i).toNat := by
        rw [slotOffset_nat _ (by change row.left.toNat < arena.slots.size at childIndex; omega), slotOffset_nat _ indexFits]
        exact different
      have child : cell next.slots row.left = cell arena.slots row.left :=
        cell_other arena i row.left updated inside word
      simp [cachedFirst, child]
  · rw [read]
    change cachedLast arena.slots i row.right = cachedLast next.slots i row.right
    rcases pending.rightLayout.index_used with endCode | usedCode
    · simp [cachedLast, row, endCode]
    · have childIndex := pending.rightLayout.in_range _ usedCode
      have different : row.right.toNat ≠ i.toNat := by
        intro eq
        exact pending.rightApart (eq ▸ usedCode)
      have word : (slotOffset row.right).toNat ≠ (slotOffset i).toNat := by
        rw [slotOffset_nat _ (by change row.right.toNat < arena.slots.size at childIndex; omega), slotOffset_nat _ indexFits]
        exact different
      have child : cell next.slots row.right = cell arena.slots row.right :=
        cell_other arena i row.right updated inside word
      simp [cachedLast, child]
  · rw [read]
    exact ll
  · rw [read]
    exact rr

end Proofs.Cpp.TreeSet
