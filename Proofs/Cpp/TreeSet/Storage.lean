import Proofs.Cpp.TreeSet.Rebalance

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeSet

def singletonRow {K : Type} (i : UInt64) (key : K) : cp.TreeSet_Slot K :=
  ⟨some key, endIndex, endIndex, 1, 1, i, i⟩

private theorem raw_read_written {A : Type} [Inhabited A] (slots : Array A) (i : Int) (row : A)
    (inside : i.toNat < slots.size) : Cpp.get (Cpp.set slots i row) i = row := by
  rw [Cpp.get_eq, Cpp.getElemBang_set _ _ _ _ inside, ite_eq_left rfl]

private theorem raw_overwrite {A : Type} (slots : Array A) (i : Int) (before after : A) :
    Cpp.set (Cpp.set slots i before) i after = Cpp.set slots i after := by
  unfold Cpp.set
  apply Array.ext_getElem?
  intro n
  by_cases same : n = i.toNat
  · subst n
    simp [Array.getElem?_setIfInBounds_self]
  · simp [Ne.symm same]

private theorem raw_append_write {A : Type} (slots : Array A) (before after : A) :
    Cpp.set (slots.push before) (slots.size : Int) after = slots.push after := by
  apply Array.ext_getElem?
  intro index
  by_cases same : index = slots.size
  · subst index
    simp [Cpp.set]
  · simp [Cpp.set, same, Ne.symm same, Array.getElem?_push]

private theorem tick_run (clock : Nat) : Cpp.tick.run clock = some ((), clock + 1) := rfl

private theorem sentinel_run {K : Type} (clock : Nat) :
    (cp.TreeSet.none (T := K)).run clock = some (endIndex, clock + 1) := rfl

private theorem some_bind {A B : Type} (value : A) (next : A → Option B) :
    (some value >>= next) = next value := rfl

private theorem pure_run {A : Type} (value : A) (clock : Nat) :
    (pure value : Cpp.M A).run clock = some (value, clock) := rfl

theorem generated_allocate_reuse_run {K : Type} [Inhabited K] (arena : cp.TreeSet K)
    (key : K) (nonnull : arena.free_head ≠ endIndex)
    (inside : (slotOffset arena.free_head).toNat < arena.slots.size) (start : Nat) :
    let i := arena.free_head
    let next := putCell arena i (singletonRow i key)
    (cp.TreeSet.allocate arena key).run start =
      some ((i, { next with free_head := (cell arena.slots i).left }), start + 4) := by
  rcases arena with ⟨slots, root, free⟩
  have read (row : cp.TreeSet_Slot K) :
      Cpp.get (Cpp.set slots (slotOffset free) row) (slotOffset free) = row :=
    raw_read_written _ _ _ inside
  simp only [cp.TreeSet.allocate, StateT.run_bind, tick_run, sentinel_run, some_bind, pure_run,
    cell, putCell, slotOffset, singletonRow, nonnull, decide_false, Bool.false_eq_true, ite_false]
  simp only [slotOffset] at read
  simp only [read, raw_overwrite]

theorem generated_allocate_append_run {K : Type} [Inhabited K] (arena : cp.TreeSet K)
    (key : K) (noFree : arena.free_head = endIndex) (fits : arena.slots.size < 2 ^ 63) (start : Nat) :
    let i := UInt64.ofNat arena.slots.size
    let next : cp.TreeSet K := ⟨arena.slots.push (singletonRow i key), arena.root, endIndex⟩
    (cp.TreeSet.allocate arena key).run start = some ((i, next), start + 6) := by
  rcases arena with ⟨slots, root, free⟩
  dsimp only at noFree fits
  have sizeAsInt (row : cp.TreeSet_Slot K) : Cpp.size (slots.push row) - 1 = (slots.size : Int) := by
    simp [Cpp.size]
  have indexCode : UInt64.ofInt (slots.size : Int) = UInt64.ofNat slots.size := by
    unfold UInt64.ofInt
    rw [Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]
  have indexNat : (UInt64.ofNat slots.size).toNat = slots.size :=
    UInt64.toNat_ofNat_of_lt' (by change slots.size < 2 ^ 64; omega)
  have signedIndex : Cpp.toSigned 64 slots.size = (slots.size : Int) := by
    unfold Cpp.toSigned
    rw [Nat.mod_eq_of_lt (by omega), ite_eq_left fits]
  have readWritten (before after : cp.TreeSet_Slot K) :
      Cpp.get (Cpp.set (slots.push before) (slots.size : Int) after) (slots.size : Int) = after :=
    raw_read_written _ _ _ (by simp)
  have lastRead (row : cp.TreeSet_Slot K) : Cpp.get (slots.push row) (slots.size : Int) = row := by
    simp [Cpp.get_eq]
  simp only [cp.TreeSet.allocate, StateT.run_bind, tick_run, sentinel_run, some_bind, pure_run,
    noFree, decide_true, ite_true, singletonRow]
  simp only [sizeAsInt, indexCode, indexNat, signedIndex]
  simp only [raw_overwrite, readWritten, lastRead, raw_append_write]

theorem generated_release_run {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i : UInt64)
    (inside : (slotOffset i).toNat < arena.slots.size) (start : Nat) :
    let next := putCell arena i { cell arena.slots i with key := none, left := arena.free_head }
    (cp.TreeSet.release arena i).run start =
      some ({ next with free_head := i }, start + 1) := by
  rcases arena with ⟨slots, root, free⟩
  have read (row : cp.TreeSet_Slot K) :
      Cpp.get (Cpp.set slots (slotOffset i) row) (slotOffset i) = row :=
    raw_read_written _ _ _ inside
  simp only [cp.TreeSet.release, StateT.run_bind, tick_run, some_bind, pure_run, putCell, cell, slotOffset]
  simp only [slotOffset] at read
  simp only [read, raw_overwrite]


inductive FreeChain {K : Type} [Inhabited K] (storage : Array (cp.TreeSet_Slot K)) :
    UInt64 → List Nat → Prop
  | empty : FreeChain storage endIndex []
  | cons {index : UInt64} {rest : List Nat}
      (inside : index.toNat < storage.size) (nonnull : index ≠ endIndex)
      (emptyKey : (cell storage index).key = none)
      (tail : FreeChain storage (cell storage index).left rest)
      (fresh : index.toNat ∉ rest) : FreeChain storage index (index.toNat :: rest)

theorem FreeChain.frame {K : Type} [Inhabited K] {before after : Array (cp.TreeSet_Slot K)}
    {index : UInt64} {free : List Nat} (chain : FreeChain before index free)
    (allocated : ∀ j ∈ free, j < after.size)
    (unchanged : ∀ j : UInt64, j.toNat ∈ free → cell before j = cell after j) :
    FreeChain after index free := by
  induction chain with
  | empty => exact .empty
  | @cons i used _ notEnd emptyKey tail fresh ih =>
    have row := unchanged i (by simp)
    rw [row] at emptyKey
    have remaining := ih (fun j h => allocated j (by simp [h])) (fun j h => unchanged j (by simp [h]))
    rw [row] at remaining
    exact .cons (allocated i.toNat (by simp)) notEnd emptyKey remaining fresh

theorem FreeChain.in_range {K : Type} [Inhabited K] {storage : Array (cp.TreeSet_Slot K)}
    {index : UInt64} {free : List Nat} (chain : FreeChain storage index free) :
    ∀ j ∈ free, j < storage.size := by
  induction chain with
  | empty => simp
  | cons inside _ _ _ _ ih =>
    intro j present
    rcases List.mem_cons.mp present with rfl | below
    · exact inside
    · exact ih _ below

theorem FreeChain.empty_key {K : Type} [Inhabited K] {storage : Array (cp.TreeSet_Slot K)}
    {index : UInt64} {free : List Nat} (chain : FreeChain storage index free) (j : UInt64)
    (member : j.toNat ∈ free) : (cell storage j).key = none := by
  induction chain with
  | empty => simp at member
  | @cons i used inside nonnull emptyKey tail fresh ih =>
    rcases List.mem_cons.mp member with same | below
    · rwa [UInt64.toNat_inj.mp same]
    · exact ih below

theorem Layout.occupied_key {K : Type} [Inhabited K] {storage : Array (cp.TreeSet_Slot K)}
    {index : UInt64} {tree : Tree K} {used : List Nat} (layout : Layout storage index tree used)
    (j : UInt64) (member : j.toNat ∈ used) : ∃ key, (cell storage j).key = some key := by
  induction layout with
  | empty => simp at member
  | @node i key left right ls rs inside nonnull value _ _ _ _ l r freshLeft freshRight disjoint il ir =>
    rcases List.mem_cons.mp member with same | below
    · exact ⟨key, by rwa [UInt64.toNat_inj.mp same]⟩
    · exact (List.mem_append.mp below).elim il ir

theorem Layout.disjoint_free {K : Type} [Inhabited K] {storage : Array (cp.TreeSet_Slot K)}
    {index head : UInt64} {tree : Tree K} {used free : List Nat}
    (layout : Layout storage index tree used) (chain : FreeChain storage head free) :
    List.Disjoint used free := by
  intro n occupied available
  have fits : n < UInt64.size := by
    induction layout with
    | empty => simp at occupied
    | @node i key left right ls rs inside nonnull val _ _ _ _ l r fl fr apart il ir =>
      rcases List.mem_cons.mp occupied with rfl | below
      · exact UInt64.toNat_lt i
      · exact (List.mem_append.mp below).elim il ir
  let j := UInt64.ofNat n
  have nat : j.toNat = n := UInt64.toNat_ofNat_of_lt' fits
  obtain ⟨value, live⟩ := layout.occupied_key j (by rwa [nat])
  have vacant := chain.empty_key j (by rwa [nat])
  rw [live] at vacant
  contradiction

theorem FreeChain.putCell_away {K : Type} [Inhabited K] {arena : cp.TreeSet K}
    {index : UInt64} {free : List Nat} (chain : FreeChain arena.slots index free)
    (i : UInt64) (row : cp.TreeSet_Slot K) (inside : i.toNat < arena.slots.size)
    (fits : arena.slots.size ≤ 2 ^ 63) (apart : i.toNat ∉ free) :
    FreeChain (putCell arena i row).slots index free := by
  apply chain.frame
  · simpa using chain.in_range
  · intro j member
    symm
    exact cell_put_away arena i j row inside (chain.in_range j.toNat member) fits
      (fun same => apart ((congrArg UInt64.toNat same) ▸ member))

theorem ChangedWithin.free_chain {K : Type} [Inhabited K] {before after : cp.TreeSet K}
    {used free : List Nat} (changed : ChangedWithin before after used)
    (chain : FreeChain before.slots before.free_head free) (apart : List.Disjoint free used) :
    FreeChain after.slots after.free_head free := by
  rw [changed.free]
  apply chain.frame
  · simpa [changed.size] using chain.in_range
  · intro j member
    exact (changed.outside j (chain.in_range _ member) (apart member)).symm


structure Retained {K : Type} [Inhabited K] (before after : cp.TreeSet K) (modified : List Nat) : Prop where
  root : after.root = before.root
  size : before.slots.size ≤ after.slots.size
  outside : ∀ i, i.toNat < before.slots.size → i.toNat ∉ modified →
    cell after.slots i = cell before.slots i

theorem Retained.layout {K : Type} [Inhabited K] {before after : cp.TreeSet K}
    {index : UInt64} {tree : Tree K} {modified used : List Nat} (frame : Retained before after modified)
    (layout : Layout before.slots index tree used) (apart : List.Disjoint used modified) :
    Layout after.slots index tree used := by
  apply layout.frame
  · intro j present
    exact lt_of_lt_of_le (layout.in_range j present) frame.size
  · intro j present
    exact (frame.outside j (layout.in_range _ present) (apart present)).symm

theorem Retained.trans {K : Type} [Inhabited K] {a b c : cp.TreeSet K} {ls rs used : List Nat}
    (first : Retained a b ls) (second : Retained b c rs) (includesLeft : ls ⊆ used)
    (includesRight : rs ⊆ used) : Retained a c used :=
  ⟨second.root.trans first.root, first.size.trans second.size,
    fun j allocated apart => (second.outside j (lt_of_lt_of_le allocated first.size)
      (fun mem => apart (includesRight mem))).trans (first.outside j allocated (fun mem => apart (includesLeft mem)))⟩

theorem ChangedWithin.retained {K : Type} [Inhabited K] {a b : cp.TreeSet K} {used : List Nat}
    (frame : ChangedWithin a b used) : Retained a b used :=
  ⟨frame.root, Nat.le_of_eq frame.size.symm, frame.outside⟩

theorem generated_allocate_layout {K : Type} [Inhabited K] (arena : cp.TreeSet K) (key : K)
    (free : List Nat) (available : FreeChain arena.slots arena.free_head free)
    (fits : arena.slots.size < 2 ^ 63) (start : Nat) :
    ∃ i next remaining stop,
      (cp.TreeSet.allocate arena key).run start = some ((i, next), stop) ∧
      stop ≤ start + 6 ∧ next.slots.size ≤ 2 ^ 63 ∧
      Layout next.slots i (.node .empty key .empty) [i.toNat] ∧
      FreeChain next.slots next.free_head remaining ∧ Retained arena next [i.toNat] ∧
      (i.toNat = arena.slots.size ∨ i.toNat ∈ free) ∧
      (if free.isEmpty then next.slots.size = arena.slots.size + 1 ∧ remaining = []
       else next.slots.size = arena.slots.size ∧ free = i.toNat :: remaining) := by
  generalize headEq : arena.free_head = head at available
  cases available with
  | empty =>
    let i := UInt64.ofNat arena.slots.size
    let next : cp.TreeSet K := ⟨arena.slots.push (singletonRow i key), arena.root, endIndex⟩
    have indexNat : i.toNat = arena.slots.size := UInt64.toNat_ofNat_of_lt' (by change arena.slots.size < 2 ^ 64; omega)
    have nextSize : next.slots.size = arena.slots.size + 1 := Array.size_push _
    have read : cell next.slots i = singletonRow i key := by
      change Cpp.get next.slots (slotOffset i) = _
      rw [Cpp.get_eq, slotOffset_nat _ (by rwa [indexNat]), indexNat]
      simp [next]
    have nonnull : i ≠ endIndex := by
      intro same
      rw [same] at indexNat
      change 2 ^ 64 - 1 = arena.slots.size at indexNat
      omega
    have layout : Layout next.slots i (.node .empty key .empty) [i.toNat] := by
      refine .node (leftSlots := []) (rightSlots := []) (by rw [indexNat, nextSize]; omega) nonnull ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by simp) (by simp) (by simp)
      · simp [read, singletonRow]
      · simp [read, singletonRow, Tree.height]
      · simp [read, singletonRow, Tree.size]
      · simp [read, cachedFirst, singletonRow]
      · simp [read, cachedLast, singletonRow]
      · rw [read]
        exact .empty
      · rw [read]
        exact .empty
    refine ⟨i, next, [], start + 6, generated_allocate_append_run arena key headEq fits start,
      le_rfl, by rw [nextSize]; omega, layout, .empty, ⟨rfl, by rw [nextSize]; omega, ?_⟩,
      Or.inl indexNat, by simp [nextSize]⟩
    intro j allocated _
    change Cpp.get next.slots (slotOffset j) = Cpp.get arena.slots (slotOffset j)
    rw [Cpp.get_eq, Cpp.get_eq, slotOffset_nat _ (by omega)]
    simp [next, getElem!_pos, allocated, Nat.lt_succ_of_lt allocated, Array.getElem_push_lt]
  | @cons _ rest allocated nonnull _ tail apart =>
    let i := head
    let changed := putCell arena i (singletonRow i key)
    let next : cp.TreeSet K := { changed with free_head := (cell arena.slots i).left }
    have indexFits : i.toNat < 2 ^ 63 := by dsimp only [i]; omega
    have inside : (slotOffset i).toNat < arena.slots.size := by
      rw [slotOffset_nat _ indexFits]
      exact allocated
    have read : cell next.slots i = singletonRow i key := cell_written _ _ _ inside
    have sameSize : next.slots.size = arena.slots.size := putCell_size ..
    have layout : Layout next.slots i (.node .empty key .empty) [i.toNat] := by
      refine .node (leftSlots := []) (rightSlots := []) (by rwa [sameSize]) nonnull ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by simp) (by simp) (by simp)
      · simp [read, singletonRow]
      · simp [read, singletonRow, Tree.height]
      · simp [read, singletonRow, Tree.size]
      · simp [read, cachedFirst, singletonRow]
      · simp [read, cachedLast, singletonRow]
      · rw [read]
        exact .empty
      · rw [read]
        exact .empty
    have run : (cp.TreeSet.allocate arena key).run start = some ((i, next), start + 4) := by
      have reuse := generated_allocate_reuse_run arena key (by rwa [headEq])
        (by rwa [headEq]) start
      simpa only [headEq] using reuse
    refine ⟨i, next, rest, start + 4, run, by omega, by rw [sameSize]; omega, layout,
      tail.putCell_away i _ allocated (by omega) apart, ⟨rfl, Nat.le_of_eq sameSize.symm, ?_⟩,
      Or.inr (by simp [i]), by simp [sameSize, i]⟩
    intro j range notTouched
    exact cell_put_away _ _ _ _ allocated range (by omega) (fun equal => notTouched (by simp [equal]))


theorem Pending.disjoint_free {K : Type} [Inhabited K] {arena : cp.TreeSet K} {i : UInt64}
    {left right : Tree K} {key : K} {ls rs free : List Nat} {head : UInt64}
    (pending : Pending arena i left key right ls rs) (chain : FreeChain arena.slots head free) :
    List.Disjoint free (i.toNat :: (ls ++ rs)) := by
  intro n vacant touched
  rcases List.mem_cons.mp touched with rfl | below
  · have missing := chain.empty_key i vacant
    rw [pending.value] at missing
    contradiction
  · rcases List.mem_append.mp below with wl | wr
    · exact pending.leftLayout.disjoint_free chain wl vacant
    · exact pending.rightLayout.disjoint_free chain wr vacant

end Proofs.Cpp.TreeSet
