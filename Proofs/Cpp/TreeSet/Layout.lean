import Proofs.Cpp.Gen.TreeSet
import Proofs.Cpp.TreeSet.Queries
import Proofs.Cpp.Lib.Basic
import Mathlib.Data.List.Nodup

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeSet

def endIndex : UInt64 := ~~~0

def cell {K : Type} [Inhabited K] (storage : Array (cp.TreeSet_Slot K)) (index : UInt64) :
    cp.TreeSet_Slot K := Cpp.get storage (Cpp.toSigned 64 index.toNat)

def cachedFirst {K : Type} [Inhabited K] (storage : Array (cp.TreeSet_Slot K)) (index child : UInt64) :
    UInt64 := if child = endIndex then index else (cell storage child).first

def cachedLast {K : Type} [Inhabited K] (storage : Array (cp.TreeSet_Slot K)) (index child : UInt64) :
    UInt64 := if child = endIndex then index else (cell storage child).last

inductive Layout {K : Type} [Inhabited K] (storage : Array (cp.TreeSet_Slot K)) :
    UInt64 → Tree K → List Nat → Prop
  | empty : Layout storage endIndex .empty []
  | node {i : UInt64} {key : K} {left right : Tree K} {leftSlots rightSlots : List Nat}
      (allocated : i.toNat < storage.size) (notEnd : i ≠ endIndex)
      (value : (cell storage i).key = some key)
      (height : (cell storage i).height.toNat = (Tree.node left key right).height)
      (size : (cell storage i).size_.toNat = (Tree.node left key right).size)
      (first : (cell storage i).first = cachedFirst storage i (cell storage i).left)
      (last : (cell storage i).last = cachedLast storage i (cell storage i).right)
      (l : Layout storage (cell storage i).left left leftSlots)
      (r : Layout storage (cell storage i).right right rightSlots)
      (newLeft : i.toNat ∉ leftSlots) (newRight : i.toNat ∉ rightSlots)
      (disjoint : List.Disjoint leftSlots rightSlots) :
      Layout storage i (.node left key right) (i.toNat :: (leftSlots ++ rightSlots))

theorem Layout.index_used {K : Type} [Inhabited K] {storage : Array (cp.TreeSet_Slot K)}
    {i : UInt64} {tree : Tree K} {slots : List Nat} (layout : Layout storage i tree slots) :
    i = endIndex ∨ i.toNat ∈ slots := by
  cases layout with
  | empty => exact Or.inl rfl
  | node => exact Or.inr (by simp)

theorem Layout.node_count {K : Type} [Inhabited K] {storage : Array (cp.TreeSet_Slot K)}
    {i : UInt64} {tree : Tree K} {slots : List Nat} (layout : Layout storage i tree slots) :
    slots.length = tree.size := by
  induction layout with
  | empty => rfl
  | node _ _ _ _ _ _ _ _ _ _ _ _ il ir => simp [Tree.size, il, ir]

theorem Layout.distinct {K : Type} [Inhabited K] {storage : Array (cp.TreeSet_Slot K)}
    {i : UInt64} {tree : Tree K} {slots : List Nat} (layout : Layout storage i tree slots) :
    slots.Nodup := by
  induction layout with
  | empty => exact List.nodup_nil
  | node _ _ _ _ _ _ _ _ _ freshL freshR disjoint il ir =>
    refine List.nodup_cons.mpr ⟨by simp [freshL, freshR], List.nodup_append.mpr ⟨il, ir, ?_⟩⟩
    intro a ha b hb eq
    subst b
    exact disjoint ha hb

theorem Layout.in_range {K : Type} [Inhabited K] {storage : Array (cp.TreeSet_Slot K)}
    {i : UInt64} {tree : Tree K} {slots : List Nat} (layout : Layout storage i tree slots) :
    ∀ j ∈ slots, j < storage.size := by
  induction layout with
  | empty => simp
  | node allocated _ _ _ _ _ _ _ _ _ _ _ il ir =>
    intro j present
    rcases List.mem_cons.mp present with rfl | below
    · exact allocated
    · exact (List.mem_append.mp below).elim (il j) (ir j)

theorem Layout.capacity {K : Type} [Inhabited K] {storage : Array (cp.TreeSet_Slot K)}
    {i : UInt64} {tree : Tree K} {slots : List Nat} (layout : Layout storage i tree slots) :
    tree.size ≤ storage.size := by
  rw [← layout.node_count, ← List.length_range (n := storage.size)]
  exact layout.distinct.length_le_of_subset (fun j hj => List.mem_range.mpr (layout.in_range j hj))

def modelSize {K : Type} [Inhabited K] (arena : cp.TreeSet K) (index : UInt64) : UInt64 :=
  if index = endIndex then 0 else (cell arena.slots index).size_

def modelHeight {K : Type} [Inhabited K] (arena : cp.TreeSet K) (index : UInt64) : UInt64 :=
  if index = endIndex then 0 else (cell arena.slots index).height

theorem generated_size_run {K : Type} [Inhabited K] (arena : cp.TreeSet K) (index : UInt64)
    (clock : Nat) : (cp.TreeSet.subtree_size arena index).run clock =
      some (modelSize arena index, clock + 2) := by
  by_cases atEnd : index = endIndex <;>
    simp [cp.TreeSet.subtree_size, cp.TreeSet.none, Cpp.tick, StateT.run_bind,
      modelSize, cell, endIndex] at atEnd ⊢

theorem generated_height_run {K : Type} [Inhabited K] (arena : cp.TreeSet K) (index : UInt64)
    (clock : Nat) : (cp.TreeSet.subtree_height arena index).run clock =
      some (modelHeight arena index, clock + 2) := by
  by_cases atEnd : index = endIndex <;>
    simp [cp.TreeSet.subtree_height, cp.TreeSet.none, Cpp.tick, StateT.run_bind,
      modelHeight, cell, endIndex] at atEnd ⊢

theorem Layout.model_size {K : Type} [Inhabited K] {arena : cp.TreeSet K} {index : UInt64}
    {tree : Tree K} {slots : List Nat} (layout : Layout arena.slots index tree slots) :
    (modelSize arena index).toNat = tree.size := by
  cases layout with
  | empty => simp [modelSize, Tree.size]
  | node _ notEnd _ _ sizes _ _ _ _ _ _ _ => simp [modelSize, notEnd, sizes]

theorem Layout.model_height {K : Type} [Inhabited K] {arena : cp.TreeSet K} {index : UInt64}
    {tree : Tree K} {slots : List Nat} (layout : Layout arena.slots index tree slots) :
    (modelHeight arena index).toNat = tree.height := by
  cases layout with
  | empty => simp [modelHeight, Tree.height]
  | node _ notEnd _ heights _ _ _ _ _ _ _ _ => simp [modelHeight, notEnd, heights]

theorem generated_init {K : Type} (clock : Nat) :
    (cp.TreeSet.init (T := K)).run clock = some (⟨List.toArray [], endIndex, endIndex⟩, clock + 3) := rfl

end Proofs.Cpp.TreeSet
