import Proofs.Cpp.TreeSet.Layout

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeSet

theorem Layout.frame {K : Type} [Inhabited K]
    {before after : Array (cp.TreeSet_Slot K)} {i : UInt64} {t : Tree K}
    {slots : List Nat} (layout : Layout before i t slots)
    (allocated : ∀ j ∈ slots, j < after.size)
    (unchanged : ∀ j : UInt64, j.toNat ∈ slots → cell before j = cell after j) :
    Layout after i t slots := by
  induction layout with
  | empty => exact .empty
  | @node i key left right ls rs _ nonnull value height size first last l r fl fr sep il ir =>
    have row := unchanged i (by simp)
    have leftCache : cachedFirst before i (cell before i).left = cachedFirst after i (cell before i).left := by
      rcases l.index_used with endCode | usedCode
      · simp [cachedFirst, endCode]
      · have child := unchanged (cell before i).left (by simp [usedCode])
        simp [cachedFirst, child]
    have rightCache : cachedLast before i (cell before i).right = cachedLast after i (cell before i).right := by
      rcases r.index_used with endCode | usedCode
      · simp [cachedLast, endCode]
      · have child := unchanged (cell before i).right (by simp [usedCode])
        simp [cachedLast, child]
    rw [leftCache] at first
    rw [rightCache] at last
    rw [row] at value height size first last
    have ll := il (fun j h => allocated j (by simp [h])) (fun j h => unchanged j (by simp [h]))
    have rr := ir (fun j h => allocated j (by simp [h])) (fun j h => unchanged j (by simp [h]))
    rw [row] at ll rr
    exact .node (allocated i.toNat (by simp)) nonnull value height size first last ll rr fl fr sep

theorem Layout.root_key {K : Type} [Inhabited K]
    {storage : Array (cp.TreeSet_Slot K)} {i : UInt64} {k : K} {l r : Tree K}
    {slots : List Nat} (layout : Layout storage i (.node l k r) slots) :
    i ≠ endIndex ∧ (cell storage i).key = some k := by
  cases layout
  exact ⟨‹i ≠ endIndex›, ‹(cell storage i).key = some k›⟩

end Proofs.Cpp.TreeSet

namespace Proofs.Cpp.TreeSet

structure Pending {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i : UInt64)
    (left : Tree K) (key : K) (right : Tree K) (ls rs : List Nat) : Prop where
  allocated : i.toNat < arena.slots.size
  nonnull : i ≠ endIndex
  value : (cell arena.slots i).key = some key
  leftLayout : Layout arena.slots (cell arena.slots i).left left ls
  rightLayout : Layout arena.slots (cell arena.slots i).right right rs
  leftApart : i.toNat ∉ ls
  rightApart : i.toNat ∉ rs
  disjoint : List.Disjoint ls rs

theorem layout_pending {K : Type} [Inhabited K] {arena : cp.TreeSet K}
    {i : UInt64} {left right : Tree K} {key : K} {used : List Nat}
    (layout : Layout arena.slots i (.node left key right) used) :
    ∃ ls rs, used = i.toNat :: (ls ++ rs) ∧ Pending arena i left key right ls rs := by
  cases layout with
  | node allocated nonnull value _ _ _ _ ll rr la ra distinct =>
    exact ⟨_, _, rfl, ⟨allocated, nonnull, value, ll, rr, la, ra, distinct⟩⟩

end Proofs.Cpp.TreeSet
