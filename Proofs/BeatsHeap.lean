import Proofs.BeatsBuild
namespace Proofs.BeatsModel

/-- `j` is `c` or a descendant of `c` in the heap numbering (children of `k` are `2k+1`, `2k+2`). -/
inductive descN (c : Nat) : Nat → Prop
  | self : descN c c
  | step (j : Nat) : c < j → descN c ((j - 1) / 2) → descN c j

theorem descN_ge (k j : Nat) (h : descN k j) : k ≤ j := by
  induction h with
  | self => omega
  | step j h1 _ _ => omega

theorem descN_child_aux (k c j : Nat) (hc : (c - 1) / 2 = k) (hck : k < c) (h : descN c j) : descN k j := by
  induction h with
  | self => exact descN.step _ hck (by rw [hc]; exact descN.self)
  | step j h1 h2 ih => exact descN.step j (by omega) ih

theorem descN_child (k j : Nat) (h : descN (2 * k + 1) j) : descN k j :=
  descN_child_aux k (2 * k + 1) j (by omega) (by omega) h

theorem descN_child2 (k j : Nat) (h : descN (2 * k + 2) j) : descN k j :=
  descN_child_aux k (2 * k + 2) j (by omega) (by omega) h

theorem descN_sib (c1 c2 : Nat) (hp1 : 0 < c1) (hp2 : 0 < c2) (hne : c1 ≠ c2) (hp : (c1 - 1) / 2 = (c2 - 1) / 2) (j : Nat)
    (h1 : descN c1 j) (h2 : descN c2 j) : False := by
  induction h1 with
  | self =>
    cases h2 with
    | self => exact hne rfl
    | step _ b1 b2 =>
      have := descN_ge _ _ b2
      omega
  | step j a1 a2 ih =>
    cases h2 with
    | self =>
      have := descN_ge _ _ a2
      omega
    | step _ b1 b2 => exact ih b2

theorem descN_disjoint (k j : Nat) (h1 : descN (2 * k + 1) j) (h2 : descN (2 * k + 2) j) : False :=
  descN_sib (2 * k + 1) (2 * k + 2) (by omega) (by omega) (by omega) (by omega) j h1 h2

theorem descN_self (k : Nat) : descN k k := descN.self

/-- The heap cell of node `j` of the subtree `t` rooted at heap index `k`, if `j` is in it. -/
def sub : BT → Nat → Nat → Option (Nd × Tag)
  | .leaf nd, k, j => if j = k then some (nd, noTag) else none
  | .node nd tg l r, k, j =>
    if j = k then some (nd, tg)
    else match sub l (2 * k + 1) j with
      | some v => some v
      | none => sub r (2 * k + 2) j

theorem sub_desc : ∀ (t : BT) (k j : Nat) (v : Nd × Tag), sub t k j = some v → descN k j
  | .leaf nd, k, j, v, h => by
    unfold sub at h
    split at h
    · rename_i e; subst e; exact descN_self _
    · simp at h
  | .node nd tg l r, k, j, v, h => by
    unfold sub at h
    split at h
    · rename_i e; subst e; exact descN_self _
    · split at h
      · rename_i w hw; exact descN_child k j (sub_desc l _ j w hw)
      · exact descN_child2 k j (sub_desc r _ j v h)

end Proofs.BeatsModel
