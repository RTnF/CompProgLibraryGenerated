import Proofs.LazySegRange
import Proofs.LazySegAncLeaf

namespace Proofs.LazySegApplyMath
open Proofs.SegTreeMath Proofs.LazySegMath
open Proofs.LazySegChmin (chminMon mi)
open Proofs.LazySegRange
open Proofs.LazySegArith

open Classical in
/-- Applying the action to the node `k` whose block of leaves is `[b, b + 2^j)`. -/
theorem apply_block (nn : Nat) (node lz : List Int) (f : Int) (B : Nat → Prop) (k j b : Nat) (lfOld lfNew : Nat → Int)
    (hk1 : 1 ≤ k) (hk2 : k < 2 * nn) (hlen : lz.length = nn) (hnode : node.length = 2 * nn)
    (hV : AllV chminMon.toMon node) (hF : AllF chminMon lz) (hf : chminMon.Fv f) (hLeaf : LeafV chminMon lfOld nn)
    (hCl : Cl chminMon lz k) (hD : ∀ d, Anc d k → ¬ B d)
    (hSA : ∀ d, 1 ≤ d → d < 2 * nn → Anc k d → d ≠ k → B d)
    (hanc : ∀ x, nn ≤ x → x < 2 * nn → (Anc x k ↔ b ≤ x ∧ x < b + 2 ^ j))
    (hnew : ∀ x, nn ≤ x → x < 2 * nn → lfNew x = if (b ≤ x ∧ x < b + 2 ^ j) then chminMon.mp f (lfOld x) else lfOld x)
    (hE : Ext chminMon lfOld nn node lz B) :
    Ext chminMon lfNew nn (applyNode chminMon node k f) (alz chminMon nn lz k f) B := by
  have hG := G_clean chminMon lz hF k hCl
  have h1 := ext_apply chminMon lfOld (fun x => if Anc x k then chminMon.mp f (lfOld x) else lfOld x) nn node lz B k f
    hk1 hk2 hlen hnode hV hF hf hLeaf hG hD (fun x hx => by simp [hx]) (fun x hx => by simp [hx]) hE
  have h2 := ext_weaken chminMon _ nn _ _ _ B (fun d hd1 hd2 hb => by
    rcases hb with hb | ⟨ha, hne⟩
    · exact hb
    · exact hSA d hd1 hd2 ha hne) h1
  refine ext_congr chminMon _ lfNew nn _ _ _ (fun x hx1 hx2 => ?_) h2
  rw [hnew x hx1 hx2]
  by_cases hx : Anc x k
  · have := (hanc x hx1 hx2).mp hx
    simp [hx, this]
  · have : ¬ (b ≤ x ∧ x < b + 2 ^ j) := fun h => hx ((hanc x hx1 hx2).mpr h)
    simp [hx, this]

theorem floor_pred (m q : Nat) (hq : 0 < q) (h : m % q ≠ 0) : (m - 1) / q = m / q := by
  have h1 := Nat.div_add_mod m q
  have h2 := Nat.mod_lt m hq
  have hm : 1 ≤ m % q := by omega
  have e : m - 1 = q * (m / q) + (m % q - 1) := by omega
  have h3 : (m % q - 1) / q = 0 := Nat.div_eq_of_lt (by omega)
  rw [e, Nat.mul_add_div hq, h3]
  simp

theorem hD_block (nn h l0 r0 k j b : Nat) (hN : nn = 2 ^ h) (hl : nn ≤ l0 ∧ l0 ≤ 2 * nn) (hr : nn ≤ r0 ∧ r0 ≤ 2 * nn)
    (hb1 : l0 ≤ b) (hb2 : b + 2 ^ j ≤ r0)
    (hanc : ∀ x, nn ≤ x → x < 2 * nn → (Anc x k ↔ b ≤ x ∧ x < b + 2 ^ j)) :
    ∀ d, Anc d k → ¬ S2 h l0 r0 0 d := by
  have hnn : 0 < nn := by rw [hN]; exact Nat.two_pow_pos h
  rintro d hdk ⟨u, hu0, huh, (⟨hm, rfl⟩ | ⟨hm, rfl⟩)⟩
  · have hpos : 0 < 2 ^ u := Nat.two_pow_pos u
    have hdvd : l0 ≠ nn := by
      intro e; apply hm; rw [e, hN]; exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 huh)
    have hx : Anc (l0 - 1) (l0 / 2 ^ u) := ⟨u, (floor_pred l0 _ hpos hm).symm⟩
    have hk := anc_trans _ _ _ hx hdk
    have := (hanc (l0 - 1) (by omega) (by omega)).mp hk
    omega
  · have hpos : 0 < 2 ^ u := Nat.two_pow_pos u
    have hne : r0 ≠ 2 * nn := by
      intro e; apply hm; rw [e, hN, ← Nat.pow_succ']; exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega))
    have hx : Anc r0 ((r0 - 1) / 2 ^ u) := ⟨u, (floor_pred r0 _ hpos hm)⟩
    have hk := anc_trans _ _ _ hx hdk
    have := (hanc r0 (by omega) (by omega)).mp hk
    omega

theorem anc_left_mem (nn h l0 r0 j : Nat) (hN : nn = 2 ^ h) (hl : nn ≤ l0 ∧ l0 ≤ 2 * nn)
    (hodd : ceilDiv l0 (2 ^ j) % 2 = 1) :
    ∀ d, 1 ≤ d → Anc (ceilDiv l0 (2 ^ j)) d → d ≠ ceilDiv l0 (2 ^ j) → S2 h l0 r0 0 d := by
  rintro d hd1 ⟨t, ht⟩ hne
  have ht0 : 1 ≤ t := by
    apply Classical.byContradiction
    intro hc
    have : t = 0 := by omega
    subst this
    simp at ht
    exact hne ht
  obtain ⟨hm, he⟩ := left_anc l0 j t ht0 hodd
  refine ⟨j + t, by omega, ?_, Or.inl ⟨hm, by rw [ht]; exact he⟩⟩
  apply Classical.byContradiction
  intro hc
  have hpow : 2 ^ (h + 1) ≤ 2 ^ (j + t) := Nat.pow_le_pow_right (by decide) (by omega)
  have hlt : l0 < 2 ^ (j + t) := by
    by_cases hq : j + t = h + 1
    · have hne' : l0 ≠ 2 * nn := by
        intro e; apply hm
        rw [e, hN, ← Nat.pow_succ', hq]
        exact Nat.mod_self _
      rw [hq, Nat.pow_succ']; omega
    · have hp2 : 2 ^ (h + 2) ≤ 2 ^ (j + t) := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.pow_succ' (n := h + 1), Nat.pow_succ' (n := h)] at hp2
      omega
  rw [ht, he, Nat.div_eq_of_lt hlt] at hd1
  omega

theorem anc_right_mem (nn h l0 r0 j : Nat) (hN : nn = 2 ^ h) (hr : nn ≤ r0 ∧ r0 ≤ 2 * nn)
    (hodd : (r0 / 2 ^ j) % 2 = 1) :
    ∀ d, 1 ≤ d → Anc (r0 / 2 ^ j - 1) d → d ≠ r0 / 2 ^ j - 1 → S2 h l0 r0 0 d := by
  rintro d hd1 ⟨t, ht⟩ hne
  have ht0 : 1 ≤ t := by
    apply Classical.byContradiction
    intro hc
    have : t = 0 := by omega
    subst this
    simp at ht
    exact hne ht
  obtain ⟨hm, he⟩ := right_anc r0 j t ht0 hodd
  refine ⟨j + t, by omega, ?_, Or.inr ⟨hm, by rw [ht]; exact he⟩⟩
  apply Classical.byContradiction
  intro hc
  have hpow : 2 ^ (h + 1) ≤ 2 ^ (j + t) := Nat.pow_le_pow_right (by decide) (by omega)
  have hlt : r0 - 1 < 2 ^ (j + t) := by
    rw [Nat.pow_succ'] at hpow; omega
  rw [ht, he, Nat.div_eq_of_lt hlt] at hd1
  omega

end Proofs.LazySegApplyMath
