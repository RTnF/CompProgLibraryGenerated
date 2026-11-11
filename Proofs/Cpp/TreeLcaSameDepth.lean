import Proofs.Cpp.Gen.TreeLcaSameDepth
import Proofs.Cpp.Lib.Basic

/-! # `tree_lca_same_depth` (library/tree/tree_lca_same_depth.hpp)

The first meeting point of the paths from two vertices of the same depth, from a doubling table;
`O(log depth)` steps. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeLcaSameDepth

/-- `w` is where the paths from `u` and `v` along `f` first meet: `f^a(u) = f^a(v) = w` and they differ before. -/
def FirstMeet (f : Int → Int) (u v w : Int) : Prop :=
  ∃ a : Nat, f^[a] u = w ∧ f^[a] v = w ∧ ∀ s, s < a → f^[s] u ≠ f^[s] v

/-- The table rows used: `anc[k][x] = f^(2^k)(x)` for `k = 0` and for every `k` with `2^k <= depth`. -/
def TabLca (anc : Array (Array Int)) (f : Int → Int) (n : Int) (depth : Nat) : Prop :=
  ∀ k : Nat, (k = 0 ∨ 2 ^ k ≤ depth) → ∀ x : Int, 0 ≤ x → x < n → (anc[k]!)[x.toNat]! = f^[2 ^ k] x

/-- The descent invariant at level `k` for the pair `(u1, v1)`, in the form `mvcgen` presents it. -/
abbrev Inv2 (f : Int → Int) (n u v : Int) (D : Nat) (u1 v1 k : Int) (s t0 : Nat) : Prop :=
  -1 ≤ k ∧ (k < 0 ∨ k = 0 ∨ 2 ^ k.toNat ≤ D) ∧ ¬u1 = v1 ∧ 0 ≤ u1 ∧ u1 < n ∧ 0 ≤ v1 ∧ v1 < n ∧
    f^[2 ^ (k + 1).toNat] u1 = f^[2 ^ (k + 1).toNat] v1 ∧
    (∃ a, u1 = f^[a] u ∧ v1 = f^[a] v ∧ ∀ s ≤ a, ¬f^[s] u = f^[s] v) ∧
    (s : Int) + k ≤ (t0 : Int) + 2 + 2 * (bitWidth D : Int)

theorem tab_get (anc : Array (Array Int)) (f : Int → Int) (n : Int) (D : Nat) (htab : TabLca anc f n D)
    (k x : Int) (hk : 0 ≤ k) (hlev : k < 0 ∨ k = 0 ∨ 2 ^ k.toNat ≤ D) (hx : 0 ≤ x ∧ x < n) :
    get (get anc k) x = f^[2 ^ k.toNat] x := by
  have : k.toNat = 0 ∨ 2 ^ k.toNat ≤ D := by omega
  exact htab k.toNat this x hx.1 hx.2

theorem lev_down (k : Int) (D : Nat) (hk : 0 ≤ k) (hlev : k < 0 ∨ k = 0 ∨ 2 ^ k.toNat ≤ D) :
    k < 1 ∨ k - 1 = 0 ∨ 2 ^ (k.toNat - 1) ≤ D := by
  rcases hlev with h | h | h
  · omega
  · omega
  · right; right; exact Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega)) h

theorem pow_succ_toNat (k : Int) (hk : 0 ≤ k) : 2 ^ (k + 1).toNat = 2 ^ k.toNat + 2 ^ k.toNat := by
  rw [show (k + 1).toNat = k.toNat + 1 by omega, Nat.pow_succ]; omega

theorem step_diff (anc : Array (Array Int)) (f : Int → Int) (n u v : Int) (D : Nat)
    (hf : ∀ x, 0 ≤ x → x < n → 0 ≤ f x ∧ f x < n) (htab : TabLca anc f n D)
    (u1 v1 k : Int) (s t0 : Nat) (h : Inv2 f n u v D u1 v1 k s t0) (hk : 0 ≤ k)
    (hne : ¬get (get anc k) u1 = get (get anc k) v1) :
    (0 ≤ k ∧ (k < 1 ∨ k - 1 = 0 ∨ 2 ^ (k.toNat - 1) ≤ D) ∧
      ¬get (get anc k) u1 = get (get anc k) v1 ∧ 0 ≤ get (get anc k) u1 ∧ get (get anc k) u1 < n ∧
      0 ≤ get (get anc k) v1 ∧ get (get anc k) v1 < n ∧
      f^[2 ^ k.toNat] (get (get anc k) u1) = f^[2 ^ k.toNat] (get (get anc k) v1) ∧
      (∃ a, get (get anc k) u1 = f^[a] u ∧ get (get anc k) v1 = f^[a] v ∧ ∀ s ≤ a, ¬f^[s] u = f^[s] v) ∧
      (s : Int) + k ≤ (t0 : Int) + 2 + 2 * (bitWidth D : Int)) ∧ 0 < k + 1 := by
  obtain ⟨-, hlev, -, hu0, hun, hv0, hvn, hm, ⟨a, ha, hb, hnot⟩, hc⟩ := h
  have gu := tab_get anc f n D htab k u1 hk hlev ⟨hu0, hun⟩
  have gv := tab_get anc f n D htab k v1 hk hlev ⟨hv0, hvn⟩
  have ru := iter_range f n hf (2 ^ k.toNat) u1 hu0 hun
  have rv := iter_range f n hf (2 ^ k.toNat) v1 hv0 hvn
  rw [gu, gv] at hne ⊢
  rw [pow_succ_toNat k hk, iter_add, iter_add] at hm
  refine ⟨⟨hk, lev_down k D hk hlev, hne, ru.1, ru.2, rv.1, rv.2, hm, ⟨2 ^ k.toNat + a, ?_, ?_, ?_⟩, hc⟩, by omega⟩
  · rw [iter_add, ha]
  · rw [iter_add, hb]
  · intro s' hs' hmet
    apply hne
    have := met_mono f u v hmet hs'
    rw [iter_add, iter_add, ← ha, ← hb] at this
    exact this

theorem step_same (anc : Array (Array Int)) (f : Int → Int) (n u v : Int) (D : Nat)
    (hf : ∀ x, 0 ≤ x → x < n → 0 ≤ f x ∧ f x < n) (htab : TabLca anc f n D)
    (u1 v1 k : Int) (s t0 : Nat) (h : Inv2 f n u v D u1 v1 k s t0) (hk : 0 ≤ k)
    (heq : get (get anc k) u1 = get (get anc k) v1) :
    (0 ≤ k ∧ (k < 1 ∨ k - 1 = 0 ∨ 2 ^ (k.toNat - 1) ≤ D) ∧ ¬u1 = v1 ∧ 0 ≤ u1 ∧ u1 < n ∧ 0 ≤ v1 ∧ v1 < n ∧
      f^[2 ^ k.toNat] u1 = f^[2 ^ k.toNat] v1 ∧
      (∃ a, u1 = f^[a] u ∧ v1 = f^[a] v ∧ ∀ s ≤ a, ¬f^[s] u = f^[s] v) ∧
      (s : Int) + k ≤ (t0 : Int) + 2 + 2 * (bitWidth D : Int)) ∧ 0 < k + 1 := by
  obtain ⟨-, hlev, hne0, hu0, hun, hv0, hvn, -, hex, hc⟩ := h
  have gu := tab_get anc f n D htab k u1 hk hlev ⟨hu0, hun⟩
  have gv := tab_get anc f n D htab k v1 hk hlev ⟨hv0, hvn⟩
  rw [gu, gv] at heq
  exact ⟨⟨hk, lev_down k D hk hlev, hne0, hu0, hun, hv0, hvn, heq, hex, hc⟩, by omega⟩

/-- `tree_lca_same_depth(anc, u, v, D)`: when the paths from `u` and `v` along `f` (a map of `[0, n)` into itself, `anc`
its doubling table) meet after `D` steps, the result is their first meeting point (`FirstMeet`); at most
`2 bitWidth D + 4` steps (`O(log D)`). For two vertices of depth `D` in a rooted tree (`f` the parent map, the root
its own parent) both paths reach the root after `D` steps, and the first meeting point is the lowest common ancestor. -/
theorem tree_lca_same_depth_spec (anc : Array (Array Int)) (f : Int → Int) (n u v : Int) (D : Nat)
    (hf : ∀ x, 0 ≤ x → x < n → 0 ≤ f x ∧ f x < n) (hu : 0 ≤ u ∧ u < n) (hv : 0 ≤ v ∧ v < n)
    (hD : D < 2 ^ 30) (hmeet : f^[D] u = f^[D] v) (htab : TabLca anc f n D) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.tree_lca_same_depth anc u v D
    ⦃⇓ r c => ⌜FirstMeet f u v r ∧ c ≤ t0 + 4 + 2 * bitWidth D⌝⦄ := by
  have hbw : bitWidth D ≤ 30 := bitWidth_lt_pow D 30 hD
  clear hD
  mvcgen [cp.tree_lca_same_depth]
  case vc1.inv =>
    exact ⟨fun ⟨top, p⟩ c => ⌜0 ≤ top ∧ p = 2 ^ top.toNat ∧ top.toNat ≤ bitWidth D ∧ (top = 0 ∨ 2 ^ top.toNat ≤ D) ∧
             c = t0 + 1 + top.toNat⌝,
           fun ⟨top, p⟩ c => ⌜0 ≤ top ∧ p = 2 ^ top.toNat ∧ top.toNat ≤ bitWidth D ∧ (top = 0 ∨ 2 ^ top.toNat ≤ D) ∧
             D < 2 ^ (top.toNat + 1) ∧ c = t0 + 2 + top.toNat⌝,
           fun ⟨top, _⟩ => bitWidth D - top.toNat⟩
  case vc6.inv =>
    exact ⟨fun ⟨u', v', k⟩ c => ⌜-1 ≤ k ∧ (k < 0 ∨ k = 0 ∨ 2 ^ k.toNat ≤ D) ∧ u' ≠ v' ∧
             0 ≤ u' ∧ u' < n ∧ 0 ≤ v' ∧ v' < n ∧ f^[2 ^ (k + 1).toNat] u' = f^[2 ^ (k + 1).toNat] v' ∧
             (∃ a : Nat, u' = f^[a] u ∧ v' = f^[a] v ∧ ∀ s, s ≤ a → f^[s] u ≠ f^[s] v) ∧
             (c : Int) + k ≤ t0 + 2 + 2 * bitWidth D⌝,
           fun ⟨u', v', _⟩ c => ⌜u' ≠ v' ∧ 0 ≤ u' ∧ u' < n ∧ f u' = f v' ∧
             (∃ a : Nat, u' = f^[a] u ∧ v' = f^[a] v ∧ ∀ s, s ≤ a → f^[s] u ≠ f^[s] v) ∧
             c ≤ t0 + 4 + 2 * bitWidth D⌝,
           fun ⟨_, _, k⟩ => (k + 1).toNat⟩
  all_goals simp +zetaDelta [fuel] at *
  -- the first loop: `top` is the largest level with `2^top <= max(D, 1)`
  · obtain ⟨h0, hp, hb, hl, hc⟩ := ‹(0 : Int) ≤ _ ∧ _›
    refine ⟨h0, hp, hb, hl, ?_, by omega⟩
    have := ‹(D : Int) < _›
    rw [hp] at this
    rw [Nat.pow_succ]; exact_mod_cast this
  · obtain ⟨h0, hp, hb, hl, hc⟩ := ‹(0 : Int) ≤ _ ∧ _›
    have hle := ‹_ * 2 ≤ (D : Int)›
    rw [hp] at hle
    have hle' : 2 ^ (‹Int × Int›.1.toNat + 1) ≤ D := by rw [Nat.pow_succ]; exact_mod_cast hle
    have := lt_bitWidth hle'
    have e : (‹Int × Int›.1 + 1).toNat = ‹Int × Int›.1.toNat + 1 := by omega
    refine ⟨⟨by omega, by rw [hp, e, Int.pow_succ], by omega, Or.inr (by rw [e]; exact hle'), by omega⟩, by omega⟩
  · omega
  · obtain ⟨h0, hp, hb, hl, hD, hc⟩ := ‹(0 : Int) ≤ _ ∧ _›
    subst ‹u = v›
    exact ⟨⟨0, rfl, rfl, fun s hs => absurd hs (by omega)⟩, by omega⟩
  -- the descent
  · obtain ⟨hk1, -, hne0, hu0, hun, -, -, hm, hex, hc⟩ := ‹(-1 : Int) ≤ _ ∧ _›
    have e : (‹Int × Int × Int›.2.2 + 1).toNat = 0 := by omega
    rw [e] at hm
    exact ⟨hne0, hu0, hun, hm, hex, by omega⟩
  · exact step_diff anc f n u v D hf htab _ _ _ _ _ ‹_› ‹_› ‹_›
  · exact step_same anc f n u v D hf htab _ _ _ _ _ ‹_› ‹_› ‹_›
  · obtain ⟨h0, hp, hb, hl, hD, hc⟩ := ‹(0 : Int) ≤ _ ∧ _›
    have e : (‹Int × Int›.1 + 1).toNat = ‹Int × Int›.1.toNat + 1 := by omega
    refine ⟨⟨by omega, by omega, ‹_›, hu.1, hu.2, hv.1, hv.2, ?_, ⟨0, rfl, rfl, fun s hs => ?_⟩, by omega⟩, by omega⟩
    · rw [e]; exact met_mono f u v hmeet (by omega)
    · rw [show s = 0 by omega]; exact ‹¬u = v›
  · obtain ⟨hne0, hu0, hun, hm, ⟨a, ha, hb, hnot⟩, hc⟩ := ‹¬(_ : Int) = _ ∧ _›
    have g := tab_get anc f n D htab 0 _ (by omega) (by omega) ⟨hu0, hun⟩
    simp only [Int.toNat_zero, Nat.pow_zero] at g
    refine ⟨⟨a + 1, ?_, ?_, fun s hs => hnot s (by omega)⟩, hc⟩
    · rw [g, Nat.add_comm, iter_add, ← ha]
    · have : ∀ x, f^[1] x = f x := fun _ => rfl
      rw [g, this, hm, Nat.add_comm, iter_add, ← hb]; rfl

end Proofs.Cpp.TreeLcaSameDepth
