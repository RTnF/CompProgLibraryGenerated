import Proofs.Cpp.Gen.CsrBuild
import Proofs.Cpp.Lib.Basic
import Proofs.CsrBuildMath

/-! # `csr_build` (library/graph/csr_build.hpp)

The CSR arrays of an arc list: `head[k]` is the number of arcs whose source is below `k`, and arc `i` is stored at
`head[from[i]]` plus the number of earlier arcs with the same source, so the arcs leaving `u` are
`target[head[u], head[u + 1])` in input order; `2 (n + m) + 1` steps. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.CsrBuildMath

namespace Proofs.Cpp.CsrBuild

/-- The source of arc `j`. -/
def src (fr : Array Int) (j : Nat) : Nat := (fr[j]!).toNat

section
variable (fr : Array Int)

theorem inv1_step (n : Int) (hd : Array Int) (L : Nat) (hF : 0 ≤ fr[L]! ∧ fr[L]! < n)
    (hsz : hd.size = n.toNat + 1) (h0 : hd[0]! = 0)
    (hk : ∀ k, 1 ≤ k → k ≤ n.toNat → hd[k]! = (cnt (src fr) (k - 1) L : Int)) :
    (set hd (get fr L + 1) (get hd (get fr L + 1) + 1))[0]! = 0 ∧
    ∀ k, 1 ≤ k → k ≤ n.toNat →
      (set hd (get fr L + 1) (get hd (get fr L + 1) + 1))[k]! = (cnt (src fr) (k - 1) (L + 1) : Int) := by
  simp only [get_natCast]
  have hidx : (fr[L]! + 1).toNat = (fr[L]!).toNat + 1 := by omega
  have hlt : (fr[L]! + 1).toNat < hd.size := by omega
  refine ⟨?_, fun k hk1 hkn => ?_⟩
  · rw [getElem!_set _ _ _ _ hlt, if_neg (by omega), h0]
  · rw [getElem!_set _ _ _ _ hlt, cnt_succ, hidx]
    by_cases hkf : k = (fr[L]!).toNat + 1
    · subst hkf
      simp only [ite_true, show (fr[L]!).toNat + 1 - 1 = (fr[L]!).toNat by omega]
      rw [get_eq, hidx, hk _ (by omega) (by omega)]
      simp [src]
    · simp only [hkf, ite_false]
      rw [hk k hk1 hkn, if_neg (by simp only [src]; omega)]
      simp

theorem inv2_step (n : Int) (hd : Array Int) (V : Nat) (hV : (V : Int) < n) (m : Nat)
    (hsz : hd.size = n.toNat + 1)
    (hlo : ∀ k, k ≤ V → hd[k]! = (ocnt (src fr) m k : Int))
    (hhi : ∀ k, V < k → k ≤ n.toNat → hd[k]! = (cnt (src fr) (k - 1) m : Int)) :
    (∀ k, k ≤ V + 1 → (set hd ((V : Int) + 1) (get hd ((V : Int) + 1) + get hd V))[k]! = (ocnt (src fr) m k : Int)) ∧
    (∀ k, V + 1 < k → k ≤ n.toNat →
      (set hd ((V : Int) + 1) (get hd ((V : Int) + 1) + get hd V))[k]! = (cnt (src fr) (k - 1) m : Int)) := by
  have hidx : ((V : Int) + 1).toNat = V + 1 := by omega
  have hlt : ((V : Int) + 1).toNat < hd.size := by omega
  refine ⟨fun k hk => ?_, fun k hk hkn => ?_⟩
  · rw [getElem!_set _ _ _ _ hlt, hidx]
    by_cases e : k = V + 1
    · subst e
      simp only [ite_true, get_eq, hidx, Int.toNat_natCast]
      rw [hhi (V + 1) (by omega) (by omega), hlo V (le_refl _), ocnt]
      simp only [Nat.add_sub_cancel]; push_cast; ring
    · simp only [e, ite_false]; exact hlo k (by omega)
  · rw [getElem!_set _ _ _ _ hlt, hidx, if_neg (by omega)]
    exact hhi k (by omega) hkn

theorem inv3_step (ps hd : Array Int) (V : Nat) (n : Int) (hV : (V : Int) < n) (m : Nat) (hps : ps.size = n.toNat)
    (hhd : ∀ k, k ≤ n.toNat → hd[k]! = (ocnt (src fr) m k : Int))
    (hlo : ∀ v, v < V → ps[v]! = (ocnt (src fr) m v : Int)) :
    ∀ v, v < V + 1 → (set ps (V : Int) (get hd V))[v]! = (ocnt (src fr) m v : Int) := by
  intro v hv
  rw [getElem!_set _ _ _ _ (by simp; omega), Int.toNat_natCast]
  by_cases e : v = V
  · subst e; simp only [ite_true, get_natCast]; exact hhd v (by omega)
  · simp only [e, ite_false]; exact hlo v (by omega)

/-- Arcs with different indices go to different positions. -/
theorem pos_ne (m : Nat) (i L : Nat) (hi : i < L) (hL : L < m) :
    ocnt (src fr) m (src fr i) + cnt (src fr) (src fr i) i ≠ ocnt (src fr) m (src fr L) + cnt (src fr) (src fr L) L := by
  have hci := cnt_lt (src fr) (show i < m by omega)
  have hcL := cnt_lt (src fr) hL
  rcases Nat.lt_trichotomy (src fr i) (src fr L) with h | h | h
  · have := ocnt_mono (src fr) m (show src fr i + 1 ≤ src fr L by omega)
    simp only [ocnt] at this
    omega
  · rw [h]
    have h1 := cnt_succ (src fr) (src fr L) i
    rw [if_pos h] at h1
    have h2 := cnt_mono (src fr) (src fr L) (show i + 1 ≤ L by omega)
    omega
  · have := ocnt_mono (src fr) m (show src fr L + 1 ≤ src fr i by omega)
    simp only [ocnt] at this
    omega

theorem pos_lt (m n : Nat) (L : Nat) (hL : L < m) (hall : ∀ j, j < m → src fr j < n) :
    ocnt (src fr) m (src fr L) + cnt (src fr) (src fr L) L < m := by
  have hcL := cnt_lt (src fr) hL
  have := ocnt_mono (src fr) m (show src fr L + 1 ≤ n from hall L hL)
  simp only [ocnt] at this
  rw [ocnt_total (src fr) n m hall] at this
  omega

theorem inv4_step (to_ tg ps : Array Int) (n : Int) (L m : Nat) (hL : L < m) (hFL : 0 ≤ fr[L]! ∧ fr[L]! < n)
    (hall : ∀ j, j < m → src fr j < n.toNat) (hps : ps.size = n.toNat) (htg : tg.size = m)
    (hpos : ∀ v : Nat, (v : Int) < n → ps[v]! = (ocnt (src fr) m v : Int) + (cnt (src fr) v L : Int))
    (htarget : ∀ i, i < L → tg[ocnt (src fr) m (fr[i]!).toNat + cnt (src fr) (fr[i]!).toNat i]! = to_[i]!) :
    (∀ v : Nat, (v : Int) < n → (set ps (get fr L) (get ps (get fr L) + 1))[v]! =
        (ocnt (src fr) m v : Int) + (cnt (src fr) v (L + 1) : Int)) ∧
    (∀ i, i < L + 1 → (set tg (get ps (get fr L)) (get to_ L))[ocnt (src fr) m (fr[i]!).toNat +
        cnt (src fr) (fr[i]!).toNat i]! = to_[i]!) := by
  simp only [get_natCast]
  have hf : (fr[L]!).toNat = src fr L := rfl
  have hfn : src fr L < n.toNat := by simp only [src]; omega
  have hp : ps[(fr[L]!).toNat]! = (ocnt (src fr) m (src fr L) : Int) + (cnt (src fr) (src fr L) L : Int) := by
    rw [hf]; exact hpos _ (by omega)
  have hplt := pos_lt fr m n.toNat L hL hall
  constructor
  · intro v hv
    rw [getElem!_set _ _ _ _ (by omega), get_eq, cnt_succ]
    by_cases e : v = (fr[L]!).toNat
    · subst e
      simp only [ite_true, hp, ← hf]
      simp [src]; push_cast; ring
    · simp only [e, ite_false]
      rw [hpos v hv, if_neg (by simp only [src]; omega)]
      simp
  · intro i hi
    rw [get_eq, hp]
    have hcast : ((ocnt (src fr) m (src fr L) : Int) + (cnt (src fr) (src fr L) L : Int)).toNat =
        ocnt (src fr) m (src fr L) + cnt (src fr) (src fr L) L := by omega
    rw [getElem!_set _ _ _ _ (by rw [hcast]; omega), hcast]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | h
    · have hne := pos_ne fr m i L h hL
      simp only [src] at hne
      simp only [src, hne, ite_false]
      exact htarget i h
    · subst h
      simp [src]

end


theorem csr_build_spec (fr to_ head target pos : Array Int) (n : Int) (hn : 0 ≤ n)
    (hto : to_.size = fr.size) (ht : target.size = fr.size) (hh : head.size = n.toNat + 1)
    (hh0 : ∀ k : Nat, head[k]! = 0) (hp : pos.size = n.toNat)
    (hF : ∀ i, i < fr.size → 0 ≤ fr[i]! ∧ fr[i]! < n) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.csr_build fr to_ head target pos n
    ⦃⇓ r c => ⌜r.1.size = n.toNat + 1 ∧
               (∀ k, k ≤ n.toNat → r.1[k]! = (ocnt (src fr) fr.size k : Int)) ∧
               r.2.1.size = fr.size ∧
               (∀ i, i < fr.size → r.2.1[ocnt (src fr) fr.size (fr[i]!).toNat +
                  cnt (src fr) (fr[i]!).toNat i]! = to_[i]!) ∧
               c = t0 + 1 + 2 * fr.size + 2 * n.toNat⌝⦄ := by
  mvcgen [cp.csr_build]
  case inv1 =>
    exact ⇓⟨xs, hd⟩ c => ⌜hd.size = n.toNat + 1 ∧ hd[0]! = 0 ∧
      (∀ k, 1 ≤ k → k ≤ n.toNat → hd[k]! = (cnt (src fr) (k - 1) xs.prefix.length : Int)) ∧
      c = t0 + 1 + xs.prefix.length⌝
  case inv2 =>
    exact ⇓⟨xs, hd⟩ c => ⌜hd.size = n.toNat + 1 ∧
      (∀ k, k ≤ xs.prefix.length → hd[k]! = (ocnt (src fr) fr.size k : Int)) ∧
      (∀ k, xs.prefix.length < k → k ≤ n.toNat → hd[k]! = (cnt (src fr) (k - 1) fr.size : Int)) ∧
      c = t0 + 1 + fr.size + xs.prefix.length⌝
  case inv3 =>
    exact ⇓⟨xs, ps⟩ c => ⌜ps.size = n.toNat ∧
      (∀ v, v < xs.prefix.length → ps[v]! = (ocnt (src fr) fr.size v : Int)) ∧
      c = t0 + 1 + fr.size + n.toNat + xs.prefix.length⌝
  case inv4 =>
    exact ⇓⟨xs, tg, ps⟩ c => ⌜ps.size = n.toNat ∧ tg.size = fr.size ∧
      (∀ v, v < n.toNat → ps[v]! = (ocnt (src fr) fr.size v + cnt (src fr) v xs.prefix.length : Int)) ∧
      (∀ i, i < xs.prefix.length → tg[ocnt (src fr) fr.size (fr[i]!).toNat + cnt (src fr) (fr[i]!).toNat i]! = to_[i]!) ∧
      c = t0 + 1 + fr.size + 2 * n.toNat + xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  all_goals (try simp only [range_length, Proofs.Cpp.size, Int.sub_zero, Int.toNat_natCast] at *)
  · -- loop 1: count the arcs of each source
    have hl := range_prefix_length ‹range _ _ = _ ++ _ :: _›
    have e := range_cursor ‹range _ _ = _ ++ _ :: _›
    try simp +zetaDelta [Proofs.Cpp.size] at e hl
    subst e
    obtain ⟨hsz, h0, hk, hc⟩ := ‹_ = n.toNat + 1 ∧ _ ∧ _ ∧ _›
    obtain ⟨a1, a2⟩ := inv1_step fr n _ _ (hF _ hl) hsz h0 hk
    exact ⟨hsz, a1, a2, by omega⟩
  · exact ⟨hh, hh0 0, fun k _ _ => by simp [hh0, cnt_zero], by omega⟩
  · -- loop 2: prefix sums
    have hl := range_prefix_length ‹range _ _ = _ ++ _ :: _›
    have e := range_cursor ‹range _ _ = _ ++ _ :: _›
    try simp +zetaDelta [Proofs.Cpp.size] at e hl
    subst e
    obtain ⟨hsz, hlo, hhi, hc⟩ := ‹_ = n.toNat + 1 ∧ (∀ k, k ≤ _ → _) ∧ _ ∧ _›
    obtain ⟨b1, b2⟩ := inv2_step fr n _ _ (by omega) fr.size hsz hlo hhi
    exact ⟨hsz, b1, b2, by omega⟩
  · obtain ⟨hsz, h0, hk, hc⟩ := ‹_ = n.toNat + 1 ∧ _ ∧ _ ∧ _›
    try simp +zetaDelta [Proofs.Cpp.size] at hk hc
    exact ⟨hsz, by simp [h0, ocnt], fun k h1 h2 => by rw [hk k (by omega) h2], by omega⟩
  · -- loop 3: copy head into pos
    have hl := range_prefix_length ‹range _ _ = _ ++ _ :: _›
    have e := range_cursor ‹range _ _ = _ ++ _ :: _›
    try simp +zetaDelta [Proofs.Cpp.size] at e hl
    subst e
    obtain ⟨hps, hlo, hc⟩ := ‹_ = n.toNat ∧ _ ∧ _›
    obtain ⟨hsz2, hlo2, hhi2, hc2⟩ := ‹_ = n.toNat + 1 ∧ (∀ k, k ≤ _ → _) ∧ _ ∧ _›
    try simp +zetaDelta [Proofs.Cpp.size] at hlo2
    exact ⟨hps, inv3_step fr _ _ _ n (by omega) fr.size hps (fun k hk => hlo2 k (by omega)) hlo, by omega⟩
  · exact ⟨hp, by omega⟩
  · -- loop 4: place the arcs
    have hl := range_prefix_length ‹range _ _ = _ ++ _ :: _›
    have e := range_cursor ‹range _ _ = _ ++ _ :: _›
    try simp +zetaDelta [Proofs.Cpp.size] at e hl
    subst e
    obtain ⟨hps, htg, hpos, htar, hc⟩ := ‹_ = n.toNat ∧ _ = fr.size ∧ _ ∧ _ ∧ _›
    have hall : ∀ j, j < fr.size → src fr j < n.toNat := fun j hj => by
      have := hF j hj; simp only [src]; omega
    obtain ⟨c1, c2⟩ := inv4_step fr to_ _ _ n _ fr.size hl (hF _ hl) hall hps htg hpos htar
    exact ⟨hps, htg, c1, c2, by omega⟩
  · obtain ⟨hps, hlo, hc⟩ := ‹_ = n.toNat ∧ _ ∧ _›
    try simp +zetaDelta [Proofs.Cpp.size] at hlo hc
    exact ⟨hps, ht, fun v hv => by rw [hlo v (by omega)]; simp [cnt_zero], by omega⟩
  · obtain ⟨hps, htg, hpos, htar, hc⟩ := ‹_ = n.toNat ∧ _ = fr.size ∧ _ ∧ _ ∧ _›
    obtain ⟨hsz2, hlo2, hhi2, hc2⟩ := ‹_ = n.toNat + 1 ∧ (∀ k, k ≤ _ → _) ∧ _ ∧ _›
    try simp +zetaDelta [Proofs.Cpp.size] at htar hc hlo2
    exact ⟨hsz2, fun k hk => hlo2 k (by omega), htg, htar, by omega⟩

end Proofs.Cpp.CsrBuild
