import Mathlib.Tactic.Ring
import Proofs.Math.PrimMath
import Proofs.Math.Fermat

/-! Pure facts for `factorize` (library/number_theory/factorize.hpp): the walk of Pollard's rho meets within `n`
steps (`floyd_meets`), the measure `firstIdx` of the rho loop, and trial division (`NoSmall`, `prime_of_noSmall`). -/

namespace Proofs.FactorizeMath
open Proofs.Fermat (IsPrime)

/-- The walk of Pollard's rho: `a F i = F^[i] 2`. -/
def walk (F : Nat → Nat) (i : Nat) : Nat := F^[i] 2

theorem walk_lt (F : Nat → Nat) (n : Nat) (h2 : 2 < n) (hF : ∀ v, F v < n) : ∀ i, walk F i < n := by
  intro i; cases i with
  | zero => simpa [walk] using h2
  | succ i => simp only [walk, Function.iterate_succ_apply']; exact hF _

theorem walk_add (F : Nat → Nat) (a b : Nat) : F^[a + b] 2 = F^[a] (F^[b] 2) := by
  rw [Function.iterate_add_apply]

/-- Two equal points of the walk give a period from the first one on. -/
theorem walk_period (F : Nat → Nat) (p L : Nat) (h : walk F (p + L) = walk F p) :
    ∀ t j, p ≤ t → walk F (t + j * L) = walk F t := by
  intro t j hpt
  have hfix : F^[L] (F^[p] 2) = F^[p] 2 := by
    have := h; unfold walk at this; rw [Nat.add_comm, Function.iterate_add_apply] at this; exact this
  have hfix' : F^[L] (F^[t] 2) = F^[t] 2 := by
    rw [show t = (t - p) + p by omega, Function.iterate_add_apply, ← Function.iterate_add_apply,
      Nat.add_comm L, Function.iterate_add_apply, hfix]
  unfold walk
  rw [Nat.add_comm, Function.iterate_add_apply]
  induction j with
  | zero => simp
  | succ j ih => rw [Nat.succ_mul, Function.iterate_add_apply, hfix', ih]

/-- Two of the points `0 .. n` of the walk coincide. -/
theorem walk_repeat (F : Nat → Nat) (n : Nat) (h2 : 2 < n) (hF : ∀ v, F v < n) :
    ∃ p q, p < q ∧ q ≤ n ∧ walk F p = walk F q := by
  have hlt := walk_lt F n h2 hF
  by_contra hno
  simp only [not_exists, not_and] at hno
  have hnd : ((List.range (n + 1)).map (walk F)).Nodup := by
    apply Proofs.PrimMath.nodup_map_inj List.nodup_range
    intro x hx y hy hxy
    have hx' := List.mem_range.mp hx; have hy' := List.mem_range.mp hy
    rcases Nat.lt_trichotomy x y with h | h | h
    · exact absurd hxy (hno x y h (by omega))
    · exact h
    · exact absurd hxy.symm (hno y x h (by omega))
  have hsub : (List.range (n + 1)).map (walk F) ⊆ List.range n := by
    intro v hv; obtain ⟨i, -, rfl⟩ := List.mem_map.mp hv; exact List.mem_range.mpr (hlt i)
  have := List.Nodup.length_le_of_subset hnd hsub
  simp at this

/-- Floyd's cycle detection meets within `n` steps: some `1 ≤ i ≤ n` has `a i = a (2 i)`. -/
theorem floyd_meets (F : Nat → Nat) (n : Nat) (h2 : 2 < n) (hF : ∀ v, F v < n) :
    ∃ i, 1 ≤ i ∧ i ≤ n ∧ walk F i = walk F (2 * i) := by
  obtain ⟨p, q, hl, hq, he⟩ := walk_repeat F n h2 hF
  set L := q - p with hL
  have hL0 : 0 < L := by omega
  have hper : walk F (p + L) = walk F p := by rw [show p + L = q by omega]; exact he.symm
  have hmd := Nat.div_add_mod p L
  have hml := Nat.mod_lt p hL0
  refine ⟨L * (p / L + 1), ?_, ?_, ?_⟩
  · exact Nat.le_trans hL0 (Nat.le_mul_of_pos_right L (Nat.succ_pos _))
  · have : L * (p / L + 1) = L * (p / L) + L := by ring
    omega
  · have hge : p ≤ L * (p / L + 1) := by
      have : L * (p / L + 1) = L * (p / L) + L := by ring
      omega
    rw [show 2 * (L * (p / L + 1)) = L * (p / L + 1) + (p / L + 1) * L by ring]
    exact (walk_period F p L hper _ _ hge).symm

/-! ## The measure of the rho loop -/

def Meet (F : Nat → Nat) (j : Nat) : Prop := walk F j = walk F (2 * j)

/-- Without meetings in `[1, i]`, no earlier point of the walk equals the `i`-th one. -/
theorem walk_first (F : Nat → Nat) (i j : Nat) (hno : ∀ t, 1 ≤ t → t ≤ i → ¬ Meet F t) (hj : j < i)
    (he : walk F j = walk F i) : False := by
  set L := i - j
  have hL0 : 0 < L := by omega
  have hper : walk F (j + L) = walk F j := by rw [show j + L = i by omega]; exact he.symm
  have hmd := Nat.div_add_mod j L
  have hml := Nat.mod_lt j hL0
  have e : L * (j / L + 1) = L * (j / L) + L := by ring
  apply hno (L * (j / L + 1)) (by omega) (by omega)
  unfold Meet
  rw [show 2 * (L * (j / L + 1)) = L * (j / L + 1) + (j / L + 1) * L by ring]
  exact (walk_period F j L hper _ _ (by omega)).symm

open Classical in
/-- The first index whose pair of walk points is `(x, y)`. -/
noncomputable def firstIdx (F : Nat → Nat) (x y : Nat) : Nat :=
  if h : ∃ j, walk F j = x ∧ walk F (2 * j) = y then Nat.find h else 0

theorem firstIdx_eq (F : Nat → Nat) (i : Nat) (hno : ∀ t, 1 ≤ t → t ≤ i → ¬ Meet F t) :
    firstIdx F (walk F i) (walk F (2 * i)) = i := by
  classical
  have h : ∃ j, walk F j = walk F i ∧ walk F (2 * j) = walk F (2 * i) := ⟨i, rfl, rfl⟩
  unfold firstIdx
  rw [dif_pos h]
  apply le_antisymm
  · exact Nat.find_min' h ⟨rfl, rfl⟩
  · by_contra hc
    have hs := Nat.find_spec h
    exact walk_first F i _ hno (by omega) hs.1

/-- Without meetings in `[1, i]`, `i < n`. -/
theorem lt_of_noMeet (F : Nat → Nat) (n i : Nat) (h2 : 2 < n) (hF : ∀ v, F v < n)
    (hno : ∀ t, 1 ≤ t → t ≤ i → ¬ Meet F t) : i < n := by
  obtain ⟨j, h1, hj, he⟩ := floyd_meets F n h2 hF
  by_contra hc
  exact hno j h1 (by omega) he

/-! ## Trial division -/

/-- No divisor of `n` in `[2, i)`. -/
def NoSmall (n i : Nat) : Prop := ∀ d, 2 ≤ d → d < i → ¬ d ∣ n

/-- A divisor `i ≥ 2` of `n` without smaller divisors `≥ 2` of `n` is prime. -/
theorem prime_of_least (n i : Nat) (hi : 2 ≤ i) (hn : 0 < n) (hd : i ∣ n) (hs : NoSmall n i) : IsPrime i := by
  refine ⟨hi, fun d hdi => ?_⟩
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdi (by omega)
  have hle : d ≤ i := Nat.le_of_dvd (by omega) hdi
  by_cases h1 : d = 1
  · exact Or.inl h1
  · by_cases h2 : d = i
    · exact Or.inr h2
    · exact absurd (Nat.dvd_trans hdi hd) (hs d (by omega) (by omega))

/-- Without divisors in `[2, i)` and with `n < i * i`, `n` is `1` or prime. -/
theorem prime_of_noSmall (n i : Nat) (hn : 2 ≤ n) (hs : NoSmall n i) (hlt : n < i * i) : IsPrime n := by
  refine ⟨hn, fun d hd => ?_⟩
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
  by_cases h1 : d = 1
  · exact Or.inl h1
  by_cases h2 : d = n
  · exact Or.inr h2
  exfalso
  obtain ⟨e, he⟩ := hd
  have hdle : d ≤ n := Nat.le_of_dvd (by omega) ⟨e, he⟩
  have he0 : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; omega)
  by_cases hdi : d < i
  · exact hs d (by omega) hdi ⟨e, he⟩
  · have hei : e < i := by
      by_contra hc
      have : i * i ≤ d * e := Nat.mul_le_mul (by omega) (by omega)
      omega
    have he2 : 2 ≤ e := by
      by_contra hc
      have : e = 1 := by omega
      subst this; omega
    exact hs e he2 hei ⟨d, by rw [he]; ring⟩

theorem noSmall_two (n : Nat) : NoSmall n 2 := fun d h1 h2 => absurd h2 (by omega)

/-- An odd `n` keeps `NoSmall` from an even bound to the next odd one. -/
theorem noSmall_step (n i : Nat) (hs : NoSmall n i) (hi : ¬ i ∣ n) (hodd : n % 2 = 1) (hi3 : 3 ≤ i) (hio : i % 2 = 1) :
    NoSmall n (i + 2) := by
  intro d h1 h2 hd
  by_cases hdi : d < i
  · exact hs d h1 hdi hd
  · by_cases e : d = i
    · subst e; exact hi hd
    · have : d = i + 1 := by omega
      subst this
      have : 2 ∣ n := Nat.dvd_trans ⟨(i + 1) / 2, by omega⟩ hd
      omega

/-- Dividing `n` by a factor keeps `NoSmall`. -/
theorem noSmall_div (n i q : Nat) (hs : NoSmall n i) (hq : q ∣ n) : NoSmall (n / q) i := by
  intro d h1 h2 hd
  exact hs d h1 h2 (Nat.dvd_trans hd (Nat.div_dvd_of_dvd hq))

end Proofs.FactorizeMath
