import Proofs.IsPrimeRun
import Proofs.IsPrimeMr

/-! Correctness of the Miller-Rabin `is_prime` specification: primes are accepted; composite numbers are rejected
under the (published, not proved here) assumption that the first twelve primes are a witness set below `2^64`. -/
namespace Proofs.IsPrimeSpec
open Proofs.IsPrimeExec Proofs.IsPrimeRun Proofs.IsPrimeMr Proofs.Fermat

abbrev badBase (n d r j : Nat) : Prop := mrb j ≤ n - 2 ∧ mrwx n r (mrb j ^ d % n) = true

theorem ispRun_iff (n d r : Nat) : ∀ (k bi : Nat) (f : Bool),
    ispRun n d r k bi f = true ↔ (f = true ∧ ∀ j, bi ≤ j → j < bi + k → ¬ badBase n d r j)
  | 0, bi, f => by
    simp only [ispRun]
    constructor
    · intro h; exact ⟨h, fun j h1 h2 => by omega⟩
    · intro ⟨h, _⟩; exact h
  | k + 1, bi, f => by
    rw [ispRun, ispRun_iff n d r k (bi + 1) (stepF n d r bi f)]
    by_cases h : badBase n d r bi
    · have e : stepF n d r bi f = false := by simp [stepF, h.1, h.2]
      rw [e]
      constructor
      · intro ⟨h1, _⟩; simp at h1
      · intro ⟨_, h2⟩; exact absurd h (h2 bi (by omega) (by omega))
    · have e : stepF n d r bi f = f := by
        unfold stepF
        rw [if_neg (fun hh => h hh)]
      rw [e]
      constructor
      · intro ⟨h1, h2⟩
        refine ⟨h1, fun j hj1 hj2 => ?_⟩
        by_cases hj : j = bi
        · subst hj; exact h
        · exact h2 j (by omega) (by omega)
      · intro ⟨h1, h2⟩
        exact ⟨h1, fun j hj1 hj2 => h2 j (by omega) (by omega)⟩


theorem mrb_ge (j : Nat) : 2 ≤ mrb j := by
  unfold mrb; repeat' (first | split | omega)

theorem isPrime_two : IsPrime 2 := by
  refine ⟨by decide, fun d hd => ?_⟩
  have : d ≤ 2 := Nat.le_of_dvd (by decide) hd
  have : d ≠ 0 := by intro h; subst h; simp at hd
  omega

theorem odd_of_prime (n : Nat) (hp : IsPrime n) (h2 : n ≠ 2) : n % 2 = 1 := by
  by_cases h : n % 2 = 0
  · have hd : 2 ∣ n := Nat.dvd_of_mod_eq_zero h
    rcases hp.2 2 hd with h1 | h1 <;> omega
  · omega

theorem ispF_prime (n : Nat) (hn : n < M64) (hp : IsPrime n) (h2 : n ≠ 2) : ispF n = true := by
  have hodd := odd_of_prime n hp h2
  have hn2 := hp.1
  have hd0 : 0 < n - 1 := by omega
  have hM : M64 = 2 ^ 64 := by decide
  have hd64 : n - 1 < 2 ^ 64 := by omega
  obtain ⟨s1, s2, s3, s4⟩ := dloop_spec 64 (n - 1) 0 hd0 hd64
  unfold ispF
  rw [ispRun_iff]
  refine ⟨rfl, fun j _ _ hb => ?_⟩
  have hnd : n - 1 = (dloop 64 (n - 1) 0).1 * 2 ^ (dloop 64 (n - 1) 0).2 := by
    rw [Nat.sub_zero] at s2; exact s2.symm
  have := mrwx_prime n (dloop 64 (n - 1) 0).1 (dloop 64 (n - 1) 0).2 (mrb j) hp (by have := mrb_ge j; omega)
    (by have := hb.1; omega) hnd
  have hb2 : mrwx n (dloop 64 (n - 1) 0).2 (mrb j ^ (dloop 64 (n - 1) 0).1 % n) = true := hb.2
  rw [this] at hb2
  exact absurd hb2 (by simp)

/-- The published witness-set computation (bases 2, 3, ..., 37 decide primality below `3.18e23`), restricted to the
inputs `is_prime` handles. It is NOT proved here; the theorems below take it as an explicit hypothesis. -/
def MRWitnessSet : Prop := ∀ n : Nat, 3 ≤ n → n < M64 → n % 2 = 1 → ¬ IsPrime n →
  ∃ j, j < 12 ∧ badBase n (dloop 64 (n - 1) 0).1 (dloop 64 (n - 1) 0).2 j

theorem ispF_composite (H : MRWitnessSet) (n : Nat) (hn : n < M64) (h3 : 3 ≤ n) (hodd : n % 2 = 1) (hnp : ¬ IsPrime n) :
    ispF n = false := by
  obtain ⟨j, hj, hb⟩ := H n h3 hn hodd hnp
  unfold ispF
  cases h : ispRun n (dloop 64 (n - 1) 0).1 (dloop 64 (n - 1) 0).2 12 0 true
  · rfl
  · rw [ispRun_iff] at h
    exact absurd hb (h.2 j (by omega) (by omega))

theorem ispSpec_prime (n : Nat) (hn : n < M64) (hp : IsPrime n) : ispSpec n = true := by
  unfold ispSpec
  by_cases h2 : n = 2
  · simp [h2]
  · have hodd := odd_of_prime n hp h2
    have hn2 := hp.1
    rw [if_neg h2, if_neg (by omega)]
    exact ispF_prime n hn hp h2

theorem ispSpec_true_prime (H : MRWitnessSet) (n : Nat) (hn : n < M64) (h : ispSpec n = true) : IsPrime n := by
  by_cases hp : IsPrime n
  · exact hp
  · exfalso
    unfold ispSpec at h
    by_cases h2 : n = 2
    · exact hp (h2 ▸ isPrime_two)
    · rw [if_neg h2] at h
      by_cases h3 : n % 2 = 0 ∨ n ≤ 1
      · rw [if_pos h3] at h; simp at h
      · rw [if_neg h3] at h
        rw [ispF_composite H n hn (by omega) (by omega) hp] at h
        simp at h

end Proofs.IsPrimeSpec
