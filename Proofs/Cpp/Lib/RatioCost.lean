import Proofs.Cpp.Lib.Basic
import Mathlib.Data.Int.GCD

namespace Proofs.Cpp.RatioCost

/-- Each magnitude fits in `bits` bits, including any intermediate operand. -/
theorem gcd_bits (a b bits : Nat) (ha : a ≤ 2 ^ bits) (hb : b ≤ 2 ^ bits) :
    gcdCost a b ≤ 2 + 2 * bits := by
  have hm := Nat.mul_le_mul ha hb
  rw [← Nat.pow_add] at hm
  have hl := log2_mono2 (a * b) (2 ^ (bits + bits)) hm
  rw [Nat.log2_two_pow] at hl
  simp only [gcdCost]
  split_ifs <;> omega

/-- A finite number of Euclidean calls has linear work in the bit bound. -/
theorem work_bits (overhead calls bits : Nat) (costs : List Nat)
    (hn : costs.length = calls) (hc : ∀ cost ∈ costs, cost ≤ 2 + 2 * bits) :
    overhead + costs.sum ≤ (overhead + 2 * calls) * (bits + 1) := by
  have hs : costs.sum ≤ calls * (2 + 2 * bits) := by
    rw [← hn]
    clear hn
    induction costs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.sum_cons, List.length_cons]
      have hx := hc x (by simp)
      have ht : ∀ cost ∈ xs, cost ≤ 2 + 2 * bits := by
        intro cost h
        exact hc cost (by simp [h])
      have hi := ih ht
      calc
        x + xs.sum ≤ (2 + 2 * bits) + xs.length * (2 + 2 * bits) := Nat.add_le_add hx hi
        _ = _ := by rw [Nat.add_mul]; omega
  calc
    overhead + costs.sum ≤ overhead + calls * (2 + 2 * bits) := Nat.add_le_add_left hs _
    _ ≤ (overhead + 2 * calls) * (bits + 1) := by nlinarith

/-- LCM never exceeds the product of the original magnitudes. -/
theorem lcm_size (d e : Int) (B : Nat) (hd : d.natAbs ≤ B) (he : e.natAbs ≤ B) :
    (Int.lcm d e : Int).natAbs ≤ B * B := by
  simp only [Int.natAbs_natCast, Int.lcm_def, Nat.lcm_eq_mul_div]
  exact le_trans (Nat.div_le_self _ _) (Nat.mul_le_mul hd he)

theorem quotient_product_size (a b g h : Int) (B : Nat)
    (ha : a.natAbs ≤ B) (hb : b.natAbs ≤ B) :
    (a / g * (b / h)).natAbs ≤ B * B := by
  rw [Int.natAbs_mul]
  exact Nat.mul_le_mul (le_trans (Int.natAbs_ediv_le_natAbs a g) ha)
    (le_trans (Int.natAbs_ediv_le_natAbs b h) hb)

theorem scaled_size (n d l : Int) (B C : Nat)
    (hn : n.natAbs ≤ B) (hl : l.natAbs ≤ C) :
    (l / d * n).natAbs ≤ C * B := by
  rw [Int.natAbs_mul]
  exact Nat.mul_le_mul (le_trans (Int.natAbs_ediv_le_natAbs l d) hl) hn

theorem add_size (n d m e : Int) (B : Nat)
    (hn : n.natAbs ≤ B) (hd : d.natAbs ≤ B)
    (hm : m.natAbs ≤ B) (he : e.natAbs ≤ B) :
    ((Int.lcm d e : Int) / d * n + (Int.lcm d e : Int) / e * m).natAbs ≤ 2 * (B * B * B) := by
  have hl := lcm_size d e B hd he
  have h₁ := scaled_size n d (Int.lcm d e) B (B * B) hn hl
  have h₂ := scaled_size m e (Int.lcm d e) B (B * B) hm hl
  have hs := Int.natAbs_add_le ((Int.lcm d e : Int) / d * n) ((Int.lcm d e : Int) / e * m)
  omega

theorem sub_size (n d m e : Int) (B : Nat)
    (hn : n.natAbs ≤ B) (hd : d.natAbs ≤ B)
    (hm : m.natAbs ≤ B) (he : e.natAbs ≤ B) :
    ((Int.lcm d e : Int) / d * n - (Int.lcm d e : Int) / e * m).natAbs ≤ 2 * (B * B * B) := by
  have hl := lcm_size d e B hd he
  have h₁ := scaled_size n d (Int.lcm d e) B (B * B) hn hl
  have h₂ := scaled_size m e (Int.lcm d e) B (B * B) hm hl
  have hs := Int.natAbs_add_le ((Int.lcm d e : Int) / d * n) (-((Int.lcm d e : Int) / e * m))
  simp only [Int.natAbs_neg, ← Int.sub_eq_add_neg] at hs
  omega

theorem cube_bits (bits : Nat) :
    2 * (2 ^ bits * 2 ^ bits * 2 ^ bits) = 2 ^ (3 * bits + 1) := by
  have h : 3 * bits + 1 = bits + bits + bits + 1 := by omega
  rw [h]
  simp [Nat.pow_add, Nat.mul_comm]

theorem square_bits_le (bits : Nat) :
    2 ^ bits * 2 ^ bits ≤ 2 ^ (3 * bits + 1) := by
  rw [← Nat.pow_add]
  exact Nat.pow_le_pow_right (by decide) (by omega)

theorem gcd_size (a b : Int) (B : Nat) (ha : a.natAbs ≤ B) (hb : b.natAbs ≤ B) :
    (Int.gcd a b : Int).natAbs ≤ B := by
  simp only [Int.natAbs_natCast, Int.gcd]
  by_cases hz : a.natAbs = 0
  · simpa only [hz, Nat.gcd_zero_left] using hb
  · exact le_trans (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)) ha

end Proofs.Cpp.RatioCost
