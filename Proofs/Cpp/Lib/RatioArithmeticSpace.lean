import Proofs.Cpp.Lib.RatioSpace
import Proofs.Cpp.Lib.RatioCost

/-! Conservative logical payload envelopes for Ratio arithmetic. The envelope
retains all named arithmetic values simultaneously, including values computed in
later phases. Callee frames are added to that fixed envelope; histories of loop
states are never retained. This is not a model of C++ heap or object lifetimes. -/
namespace Proofs.Cpp.RatioArithmeticSpace
open Proofs.Cpp.RatioSpace Proofs.Cpp.RatioCost

def normalizePeak (n d : Int) (k : Nat) : Nat :=
  max (signedPayloadBits (normalizeContext n d) +
    payloadBits (frame (stateAt k (n.natAbs, d.natAbs))))
    (signedPayloadBits (normalizeScale n d))

def lcmPeak (a b k : Nat) : Nat :=
  max (payloadBits (lcmContext a b ++ frame (stateAt k (a, b))))
    (payloadBits (lcmScale a b))

def additiveContext (subtract : Bool) (n d m e : Int) : List Int :=
  let l : Int := Int.lcm d e
  let x := l / d * n
  let y := l / e * m
  let z := if subtract then x - y else x + y
  [n, d, m, e, l, x, y, z]

def additivePeak (subtract : Bool) (n d m e : Int) (k₁ k₂ : Nat) : Nat :=
  let l : Int := Int.lcm d e
  let x := l / d * n
  let y := l / e * m
  let z := if subtract then x - y else x + y
  signedPayloadBits (additiveContext subtract n d m e) +
    max (lcmPeak d.natAbs e.natAbs k₁) (normalizePeak z l k₂)

theorem additive_context_bits (subtract : Bool) (n d m e : Int) (bits : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits)
    (hm : m.natAbs ≤ 2 ^ bits) (he : e.natAbs ≤ 2 ^ bits) :
    ∀ value ∈ additiveContext subtract n d m e, value.natAbs ≤ 2 ^ (3 * bits + 1) := by
  have hi : 2 ^ bits ≤ 2 ^ (3 * bits + 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hl := lcm_size d e (2 ^ bits) hd he
  have hl' := le_trans hl (square_bits_le bits)
  have hcube : 2 ^ bits * 2 ^ bits * 2 ^ bits ≤ 2 ^ (3 * bits + 1) := by
    rw [← cube_bits]
    omega
  have hx := le_trans (scaled_size n d (Int.lcm d e) _ _ hn hl) hcube
  have hy := le_trans (scaled_size m e (Int.lcm d e) _ _ hm hl) hcube
  have hz : ((if subtract then
      (Int.lcm d e : Int) / d * n - (Int.lcm d e : Int) / e * m else
      (Int.lcm d e : Int) / d * n + (Int.lcm d e : Int) / e * m) : Int).natAbs ≤
      2 ^ (3 * bits + 1) := by
    rw [← cube_bits]
    cases subtract with
    | false => exact add_size n d m e _ hn hd hm he
    | true => exact sub_size n d m e _ hn hd hm he
  intro value hv
  simp [additiveContext] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact le_trans hn hi
  · exact le_trans hd hi
  · exact le_trans hm hi
  · exact le_trans he hi
  · exact hl'
  · exact hx
  · exact hy
  · exact hz

/-- Both addition and subtraction have O(input bits + 1) logical payload. -/
theorem additive_peak_bits (subtract : Bool) (n d m e : Int) (bits k₁ k₂ : Nat)
    (hd0 : d ≠ 0) (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits)
    (hm : m.natAbs ≤ 2 ^ bits) (he : e.natAbs ≤ 2 ^ bits) :
    additivePeak subtract n d m e k₁ k₂ ≤ 81 * (bits + 1) := by
  have hs := additive_context_bits subtract n d m e bits hn hd hm he
  have hctx := signed_context_bits (additiveContext subtract n d m e) (3 * bits + 1) hs
  change signedPayloadBits (additiveContext subtract n d m e) ≤ 16 * (3 * bits + 2) at hctx
  have hz := hs (if subtract then
      (Int.lcm d e : Int) / d * n - (Int.lcm d e : Int) / e * m else
      (Int.lcm d e : Int) / d * n + (Int.lcm d e : Int) / e * m) (by simp [additiveContext])
  have hl := hs (Int.lcm d e) (by simp [additiveContext])
  have hnorm := normalize_peak_bits _ _ (3 * bits + 1) k₂ hz hl
  have hlcm := lcm_peak_bits d.natAbs e.natAbs bits k₁ (by omega) hd he
  change lcmPeak d.natAbs e.natAbs k₁ ≤ 10 * (bits + 1) at hlcm
  change normalizePeak _ _ k₂ ≤ 11 * (3 * bits + 2) at hnorm
  unfold additivePeak
  apply Nat.le_trans (Nat.add_le_add hctx (max_le (by omega) hnorm))
  omega

def gcdPeak (a b : Int) (k : Nat) : Nat :=
  signedPayloadBits [a, b] + payloadBits (frame (stateAt k (a.natAbs, b.natAbs)))

theorem gcd_peak_bits (a b : Int) (bits k : Nat)
    (ha : a.natAbs ≤ 2 ^ bits) (hb : b.natAbs ≤ 2 ^ bits) :
    gcdPeak a b k ≤ 7 * (bits + 1) := by
  have hc : ∀ value ∈ [a, b], value.natAbs ≤ 2 ^ bits := by
    intro value hv
    simp at hv
    rcases hv with rfl | rfl
    · exact ha
    · exact hb
  have hs := signed_context_bits [a, b] bits hc
  change signedPayloadBits [a, b] ≤ 4 * (bits + 1) at hs
  have hf := (all_frames a.natAbs b.natAbs bits k ha hb).2
  unfold gcdPeak
  omega

def productContext (divide : Bool) (n d m e : Int) : List Int :=
  let g : Int := if divide then Int.gcd n m else Int.gcd n e
  let h : Int := if divide then Int.gcd d e else Int.gcd m d
  let z := if divide then n / g * (e / h) else n / g * (m / h)
  let w := if divide then d / h * (m / g) else d / h * (e / g)
  [n, d, m, e, g, h, z, w]

def productPeak (divide : Bool) (n d m e : Int) (k₁ k₂ k₃ : Nat) : Nat :=
  let g : Int := if divide then Int.gcd n m else Int.gcd n e
  let h : Int := if divide then Int.gcd d e else Int.gcd m d
  let z := if divide then n / g * (e / h) else n / g * (m / h)
  let w := if divide then d / h * (m / g) else d / h * (e / g)
  let p₁ := if divide then gcdPeak n m k₁ else gcdPeak n e k₁
  let p₂ := if divide then gcdPeak d e k₂ else gcdPeak m d k₂
  let p₃ := if divide then normalizePeak z w k₃ else 0
  signedPayloadBits (productContext divide n d m e) + max p₁ (max p₂ p₃)

theorem product_context_bits (divide : Bool) (n d m e : Int) (bits : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits)
    (hm : m.natAbs ≤ 2 ^ bits) (he : e.natAbs ≤ 2 ^ bits) :
    ∀ value ∈ productContext divide n d m e, value.natAbs ≤ 2 ^ (3 * bits + 1) := by
  have hi : 2 ^ bits ≤ 2 ^ (3 * bits + 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hgnm := le_trans (gcd_size n m _ hn hm) hi
  have hgne := le_trans (gcd_size n e _ hn he) hi
  have hgde := le_trans (gcd_size d e _ hd he) hi
  have hgmd := le_trans (gcd_size m d _ hm hd) hi
  cases divide <;> intro value hv <;> simp [productContext] at hv
  · rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact le_trans hn hi
    · exact le_trans hd hi
    · exact le_trans hm hi
    · exact le_trans he hi
    · exact hgne
    · exact hgmd
    · exact le_trans (quotient_product_size n m _ _ _ hn hm) (square_bits_le bits)
    · exact le_trans (quotient_product_size d e _ _ _ hd he) (square_bits_le bits)
  · rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact le_trans hn hi
    · exact le_trans hd hi
    · exact le_trans hm hi
    · exact le_trans he hi
    · exact hgnm
    · exact hgde
    · exact le_trans (quotient_product_size n e _ _ _ hn he) (square_bits_le bits)
    · exact le_trans (quotient_product_size d m _ _ _ hd hm) (square_bits_le bits)

theorem product_peak_bits (divide : Bool) (n d m e : Int) (bits k₁ k₂ k₃ : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits)
    (hm : m.natAbs ≤ 2 ^ bits) (he : e.natAbs ≤ 2 ^ bits) :
    productPeak divide n d m e k₁ k₂ k₃ ≤ 81 * (bits + 1) := by
  have hs := product_context_bits divide n d m e bits hn hd hm he
  have hc := signed_context_bits (productContext divide n d m e) (3 * bits + 1) hs
  change signedPayloadBits (productContext divide n d m e) ≤ 16 * (3 * bits + 2) at hc
  have h₁ := gcd_peak_bits n m bits k₁ hn hm
  have h₂ := gcd_peak_bits d e bits k₂ hd he
  have h₃ := gcd_peak_bits n e bits k₁ hn he
  have h₄ := gcd_peak_bits m d bits k₂ hm hd
  cases divide with
  | false =>
    unfold productPeak
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply Nat.le_trans (Nat.add_le_add hc (max_le h₃ (max_le h₄ (by omega))))
    omega
  | true =>
    have hz := hs (n / (Int.gcd n m : Int) * (e / (Int.gcd d e : Int))) (by simp [productContext])
    have hw := hs (d / (Int.gcd d e : Int) * (m / (Int.gcd n m : Int))) (by simp [productContext])
    have hnrm := normalize_peak_bits _ _ (3 * bits + 1) k₃ hz hw
    change normalizePeak _ _ k₃ ≤ 11 * (3 * bits + 2) at hnrm
    unfold productPeak
    simp only [↓reduceIte]
    apply Nat.le_trans (Nat.add_le_add hc (max_le (by omega) (max_le (by omega) hnrm)))
    omega

/-- Original operand fields retained around a copied/scalar-converted call. -/
def wrapperPeak (n d m e : Int) (calleePeak : Nat) : Nat :=
  signedPayloadBits [n, d, m, e] + calleePeak

theorem wrapper_peak_bits (n d m e : Int) (bits callee bound : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits)
    (hm : m.natAbs ≤ 2 ^ bits) (he : e.natAbs ≤ 2 ^ bits)
    (hcallee : callee ≤ bound * (bits + 1)) :
    wrapperPeak n d m e callee ≤ (bound + 8) * (bits + 1) := by
  have hc : ∀ value ∈ [n, d, m, e], value.natAbs ≤ 2 ^ bits := by
    intro value hv
    simp at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hn
    · exact hd
    · exact hm
    · exact he
  have hs := signed_context_bits [n, d, m, e] bits hc
  change signedPayloadBits [n, d, m, e] ≤ 8 * (bits + 1) at hs
  unfold wrapperPeak
  rw [Nat.add_mul]
  omega

theorem additive_wrapper_bits (subtract : Bool) (n d m e : Int) (bits k₁ k₂ : Nat)
    (hd0 : d ≠ 0) (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits)
    (hm : m.natAbs ≤ 2 ^ bits) (he : e.natAbs ≤ 2 ^ bits) :
    wrapperPeak n d m e (additivePeak subtract n d m e k₁ k₂) ≤ 89 * (bits + 1) := by
  exact wrapper_peak_bits n d m e bits _ 81 hn hd hm he
    (additive_peak_bits subtract n d m e bits k₁ k₂ hd0 hn hd hm he)

theorem product_wrapper_bits (divide : Bool) (n d m e : Int) (bits k₁ k₂ k₃ : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits)
    (hm : m.natAbs ≤ 2 ^ bits) (he : e.natAbs ≤ 2 ^ bits) :
    wrapperPeak n d m e (productPeak divide n d m e k₁ k₂ k₃) ≤ 89 * (bits + 1) := by
  exact wrapper_peak_bits n d m e bits _ 81 hn hd hm he
    (product_peak_bits divide n d m e bits k₁ k₂ k₃ hn hd hm he)

/-- Input and copied result; no histories or heap allocations are modeled. -/
def copyContext (n d : Int) : List Int := [n, d, n, d]

theorem copy_context_bits (n d : Int) (bits : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits) :
    signedPayloadBits (copyContext n d) ≤ 8 * (bits + 1) := by
  exact signed_context_bits _ bits (by
    intro value hv
    simp [copyContext] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> assumption)

/-- Original fields, possible postfix snapshot, and updated fields. -/
def shiftContext (subtract : Bool) (n d : Int) : List Int :=
  [n, d, n, d, if subtract then n - d else n + d, d]

theorem shift_context_bits (subtract : Bool) (n d : Int) (bits : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits) :
    signedPayloadBits (shiftContext subtract n d) ≤ 24 * (bits + 1) := by
  have hi : 2 ^ bits ≤ 2 ^ (bits + 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hz : (if subtract then n - d else n + d).natAbs ≤ 2 ^ (bits + 1) := by
    have ha := Int.natAbs_add_le n d
    have hs := Int.natAbs_add_le n (-d)
    simp only [Int.natAbs_neg, ← Int.sub_eq_add_neg] at hs
    rw [Nat.pow_succ]
    cases subtract
    · exact ha.trans (by omega)
    · exact hs.trans (by omega)
  have hctx : ∀ value ∈ shiftContext subtract n d, value.natAbs ≤ 2 ^ (bits + 1) := by
    intro value hv
    simp [shiftContext] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hn.trans hi
    · exact hd.trans hi
    · exact hn.trans hi
    · exact hd.trans hi
    · exact hz
    · exact hd.trans hi
  have h := signed_context_bits _ (bits + 1) hctx
  change signedPayloadBits (shiftContext subtract n d) ≤ 12 * (bits + 1 + 1) at h
  omega

def compareContext (n d m e : Int) : List Int :=
  let g : Int := Int.gcd d e
  [n, d, m, e, d, e, g, e / g * n, d / g * m]

def comparePeak (n d m e : Int) (k : Nat) : Nat :=
  signedPayloadBits (compareContext n d m e) +
    payloadBits (frame (stateAt k (d.natAbs, e.natAbs)))

theorem compare_context_bits (n d m e : Int) (bits : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits)
    (hm : m.natAbs ≤ 2 ^ bits) (he : e.natAbs ≤ 2 ^ bits) :
    signedPayloadBits (compareContext n d m e) ≤ 36 * (bits + 1) := by
  have hi : 2 ^ bits ≤ 2 ^ (2 * bits) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hg := gcd_size d e (2 ^ bits) hd he
  have hx := scaled_size n (Int.gcd d e : Int) e (2 ^ bits) (2 ^ bits) hn he
  have hy := scaled_size m (Int.gcd d e : Int) d (2 ^ bits) (2 ^ bits) hm hd
  have hp : 2 ^ bits * 2 ^ bits = 2 ^ (2 * bits) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hp] at hx hy
  have hctx : ∀ value ∈ compareContext n d m e, value.natAbs ≤ 2 ^ (2 * bits) := by
    intro value hv
    simp [compareContext] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hn.trans hi
    · exact hd.trans hi
    · exact hm.trans hi
    · exact he.trans hi
    · exact hd.trans hi
    · exact he.trans hi
    · exact hg.trans hi
    · exact hx
    · exact hy
  have h := signed_context_bits _ (2 * bits) hctx
  change signedPayloadBits (compareContext n d m e) ≤ 18 * (2 * bits + 1) at h
  omega

theorem compare_peak_bits (n d m e : Int) (bits k : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits)
    (hm : m.natAbs ≤ 2 ^ bits) (he : e.natAbs ≤ 2 ^ bits) :
    comparePeak n d m e k ≤ 39 * (bits + 1) := by
  have hc := compare_context_bits n d m e bits hn hd hm he
  have hf := (all_frames d.natAbs e.natAbs bits k hd he).2
  unfold comparePeak
  omega

def negatePeak (n d : Int) (k : Nat) : Nat :=
  signedPayloadBits [n, d, -n, d] + normalizePeak (-n) d k

theorem negate_peak_bits (n d : Int) (bits k : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits) :
    negatePeak n d k ≤ 19 * (bits + 1) := by
  have hctx : ∀ value ∈ [n, d, -n, d], value.natAbs ≤ 2 ^ bits := by
    intro value hv
    simp at hv
    rcases hv with rfl | rfl | rfl | rfl <;> simpa only [Int.natAbs_neg] using (by assumption : _)
  have hc := signed_context_bits _ bits hctx
  have hn' : (-n).natAbs ≤ 2 ^ bits := by simpa only [Int.natAbs_neg] using hn
  have hf := normalize_peak_bits (-n) d bits k hn' hd
  change signedPayloadBits [n, d, -n, d] ≤ 8 * (bits + 1) at hc
  unfold negatePeak
  dsimp only [normalizePeak] at *
  omega

def constructPeak (n d : Int) (k : Nat) : Nat :=
  signedPayloadBits (copyContext n d) + normalizePeak n d k

theorem construct_peak_bits (n d : Int) (bits k : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits) :
    constructPeak n d k ≤ 19 * (bits + 1) := by
  have hc := copy_context_bits n d bits hn hd
  have hf := normalize_peak_bits n d bits k hn hd
  unfold constructPeak
  dsimp only [normalizePeak] at *
  omega

theorem equality_context_bits (n d m e : Int) (bits : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits)
    (hm : m.natAbs ≤ 2 ^ bits) (he : e.natAbs ≤ 2 ^ bits) :
    signedPayloadBits [n, d, m, e] ≤ 8 * (bits + 1) := by
  exact signed_context_bits _ bits (by
    intro value hv
    simp at hv
    rcases hv with rfl | rfl | rfl | rfl <;> assumption)

end Proofs.Cpp.RatioArithmeticSpace
