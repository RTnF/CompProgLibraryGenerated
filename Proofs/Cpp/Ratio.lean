import Proofs.Cpp.Gen.Ratio
import Proofs.Cpp.Lib.Basic
import Proofs.Cpp.Lib.RatioMath
import Proofs.Cpp.Lib.RatioCost
import Proofs.Cpp.Lib.RatioSpace
import Proofs.Cpp.Lib.RatioArithmeticSpace
import Proofs.Cpp.Lib.UnsignedMagnitude

/-! Complete original Ratio API, translated from the public header.
Pure rational models, work and logical payload bounds are in Lib.Ratio*. -/

namespace Proofs.Cpp.Ratio

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

theorem ratio_euclid_log_bound (a b : Nat) :
    gcdCost a b ≤ 2 + Nat.log2 (a * b) := by
  simp only [gcdCost]
  split_ifs <;> omega

@[spec] theorem ratio_gcd_nonneg (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (hbound : b.toNat < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.numeric_gcd_nonnegative a b
    ⦃⇓ r c => ⌜r = (Int.gcd a b : Int) ∧
      c ≤ t0 + 2 + gcdCost a.toNat b.toNat⌝⦄ := by
  mvcgen [cp.Ratio.numeric_gcd_nonnegative]
  case inv =>
    exact ⟨fun ⟨x, y⟩ c => ⌜0 ≤ x ∧ 0 ≤ y ∧
      Int.gcd x y = Int.gcd a b ∧
      c + gcdCost x.toNat y.toNat ≤ t0 + 1 + gcdCost a.toNat b.toNat⌝,
      fun ⟨x, _⟩ c => ⌜x = (Int.gcd a b : Int) ∧
        c ≤ t0 + 2 + gcdCost a.toNat b.toNat⌝,
      fun ⟨_, y⟩ => y.toNat⟩
  all_goals simp +zetaDelta [fuel] at *
  · obtain ⟨hx, hy, hg, hc⟩ := ‹_ ∧ _›
    have hz : (‹Int × Int›).2 = 0 := ‹_›
    simp only [hz, Int.gcd_zero_right] at hg
    have hv : (‹Int × Int›).1 = (Int.gcd a b : Int) := by
      rw [← hg, Int.natAbs_of_nonneg hx]
    simp only [hz, Int.toNat_zero, gcdCost_zero] at hc
    exact ⟨hv, by omega⟩
  · obtain ⟨hx, hy, hg, hc⟩ := ‹_ ∧ _›
    have hn : (‹Int × Int›).2 ≠ 0 := ‹_›
    have hp : 0 < (‹Int × Int›).2 := by omega
    have hr := Int.emod_nonneg (‹Int × Int›).1 hn
    have hlt := Int.emod_lt_of_pos (‹Int × Int›).1 hp
    have hcost := gcdCost_step (‹Int × Int›).1.toNat (‹Int × Int›).2.toNat (by omega)
    rw [← Int.toNat_emod hx hy] at hcost
    have hrec : Int.gcd (‹Int × Int›).2 ((‹Int × Int›).1 % (‹Int × Int›).2) = Int.gcd a b := by
      rw [← hg]
      simp only [Int.gcd]
      have hxabs : (‹Int × Int›).1.natAbs = (‹Int × Int›).1.toNat := by omega
      have hyabs : (‹Int × Int›).2.natAbs = (‹Int × Int›).2.toNat := by omega
      have hrabs : ((‹Int × Int›).1 % (‹Int × Int›).2).natAbs =
          ((‹Int × Int›).1 % (‹Int × Int›).2).toNat := by omega
      rw [hxabs, hyabs, hrabs, Int.toNat_emod hx hy]
      conv_lhs => rw [Nat.gcd_comm]
      rw [← Nat.gcd_rec]
      exact Nat.gcd_comm _ _
    exact ⟨⟨hy, hr, hrec, by omega⟩, hlt, hp⟩
  · exact ⟨⟨ha, hb, by omega⟩, hbound⟩
  · exact ‹_ ∧ _›

/-- Magnitudes fit the existing bounded while semantics (all signed 64-bit inputs). -/
@[spec] theorem ratio_gcd_signed (a b : Int) (hbound : b.natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.numeric_gcd a b
    ⦃⇓ r c => ⌜r = (Int.gcd a b : Int) ∧
      c ≤ t0 + 3 + gcdCost a.natAbs b.natAbs⌝⦄ := by
  mvcgen [cp.Ratio.numeric_gcd]
  all_goals simp_all +zetaDelta [fuel]
  all_goals have haabs : (0 ≤ a → a.toNat = a.natAbs) ∧
      (a < 0 → (-a).toNat = a.natAbs) := by constructor <;> intro h <;> omega
  all_goals have hbabs : (0 ≤ b → b.toNat = b.natAbs) ∧
      (b < 0 → (-b).toNat = b.natAbs) := by constructor <;> intro h <;> omega
  all_goals simp_all
  all_goals omega

@[spec] theorem ratio_lcm_signed (a b : Int) (hbound : b.natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.numeric_lcm a b
    ⦃⇓ r c => ⌜r = (Int.lcm a b : Int) ∧
      c ≤ t0 + 3 + gcdCost a.natAbs b.natAbs⌝⦄ := by
  mvcgen [cp.Ratio.numeric_lcm]
  all_goals simp_all +zetaDelta [fuel]
  all_goals have haabs : (0 ≤ a → a.toNat = a.natAbs) ∧
      (a < 0 → (-a).toNat = a.natAbs) := by constructor <;> intro h <;> omega
  all_goals have hbabs : (0 ≤ b → b.toNat = b.natAbs) ∧
      (b < 0 → (-b).toNat = b.natAbs) := by constructor <;> intro h <;> omega
  all_goals have hf := Proofs.Cpp.RatioMath.lcm_magnitude_formula a b
  all_goals have han : (a.natAbs : Int) = if 0 ≤ a then a else -a := by split <;> omega
  all_goals have hbn : (b.natAbs : Int) = if 0 ≤ b then b else -b := by split <;> omega
  all_goals rw [han, hbn] at hf
  all_goals simp_all
  all_goals first
    | (have hz : a = 0 ∨ b = 0 := by assumption
       rcases hz with hz | hz <;> simp_all [Int.lcm_def] <;> omega)
    | omega
    | (split_ifs at hf <;> omega)

-- Appended to the freshly generated complete original Ratio model by
-- tests/test_ratio_stream_model.py. All stream operations and their costs are parameters.
open Proofs.Cpp Proofs.Cpp.Gen

theorem ratio_extract_contract {T : Type} [Streams] [StreamRead T]
    (input : IStream) (r : cp.Ratio T) :
    cp.op_shr_istream_Ratio input r = (do
      tick
      let (n, input) ← StreamRead.read input r.n
      let (d, input) ← StreamRead.read input r.d
      pure (input, input, (⟨n, d⟩ : cp.Ratio T))) := by
  rfl

theorem ratio_insert_contract {T : Type} [Streams] [One T] [LT T] [DecidableLT T]
    [StreamWrite T] [StreamWrite StreamChar] (output : OStream) (r : cp.Ratio T) :
    cp.op_shl_ostream_Ratio output r = (do
      tick
      let mut output ← StreamWrite.write output r.n
      if decide (r.d > (1 : T)) then
        output ← StreamWrite.write output (⟨47⟩ : StreamChar)
        output ← StreamWrite.write output r.d
      pure (output, output)) := by
  rfl

open Std.Do

theorem ratio_extract_run {T : Type} [Streams] [StreamRead T]
    (input input₁ input₂ : IStream) (r : cp.Ratio T) (n d : T) (t0 c₁ c₂ : Nat)
    (hn : (StreamRead.read input r.n).run (t0 + 1) = some ((n, input₁), c₁))
    (hd : (StreamRead.read input₁ r.d).run c₁ = some ((d, input₂), c₂)) :
    (cp.op_shr_istream_Ratio input r).run t0 =
      some ((input₂, input₂, (⟨n, d⟩ : cp.Ratio T)), c₂) := by
  rw [ratio_extract_contract]
  change Option.bind ((StreamRead.read input r.n).run (t0 + 1)) (fun a =>
    Option.bind ((StreamRead.read a.1.2 r.d).run a.2)
      (fun b => some ((b.1.2, b.1.2, (⟨a.1.1, b.1.1⟩ : cp.Ratio T)), b.2))) = _
  rw [hn]
  simp only [Option.bind_some]
  rw [hd]
  rfl

theorem ratio_insert_integer_run {T : Type} [Streams] [One T] [LT T] [DecidableLT T]
    [StreamWrite T] [StreamWrite StreamChar] (output output₁ : OStream)
    (r : cp.Ratio T) (t0 c₁ : Nat) (hshort : ¬r.d > (1 : T))
    (hn : (StreamWrite.write output r.n).run (t0 + 1) = some (output₁, c₁)) :
    (cp.op_shl_ostream_Ratio output r).run t0 = some ((output₁, output₁), c₁) := by
  simp only [ratio_insert_contract, hshort, decide_false, Bool.false_eq_true, ↓reduceIte]
  change Option.bind ((StreamWrite.write output r.n).run (t0 + 1))
    (fun a => some ((a.1, a.1), a.2)) = _
  rw [hn]
  rfl

theorem ratio_insert_fraction_run {T : Type} [Streams] [One T] [LT T] [DecidableLT T]
    [StreamWrite T] [StreamWrite StreamChar] (output output₁ output₂ output₃ : OStream)
    (r : cp.Ratio T) (t0 c₁ c₂ c₃ : Nat) (hlong : r.d > (1 : T))
    (hn : (StreamWrite.write output r.n).run (t0 + 1) = some (output₁, c₁))
    (hslash : (StreamWrite.write output₁ (⟨47⟩ : StreamChar)).run c₁ = some (output₂, c₂))
    (hd : (StreamWrite.write output₂ r.d).run c₂ = some (output₃, c₃)) :
    (cp.op_shl_ostream_Ratio output r).run t0 = some ((output₃, output₃), c₃) := by
  simp only [ratio_insert_contract, hlong, decide_true, ↓reduceIte]
  change Option.bind ((StreamWrite.write output r.n).run (t0 + 1)) (fun a =>
    Option.bind ((StreamWrite.write a.1 (⟨47⟩ : StreamChar)).run a.2) (fun b =>
      Option.bind ((StreamWrite.write b.1 r.d).run b.2) (fun c => some ((c.1, c.1), c.2)))) = _
  rw [hn]
  simp only [Option.bind_some]
  rw [hslash]
  simp only [Option.bind_some]
  rw [hd]
  rfl

theorem ratio_extract_work {T : Type} [Streams] [StreamRead T]
    (input input₁ input₂ : IStream) (r : cp.Ratio T) (n d : T) (t0 c₁ c₂ work₁ work₂ : Nat)
    (hn : (StreamRead.read input r.n).run (t0 + 1) = some ((n, input₁), c₁))
    (hd : (StreamRead.read input₁ r.d).run c₁ = some ((d, input₂), c₂))
    (hc₁ : c₁ ≤ t0 + 1 + work₁) (hc₂ : c₂ ≤ c₁ + work₂) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.op_shr_istream_Ratio input r
    ⦃⇓ q c => ⌜q = (input₂, input₂, (⟨n, d⟩ : cp.Ratio T)) ∧
      c ≤ t0 + 1 + work₁ + work₂⌝⦄ := by
  exact triple_of_run _ _ (ratio_extract_run input input₁ input₂ r n d t0 c₁ c₂ hn hd)
    ⟨rfl, by omega⟩

theorem ratio_insert_integer_work {T : Type} [Streams] [One T] [LT T] [DecidableLT T]
    [StreamWrite T] [StreamWrite StreamChar] (output output₁ : OStream)
    (r : cp.Ratio T) (t0 c₁ work : Nat) (hshort : ¬r.d > (1 : T))
    (hn : (StreamWrite.write output r.n).run (t0 + 1) = some (output₁, c₁))
    (hc : c₁ ≤ t0 + 1 + work) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.op_shl_ostream_Ratio output r
    ⦃⇓ q c => ⌜q = (output₁, output₁) ∧ c ≤ t0 + 1 + work⌝⦄ := by
  exact triple_of_run _ _ (ratio_insert_integer_run output output₁ r t0 c₁ hshort hn) ⟨rfl, hc⟩

theorem ratio_insert_fraction_work {T : Type} [Streams] [One T] [LT T] [DecidableLT T]
    [StreamWrite T] [StreamWrite StreamChar] (output output₁ output₂ output₃ : OStream)
    (r : cp.Ratio T) (t0 c₁ c₂ c₃ work₁ work₂ work₃ : Nat) (hlong : r.d > (1 : T))
    (hn : (StreamWrite.write output r.n).run (t0 + 1) = some (output₁, c₁))
    (hslash : (StreamWrite.write output₁ (⟨47⟩ : StreamChar)).run c₁ = some (output₂, c₂))
    (hd : (StreamWrite.write output₂ r.d).run c₂ = some (output₃, c₃))
    (hc₁ : c₁ ≤ t0 + 1 + work₁) (hc₂ : c₂ ≤ c₁ + work₂) (hc₃ : c₃ ≤ c₂ + work₃) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.op_shl_ostream_Ratio output r
    ⦃⇓ q c => ⌜q = (output₃, output₃) ∧ c ≤ t0 + 1 + work₁ + work₂ + work₃⌝⦄ := by
  exact triple_of_run _ _
    (ratio_insert_fraction_run output output₁ output₂ output₃ r t0 c₁ c₂ c₃ hlong hn hslash hd)
    ⟨rfl, by omega⟩

/-- Fixed integer fields retained by extraction, plus the larger of the two
sequential stream-operation peaks. Stream buffers belong to those contracts. -/
theorem ratio_extract_payload (oldn oldd n d : Int) (bits first second peak : Nat)
    (holdn : oldn.natAbs ≤ 2 ^ bits) (holdd : oldd.natAbs ≤ 2 ^ bits)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits)
    (hfirst : first ≤ peak) (hsecond : second ≤ peak) :
    RatioSpace.signedPayloadBits [oldn, oldd, n, d] + max first second ≤
      8 * (bits + 1) + peak := by
  exact Nat.add_le_add
    (RatioArithmeticSpace.equality_context_bits oldn oldd n d bits holdn holdd hn hd)
    (max_le hfirst hsecond)

/-- Output retains a fixed envelope of integer values; stream-operation peaks
are composed by maximum, not by the number of characters already emitted. -/
theorem ratio_insert_payload (n d : Int) (bits first slash last peak : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits)
    (hfirst : first ≤ peak) (hslash : slash ≤ peak) (hlast : last ≤ peak) :
    RatioSpace.signedPayloadBits (RatioArithmeticSpace.copyContext n d) +
      max first (max slash last) ≤ 8 * (bits + 1) + peak := by
  exact Nat.add_le_add (RatioArithmeticSpace.copy_context_bits n d bits hn hd)
    (max_le hfirst (max_le hslash hlast))

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

@[spec] theorem ratio_euclid_normalize (n d : Int) (hbound : d.natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.normalize (⟨n, d⟩ : cp.Ratio Int)
    ⦃⇓ q c => ⌜(q.n, q.d) = RatioMath.normalize n d ∧
      c ≤ t0 + 4 + gcdCost n.natAbs d.natAbs⌝⦄ := by
  mvcgen [cp.Ratio.normalize]
  all_goals simp_all +zetaDelta [RatioMath.normalize, fuel, Int.gcd]
  all_goals omega

@[spec] theorem ratio_euclid_init (n d : Int) (hbound : d.natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.init_T_T n d
    ⦃⇓ q c => ⌜(q.n, q.d) = RatioMath.normalize n d ∧
      c ≤ t0 + 5 + gcdCost n.natAbs d.natAbs⌝⦄ := by
  mvcgen [cp.Ratio.init_T_T]
  all_goals simp_all +zetaDelta
  all_goals omega

@[spec] theorem ratio_euclid_negate (n d : Int) (hbound : d.natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_sub (⟨n, d⟩ : cp.Ratio Int)
    ⦃⇓ q c => ⌜(q.n, q.d) = RatioMath.normalize (-n) d ∧
      c ≤ t0 + 6 + gcdCost n.natAbs d.natAbs⌝⦄ := by
  mvcgen [cp.Ratio.op_sub]
  all_goals simp_all +zetaDelta
  all_goals omega

@[spec] theorem ratio_euclid_multiply (n d m e : Int)
    (hd : d.natAbs < fuel) (he : e.natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_mul_assign (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)
    ⦃⇓ q c => ⌜q.1 = q.2 ∧ (q.1.n, q.1.d) = RatioMath.mul n d m e ∧
      c ≤ t0 + 7 + gcdCost n.natAbs e.natAbs + gcdCost m.natAbs d.natAbs⌝⦄ := by
  mvcgen [cp.Ratio.op_mul_assign]
  all_goals simp_all +zetaDelta [RatioMath.mul, Int.gcd]
  all_goals omega

@[spec] theorem ratio_euclid_add (n d m e : Int)
    (he : e.natAbs < fuel) (hl : (Int.lcm d e : Int).natAbs < fuel) (t0 : Nat) :
    let l : Int := Int.lcm d e
    let z := l / d * n + l / e * m
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_add_assign (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)
    ⦃⇓ q c => ⌜q.1 = q.2 ∧ (q.1.n, q.1.d) = RatioMath.add n d m e ∧
      c ≤ t0 + 8 + gcdCost d.natAbs e.natAbs + gcdCost z.natAbs l.natAbs⌝⦄ := by
  dsimp only
  mvcgen [cp.Ratio.op_add_assign]
  all_goals simp_all +zetaDelta [RatioMath.add]
  all_goals omega

@[spec] theorem ratio_euclid_sub (n d m e : Int)
    (he : e.natAbs < fuel) (hl : (Int.lcm d e : Int).natAbs < fuel) (t0 : Nat) :
    let l : Int := Int.lcm d e
    let z := l / d * n - l / e * m
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_sub_assign (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)
    ⦃⇓ q c => ⌜q.1 = q.2 ∧ (q.1.n, q.1.d) = RatioMath.sub n d m e ∧
      c ≤ t0 + 8 + gcdCost d.natAbs e.natAbs + gcdCost z.natAbs l.natAbs⌝⦄ := by
  dsimp only
  mvcgen [cp.Ratio.op_sub_assign]
  all_goals simp_all +zetaDelta [RatioMath.sub]
  all_goals omega

@[spec] theorem ratio_euclid_divide (n d m e : Int)
    (hm : m ≠ 0) (hmb : m.natAbs < fuel) (he : e.natAbs < fuel)
    (hw : (d / (Int.gcd d e : Int) * (m / (Int.gcd n m : Int))).natAbs < fuel) (t0 : Nat) :
    let z := n / (Int.gcd n m : Int) * (e / (Int.gcd d e : Int))
    let w := d / (Int.gcd d e : Int) * (m / (Int.gcd n m : Int))
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_div_assign (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)
    ⦃⇓ q c => ⌜q.1 = q.2 ∧ (q.1.n, q.1.d) = RatioMath.div n d m e ∧
      c ≤ t0 + 11 + gcdCost n.natAbs m.natAbs + gcdCost d.natAbs e.natAbs +
        gcdCost z.natAbs w.natAbs⌝⦄ := by
  dsimp only
  mvcgen [cp.Ratio.op_div_assign]
  all_goals simp_all +zetaDelta [RatioMath.div]
  all_goals omega

@[spec] theorem ratio_euclid_compare (n d m e : Int) (he : e.natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_cmp (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)
    ⦃⇓ q c => ⌜q = (if e / (Int.gcd d e : Int) * n < d / (Int.gcd d e : Int) * m then Ordering.lt
      else if d / (Int.gcd d e : Int) * m < e / (Int.gcd d e : Int) * n then Ordering.gt else Ordering.eq) ∧
      c ≤ t0 + 4 + gcdCost d.natAbs e.natAbs⌝⦄ := by
  mvcgen [cp.Ratio.op_cmp]
  all_goals simp_all +zetaDelta
  all_goals omega

theorem ratio_euclid_add_Ratio_Ratio_run {T : Type} [Zero T] [One T] [Add T] [Mul T] [Neg T] [Div T] [Mod T] [LT T] [DecidableLT T] [DecidableEq T] (a : (cp.Ratio T)) (b : (cp.Ratio T)) (t : Nat) :
    (cp.op_add_Ratio_Ratio a b).run t =
      Option.bind ((cp.Ratio.op_add_assign a b).run (t + 1))
        (fun result => some (result.1.1, result.2)) := by
  rfl

theorem ratio_euclid_add_Ratio_T_run {T : Type} [Zero T] [One T] [Add T] [Mul T] [Neg T] [Div T] [Mod T] [LT T] [DecidableLT T] [DecidableEq T] (a : (cp.Ratio T)) (b : T) (t : Nat) :
    (cp.op_add_Ratio_T a b).run t =
      Option.bind ((cp.Ratio.op_add_assign a (⟨b, 1⟩ : cp.Ratio T)).run (t + 2))
        (fun result => some (result.1.1, result.2)) := by
  rfl

theorem ratio_euclid_add_T_Ratio_run {T : Type} [Zero T] [One T] [Add T] [Mul T] [Neg T] [Div T] [Mod T] [LT T] [DecidableLT T] [DecidableEq T] (a : T) (b : (cp.Ratio T)) (t : Nat) :
    (cp.op_add_T_Ratio a b).run t =
      Option.bind ((cp.Ratio.op_add_assign (⟨a, 1⟩ : cp.Ratio T) b).run (t + 2))
        (fun result => some (result.1.1, result.2)) := by
  rfl

theorem ratio_euclid_sub_Ratio_Ratio_run {T : Type} [Zero T] [One T] [Sub T] [Mul T] [Neg T] [Div T] [Mod T] [LT T] [DecidableLT T] [DecidableEq T] (a : (cp.Ratio T)) (b : (cp.Ratio T)) (t : Nat) :
    (cp.op_sub_Ratio_Ratio a b).run t =
      Option.bind ((cp.Ratio.op_sub_assign a b).run (t + 1))
        (fun result => some (result.1.1, result.2)) := by
  rfl

theorem ratio_euclid_sub_Ratio_T_run {T : Type} [Zero T] [One T] [Sub T] [Mul T] [Neg T] [Div T] [Mod T] [LT T] [DecidableLT T] [DecidableEq T] (a : (cp.Ratio T)) (b : T) (t : Nat) :
    (cp.op_sub_Ratio_T a b).run t =
      Option.bind ((cp.Ratio.op_sub_assign a (⟨b, 1⟩ : cp.Ratio T)).run (t + 2))
        (fun result => some (result.1.1, result.2)) := by
  rfl

theorem ratio_euclid_sub_T_Ratio_run {T : Type} [Zero T] [One T] [Sub T] [Mul T] [Neg T] [Div T] [Mod T] [LT T] [DecidableLT T] [DecidableEq T] (a : T) (b : (cp.Ratio T)) (t : Nat) :
    (cp.op_sub_T_Ratio a b).run t =
      Option.bind ((cp.Ratio.op_sub_assign (⟨a, 1⟩ : cp.Ratio T) b).run (t + 2))
        (fun result => some (result.1.1, result.2)) := by
  rfl

theorem ratio_euclid_mul_Ratio_Ratio_run {T : Type} [Zero T] [Mul T] [Neg T] [Div T] [Mod T] [LT T] [DecidableLT T] [DecidableEq T] (a : (cp.Ratio T)) (b : (cp.Ratio T)) (t : Nat) :
    (cp.op_mul_Ratio_Ratio a b).run t =
      Option.bind ((cp.Ratio.op_mul_assign a b).run (t + 1))
        (fun result => some (result.1.1, result.2)) := by
  rfl

theorem ratio_euclid_mul_Ratio_T_run {T : Type} [Zero T] [One T] [Mul T] [Neg T] [Div T] [Mod T] [LT T] [DecidableLT T] [DecidableEq T] (a : (cp.Ratio T)) (b : T) (t : Nat) :
    (cp.op_mul_Ratio_T a b).run t =
      Option.bind ((cp.Ratio.op_mul_assign a (⟨b, 1⟩ : cp.Ratio T)).run (t + 2))
        (fun result => some (result.1.1, result.2)) := by
  rfl

theorem ratio_euclid_mul_T_Ratio_run {T : Type} [Zero T] [One T] [Mul T] [Neg T] [Div T] [Mod T] [LT T] [DecidableLT T] [DecidableEq T] (a : T) (b : (cp.Ratio T)) (t : Nat) :
    (cp.op_mul_T_Ratio a b).run t =
      Option.bind ((cp.Ratio.op_mul_assign (⟨a, 1⟩ : cp.Ratio T) b).run (t + 2))
        (fun result => some (result.1.1, result.2)) := by
  rfl

theorem ratio_euclid_div_Ratio_Ratio_run {T : Type} [Zero T] [One T] [Mul T] [Neg T] [Div T] [Mod T] [LT T] [DecidableLT T] [DecidableEq T] (a : (cp.Ratio T)) (b : (cp.Ratio T)) (t : Nat) :
    (cp.op_div_Ratio_Ratio a b).run t =
      Option.bind ((cp.Ratio.op_div_assign a b).run (t + 1))
        (fun result => some (result.1.1, result.2)) := by
  rfl

theorem ratio_euclid_div_Ratio_T_run {T : Type} [Zero T] [One T] [Mul T] [Neg T] [Div T] [Mod T] [LT T] [DecidableLT T] [DecidableEq T] (a : (cp.Ratio T)) (b : T) (t : Nat) :
    (cp.op_div_Ratio_T a b).run t =
      Option.bind ((cp.Ratio.op_div_assign a (⟨b, 1⟩ : cp.Ratio T)).run (t + 2))
        (fun result => some (result.1.1, result.2)) := by
  rfl

theorem ratio_euclid_div_T_Ratio_run {T : Type} [Zero T] [One T] [Mul T] [Neg T] [Div T] [Mod T] [LT T] [DecidableLT T] [DecidableEq T] (a : T) (b : (cp.Ratio T)) (t : Nat) :
    (cp.op_div_T_Ratio a b).run t =
      Option.bind ((cp.Ratio.op_div_assign (⟨a, 1⟩ : cp.Ratio T) b).run (t + 2))
        (fun result => some (result.1.1, result.2)) := by
  rfl

theorem ratio_euclid_init_scalar_run {T : Type} [One T] (n : T) (t : Nat) :
    (cp.Ratio.init_T n).run t = some ((⟨n, 1⟩ : cp.Ratio T), t + 1) := by
  rfl

theorem ratio_euclid_prefix_increment_run {T : Type} [Add T] (n d : T) (t : Nat) :
    (cp.Ratio.op_inc_0 (⟨n, d⟩ : cp.Ratio T)).run t =
      some (((⟨n + d, d⟩ : cp.Ratio T), (⟨n + d, d⟩ : cp.Ratio T)), t + 1) := by
  rfl

theorem ratio_euclid_postfix_increment_run {T : Type} [Add T] (n d : T) (tag : Int) (t : Nat) :
    (cp.Ratio.op_inc_int (⟨n, d⟩ : cp.Ratio T) tag).run t =
      some (((⟨n, d⟩ : cp.Ratio T), (⟨n + d, d⟩ : cp.Ratio T)), t + 2) := by
  rfl

theorem ratio_euclid_prefix_decrement_run {T : Type} [Sub T] (n d : T) (t : Nat) :
    (cp.Ratio.op_dec_0 (⟨n, d⟩ : cp.Ratio T)).run t =
      some (((⟨n - d, d⟩ : cp.Ratio T), (⟨n - d, d⟩ : cp.Ratio T)), t + 1) := by
  rfl

theorem ratio_euclid_postfix_decrement_run {T : Type} [Sub T] (n d : T) (tag : Int) (t : Nat) :
    (cp.Ratio.op_dec_int (⟨n, d⟩ : cp.Ratio T) tag).run t =
      some (((⟨n, d⟩ : cp.Ratio T), (⟨n - d, d⟩ : cp.Ratio T)), t + 2) := by
  rfl

theorem ratio_euclid_unary_plus_run {T : Type} (n d : T) (t : Nat) :
    (cp.Ratio.op_add (⟨n, d⟩ : cp.Ratio T)).run t =
      some ((⟨n, d⟩ : cp.Ratio T), t + 1) := by
  rfl

theorem ratio_euclid_equal_run {T : Type} [DecidableEq T] (n d m e : T) (t : Nat) :
    (cp.Ratio.op_eq (⟨n, d⟩ : cp.Ratio T) (⟨m, e⟩ : cp.Ratio T)).run t =
      some (decide (n = m ∧ d = e), t + 1) := by
  rfl

theorem ratio_euclid_equal_normalized_value (n d m e : Int)
    (hd : d ≠ 0) (he : e ≠ 0) (t : Nat) :
    let p := RatioMath.normalize n d
    let q := RatioMath.normalize m e
    (cp.Ratio.op_eq (⟨p.1, p.2⟩ : cp.Ratio Int) (⟨q.1, q.2⟩ : cp.Ratio Int)).run t =
      some (decide (Rat.divInt n d = Rat.divInt m e), t + 1) := by
  dsimp only
  rw [ratio_euclid_equal_run]
  have h := RatioMath.normalize_eq_iff n d m e hd he
  rw [Prod.ext_iff] at h
  simp only [h]

theorem ratio_euclid_div_zero_run (n d e : Int) (t : Nat) :
    (cp.Ratio.op_div_assign (⟨n, d⟩ : cp.Ratio Int) (⟨0, e⟩ : cp.Ratio Int)).run t = none := by
  rfl

theorem ratio_euclid_div_Ratio_Ratio_zero (n d e : Int) (t : Nat) :
    (cp.op_div_Ratio_Ratio (⟨n, d⟩ : cp.Ratio Int) (⟨0, e⟩ : cp.Ratio Int)).run t = none := by
  rw [ratio_euclid_div_Ratio_Ratio_run, ratio_euclid_div_zero_run]
  rfl

theorem ratio_euclid_div_Ratio_T_zero (n d : Int) (t : Nat) :
    (cp.op_div_Ratio_T (⟨n, d⟩ : cp.Ratio Int) 0).run t = none := by
  rw [ratio_euclid_div_Ratio_T_run, ratio_euclid_div_zero_run]
  rfl

theorem ratio_euclid_div_T_Ratio_zero (a e : Int) (t : Nat) :
    (cp.op_div_T_Ratio a (⟨0, e⟩ : cp.Ratio Int)).run t = none := by
  rw [ratio_euclid_div_T_Ratio_run, ratio_euclid_div_zero_run]
  rfl

/-- Work is O(bits + 1) when the operand magnitudes have a common bit bound. -/
theorem ratio_euclid_normalize_bits (n d : Int) (bits : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits)
    (hbound : d.natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.normalize (⟨n, d⟩ : cp.Ratio Int)
    ⦃⇓ q c => ⌜(q.n, q.d) = RatioMath.normalize n d ∧
      c ≤ t0 + 6 * (bits + 1)⌝⦄ := by
  have hg := RatioCost.gcd_bits n.natAbs d.natAbs bits hn hd
  mvcgen
  all_goals simp_all +zetaDelta
  all_goals omega

theorem ratio_euclid_multiply_bits (n d m e : Int) (bits : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits)
    (hm : m.natAbs ≤ 2 ^ bits) (he : e.natAbs ≤ 2 ^ bits)
    (hdb : d.natAbs < fuel) (heb : e.natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_mul_assign (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)
    ⦃⇓ q c => ⌜q.1 = q.2 ∧ (q.1.n, q.1.d) = RatioMath.mul n d m e ∧
      c ≤ t0 + 11 * (bits + 1)⌝⦄ := by
  have hg1 := RatioCost.gcd_bits n.natAbs e.natAbs bits hn he
  have hg2 := RatioCost.gcd_bits m.natAbs d.natAbs bits hm hd
  mvcgen
  all_goals simp_all +zetaDelta
  all_goals omega

theorem ratio_euclid_add_bits (n d m e : Int) (bits : Nat)
    (he : e.natAbs < fuel) (hl : (Int.lcm d e : Int).natAbs < fuel) (t0 : Nat) :
    let l : Int := Int.lcm d e
    let z := l / d * n + l / e * m
    (∀ x ∈ [d, e, z, l], x.natAbs ≤ 2 ^ bits) →
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_add_assign (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)
    ⦃⇓ q c => ⌜q.1 = q.2 ∧ (q.1.n, q.1.d) = RatioMath.add n d m e ∧
      c ≤ t0 + 12 * (bits + 1)⌝⦄ := by
  dsimp only
  intro hs
  have hg1 := RatioCost.gcd_bits d.natAbs e.natAbs bits
    (hs d (by simp)) (hs e (by simp))
  have hg2 := RatioCost.gcd_bits
    (((Int.lcm d e : Int) / d * n + (Int.lcm d e : Int) / e * m).natAbs)
    ((Int.lcm d e : Int).natAbs) bits (hs _ (by simp)) (hs _ (by simp))
  mvcgen
  all_goals simp_all +zetaDelta
  all_goals omega

theorem ratio_euclid_sub_bits (n d m e : Int) (bits : Nat)
    (he : e.natAbs < fuel) (hl : (Int.lcm d e : Int).natAbs < fuel) (t0 : Nat) :
    let l : Int := Int.lcm d e
    let z := l / d * n - l / e * m
    (∀ x ∈ [d, e, z, l], x.natAbs ≤ 2 ^ bits) →
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_sub_assign (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)
    ⦃⇓ q c => ⌜q.1 = q.2 ∧ (q.1.n, q.1.d) = RatioMath.sub n d m e ∧
      c ≤ t0 + 12 * (bits + 1)⌝⦄ := by
  dsimp only
  intro hs
  have hg1 := RatioCost.gcd_bits d.natAbs e.natAbs bits
    (hs d (by simp)) (hs e (by simp))
  have hg2 := RatioCost.gcd_bits
    (((Int.lcm d e : Int) / d * n - (Int.lcm d e : Int) / e * m).natAbs)
    ((Int.lcm d e : Int).natAbs) bits (hs _ (by simp)) (hs _ (by simp))
  mvcgen
  all_goals simp_all +zetaDelta
  all_goals omega

theorem ratio_euclid_divide_bits (n d m e : Int) (bits : Nat)
    (hm : m ≠ 0) (hmb : m.natAbs < fuel) (he : e.natAbs < fuel)
    (hw : (d / (Int.gcd d e : Int) * (m / (Int.gcd n m : Int))).natAbs < fuel) (t0 : Nat) :
    let z := n / (Int.gcd n m : Int) * (e / (Int.gcd d e : Int))
    let w := d / (Int.gcd d e : Int) * (m / (Int.gcd n m : Int))
    (∀ x ∈ [n, m, d, e, z, w], x.natAbs ≤ 2 ^ bits) →
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_div_assign (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)
    ⦃⇓ q c => ⌜q.1 = q.2 ∧ (q.1.n, q.1.d) = RatioMath.div n d m e ∧
      c ≤ t0 + 17 * (bits + 1)⌝⦄ := by
  dsimp only
  intro hs
  have hg1 := RatioCost.gcd_bits n.natAbs m.natAbs bits (hs _ (by simp)) (hs _ (by simp))
  have hg2 := RatioCost.gcd_bits d.natAbs e.natAbs bits (hs _ (by simp)) (hs _ (by simp))
  have hg3 := RatioCost.gcd_bits
    ((n / (Int.gcd n m : Int) * (e / (Int.gcd d e : Int))).natAbs)
    ((d / (Int.gcd d e : Int) * (m / (Int.gcd n m : Int))).natAbs) bits
    (hs _ (by simp)) (hs _ (by simp))
  mvcgen
  all_goals simp_all +zetaDelta
  all_goals omega

/-- Only original operand sizes occur in the bit bound; fuel is a model-domain premise. -/
theorem ratio_euclid_add_input_bits (n d m e : Int) (bits : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits)
    (hm : m.natAbs ≤ 2 ^ bits) (he : e.natAbs ≤ 2 ^ bits)
    (heb : e.natAbs < fuel) (hlb : (Int.lcm d e : Int).natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_add_assign (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)
    ⦃⇓ q c => ⌜q.1 = q.2 ∧ (q.1.n, q.1.d) = RatioMath.add n d m e ∧
      c ≤ t0 + 16 * (bits + 1)⌝⦄ := by
  have hl := RatioCost.lcm_size d e (2 ^ bits) hd he
  have hz := RatioCost.add_size n d m e (2 ^ bits) hn hd hm he
  rw [RatioCost.cube_bits] at hz
  have hl' := le_trans hl (RatioCost.square_bits_le bits)
  have hg1 := RatioCost.gcd_bits d.natAbs e.natAbs bits hd he
  have hg2 := RatioCost.gcd_bits
    (((Int.lcm d e : Int) / d * n + (Int.lcm d e : Int) / e * m).natAbs)
    ((Int.lcm d e : Int).natAbs) (3 * bits + 1) hz hl'
  mvcgen
  all_goals simp_all +zetaDelta
  all_goals omega

/-- Only original operand sizes occur in the bit bound; fuel is a model-domain premise. -/
theorem ratio_euclid_sub_input_bits (n d m e : Int) (bits : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits)
    (hm : m.natAbs ≤ 2 ^ bits) (he : e.natAbs ≤ 2 ^ bits)
    (heb : e.natAbs < fuel) (hlb : (Int.lcm d e : Int).natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_sub_assign (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)
    ⦃⇓ q c => ⌜q.1 = q.2 ∧ (q.1.n, q.1.d) = RatioMath.sub n d m e ∧
      c ≤ t0 + 16 * (bits + 1)⌝⦄ := by
  have hl := RatioCost.lcm_size d e (2 ^ bits) hd he
  have hz := RatioCost.sub_size n d m e (2 ^ bits) hn hd hm he
  rw [RatioCost.cube_bits] at hz
  have hl' := le_trans hl (RatioCost.square_bits_le bits)
  have hg1 := RatioCost.gcd_bits d.natAbs e.natAbs bits hd he
  have hg2 := RatioCost.gcd_bits
    (((Int.lcm d e : Int) / d * n - (Int.lcm d e : Int) / e * m).natAbs)
    ((Int.lcm d e : Int).natAbs) (3 * bits + 1) hz hl'
  mvcgen
  all_goals simp_all +zetaDelta
  all_goals omega

theorem ratio_euclid_divide_input_bits (n d m e : Int) (bits : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits)
    (hm : m.natAbs ≤ 2 ^ bits) (he : e.natAbs ≤ 2 ^ bits)
    (hm0 : m ≠ 0) (hmb : m.natAbs < fuel) (heb : e.natAbs < fuel)
    (hwb : (d / (Int.gcd d e : Int) * (m / (Int.gcd n m : Int))).natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_div_assign (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)
    ⦃⇓ q c => ⌜q.1 = q.2 ∧ (q.1.n, q.1.d) = RatioMath.div n d m e ∧
      c ≤ t0 + 23 * (bits + 1)⌝⦄ := by
  have hz := RatioCost.quotient_product_size n e (Int.gcd n m) (Int.gcd d e) (2 ^ bits) hn he
  have hw := RatioCost.quotient_product_size d m (Int.gcd d e) (Int.gcd n m) (2 ^ bits) hd hm
  have hz' := le_trans hz (RatioCost.square_bits_le bits)
  have hw' := le_trans hw (RatioCost.square_bits_le bits)
  have hg1 := RatioCost.gcd_bits n.natAbs m.natAbs bits hn hm
  have hg2 := RatioCost.gcd_bits d.natAbs e.natAbs bits hd he
  have hg3 := RatioCost.gcd_bits
    ((n / (Int.gcd n m : Int) * (e / (Int.gcd d e : Int))).natAbs)
    ((d / (Int.gcd d e : Int) * (m / (Int.gcd n m : Int))).natAbs) (3 * bits + 1) hz' hw'
  mvcgen
  all_goals simp_all +zetaDelta
  all_goals omega

theorem ratio_euclid_init_input_bits (n d : Int) (bits : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits)
    (hbound : d.natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.init_T_T n d
    ⦃⇓ q c => ⌜(q.n, q.d) = RatioMath.normalize n d ∧ c ≤ t0 + 7 * (bits + 1)⌝⦄ := by
  have hg := RatioCost.gcd_bits n.natAbs d.natAbs bits hn hd
  mvcgen
  all_goals simp_all +zetaDelta
  all_goals omega

theorem ratio_euclid_negate_input_bits (n d : Int) (bits : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits)
    (hbound : d.natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_sub (⟨n, d⟩ : cp.Ratio Int)
    ⦃⇓ q c => ⌜(q.n, q.d) = RatioMath.normalize (-n) d ∧ c ≤ t0 + 8 * (bits + 1)⌝⦄ := by
  have hg := RatioCost.gcd_bits n.natAbs d.natAbs bits hn hd
  mvcgen
  all_goals simp_all +zetaDelta
  all_goals omega

theorem ratio_euclid_compare_input_bits (n d m e : Int) (bits : Nat)
    (hd : d.natAbs ≤ 2 ^ bits) (he : e.natAbs ≤ 2 ^ bits)
    (hbound : e.natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_cmp (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)
    ⦃⇓ q c => ⌜q = (if e / (Int.gcd d e : Int) * n < d / (Int.gcd d e : Int) * m then Ordering.lt
      else if d / (Int.gcd d e : Int) * m < e / (Int.gcd d e : Int) * n then Ordering.gt else Ordering.eq) ∧
      c ≤ t0 + 6 * (bits + 1)⌝⦄ := by
  have hg := RatioCost.gcd_bits d.natAbs e.natAbs bits hd he
  mvcgen
  all_goals simp_all +zetaDelta
  all_goals omega

theorem ratio_euclid_add_Ratio_Ratio_input_value_bits (n d m e : Int) (bits : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits) (hm : m.natAbs ≤ 2 ^ bits) (he : e.natAbs ≤ 2 ^ bits) (hd0 : d ≠ 0) (he0 : e ≠ 0) (heb : e.natAbs < fuel) (hlb : (Int.lcm d e : Int).natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.op_add_Ratio_Ratio (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)
    ⦃⇓ q c => ⌜Rat.divInt q.n q.d = Rat.divInt n d + Rat.divInt m e ∧
      c ≤ t0 + 18 * (bits + 1)⌝⦄ := by
  obtain ⟨r, c, hr, _, hp, hc⟩ := run_of_triple
    (ratio_euclid_add_input_bits n d m e bits hn hd hm he heb hlb (t0 + 1))
  refine triple_of_run r.1 c ?_ ⟨?_, by omega⟩
  · rw [ratio_euclid_add_Ratio_Ratio_run, hr]
    rfl
  · have hv := congrArg (fun p : Int × Int => Rat.divInt p.1 p.2) hp
    dsimp only at hv
    rw [hv]
    exact RatioMath.add_value n d m e hd0 he0

theorem ratio_euclid_add_Ratio_T_input_value_bits (n d b : Int) (bits : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits) (hb : b.natAbs ≤ 2 ^ bits) (hd0 : d ≠ 0) (hlb : (Int.lcm d 1 : Int).natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.op_add_Ratio_T (⟨n, d⟩ : cp.Ratio Int) b
    ⦃⇓ q c => ⌜Rat.divInt q.n q.d = Rat.divInt n d + Rat.divInt b 1 ∧
      c ≤ t0 + 18 * (bits + 1)⌝⦄ := by
  obtain ⟨r, c, hr, _, hp, hc⟩ := run_of_triple
    (ratio_euclid_add_input_bits n d b 1 bits hn hd hb (by have h := Nat.two_pow_pos bits; omega) (by decide) hlb (t0 + 2))
  refine triple_of_run r.1 c ?_ ⟨?_, by omega⟩
  · rw [ratio_euclid_add_Ratio_T_run, hr]
    rfl
  · have hv := congrArg (fun p : Int × Int => Rat.divInt p.1 p.2) hp
    dsimp only at hv
    rw [hv]
    exact RatioMath.add_value n d b 1 hd0 (by decide)

theorem ratio_euclid_add_T_Ratio_input_value_bits (a m e : Int) (bits : Nat)
    (ha : a.natAbs ≤ 2 ^ bits) (hm : m.natAbs ≤ 2 ^ bits) (he : e.natAbs ≤ 2 ^ bits) (he0 : e ≠ 0) (heb : e.natAbs < fuel) (hlb : (Int.lcm 1 e : Int).natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.op_add_T_Ratio a (⟨m, e⟩ : cp.Ratio Int)
    ⦃⇓ q c => ⌜Rat.divInt q.n q.d = Rat.divInt a 1 + Rat.divInt m e ∧
      c ≤ t0 + 18 * (bits + 1)⌝⦄ := by
  obtain ⟨r, c, hr, _, hp, hc⟩ := run_of_triple
    (ratio_euclid_add_input_bits a 1 m e bits ha (by have h := Nat.two_pow_pos bits; omega) hm he heb hlb (t0 + 2))
  refine triple_of_run r.1 c ?_ ⟨?_, by omega⟩
  · rw [ratio_euclid_add_T_Ratio_run, hr]
    rfl
  · have hv := congrArg (fun p : Int × Int => Rat.divInt p.1 p.2) hp
    dsimp only at hv
    rw [hv]
    exact RatioMath.add_value a 1 m e (by decide) he0

theorem ratio_euclid_sub_Ratio_Ratio_input_value_bits (n d m e : Int) (bits : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits) (hm : m.natAbs ≤ 2 ^ bits) (he : e.natAbs ≤ 2 ^ bits) (hd0 : d ≠ 0) (he0 : e ≠ 0) (heb : e.natAbs < fuel) (hlb : (Int.lcm d e : Int).natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.op_sub_Ratio_Ratio (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)
    ⦃⇓ q c => ⌜Rat.divInt q.n q.d = Rat.divInt n d - Rat.divInt m e ∧
      c ≤ t0 + 18 * (bits + 1)⌝⦄ := by
  obtain ⟨r, c, hr, _, hp, hc⟩ := run_of_triple
    (ratio_euclid_sub_input_bits n d m e bits hn hd hm he heb hlb (t0 + 1))
  refine triple_of_run r.1 c ?_ ⟨?_, by omega⟩
  · rw [ratio_euclid_sub_Ratio_Ratio_run, hr]
    rfl
  · have hv := congrArg (fun p : Int × Int => Rat.divInt p.1 p.2) hp
    dsimp only at hv
    rw [hv]
    exact RatioMath.sub_value n d m e hd0 he0

theorem ratio_euclid_sub_Ratio_T_input_value_bits (n d b : Int) (bits : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits) (hb : b.natAbs ≤ 2 ^ bits) (hd0 : d ≠ 0) (hlb : (Int.lcm d 1 : Int).natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.op_sub_Ratio_T (⟨n, d⟩ : cp.Ratio Int) b
    ⦃⇓ q c => ⌜Rat.divInt q.n q.d = Rat.divInt n d - Rat.divInt b 1 ∧
      c ≤ t0 + 18 * (bits + 1)⌝⦄ := by
  obtain ⟨r, c, hr, _, hp, hc⟩ := run_of_triple
    (ratio_euclid_sub_input_bits n d b 1 bits hn hd hb (by have h := Nat.two_pow_pos bits; omega) (by decide) hlb (t0 + 2))
  refine triple_of_run r.1 c ?_ ⟨?_, by omega⟩
  · rw [ratio_euclid_sub_Ratio_T_run, hr]
    rfl
  · have hv := congrArg (fun p : Int × Int => Rat.divInt p.1 p.2) hp
    dsimp only at hv
    rw [hv]
    exact RatioMath.sub_value n d b 1 hd0 (by decide)

theorem ratio_euclid_sub_T_Ratio_input_value_bits (a m e : Int) (bits : Nat)
    (ha : a.natAbs ≤ 2 ^ bits) (hm : m.natAbs ≤ 2 ^ bits) (he : e.natAbs ≤ 2 ^ bits) (he0 : e ≠ 0) (heb : e.natAbs < fuel) (hlb : (Int.lcm 1 e : Int).natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.op_sub_T_Ratio a (⟨m, e⟩ : cp.Ratio Int)
    ⦃⇓ q c => ⌜Rat.divInt q.n q.d = Rat.divInt a 1 - Rat.divInt m e ∧
      c ≤ t0 + 18 * (bits + 1)⌝⦄ := by
  obtain ⟨r, c, hr, _, hp, hc⟩ := run_of_triple
    (ratio_euclid_sub_input_bits a 1 m e bits ha (by have h := Nat.two_pow_pos bits; omega) hm he heb hlb (t0 + 2))
  refine triple_of_run r.1 c ?_ ⟨?_, by omega⟩
  · rw [ratio_euclid_sub_T_Ratio_run, hr]
    rfl
  · have hv := congrArg (fun p : Int × Int => Rat.divInt p.1 p.2) hp
    dsimp only at hv
    rw [hv]
    exact RatioMath.sub_value a 1 m e (by decide) he0

theorem ratio_euclid_mul_Ratio_Ratio_input_value_bits (n d m e : Int) (bits : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits) (hm : m.natAbs ≤ 2 ^ bits) (he : e.natAbs ≤ 2 ^ bits) (hd0 : d ≠ 0) (he0 : e ≠ 0) (heb : e.natAbs < fuel) (hdb : d.natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.op_mul_Ratio_Ratio (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)
    ⦃⇓ q c => ⌜Rat.divInt q.n q.d = Rat.divInt n d * Rat.divInt m e ∧
      c ≤ t0 + 13 * (bits + 1)⌝⦄ := by
  obtain ⟨r, c, hr, _, hp, hc⟩ := run_of_triple
    (ratio_euclid_multiply_bits n d m e bits hn hd hm he hdb heb (t0 + 1))
  refine triple_of_run r.1 c ?_ ⟨?_, by omega⟩
  · rw [ratio_euclid_mul_Ratio_Ratio_run, hr]
    rfl
  · have hv := congrArg (fun p : Int × Int => Rat.divInt p.1 p.2) hp
    dsimp only at hv
    rw [hv]
    exact RatioMath.mul_value n d m e hd0 he0

theorem ratio_euclid_mul_Ratio_T_input_value_bits (n d b : Int) (bits : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits) (hb : b.natAbs ≤ 2 ^ bits) (hd0 : d ≠ 0) (hdb : d.natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.op_mul_Ratio_T (⟨n, d⟩ : cp.Ratio Int) b
    ⦃⇓ q c => ⌜Rat.divInt q.n q.d = Rat.divInt n d * Rat.divInt b 1 ∧
      c ≤ t0 + 13 * (bits + 1)⌝⦄ := by
  obtain ⟨r, c, hr, _, hp, hc⟩ := run_of_triple
    (ratio_euclid_multiply_bits n d b 1 bits hn hd hb (by have h := Nat.two_pow_pos bits; omega) hdb (by decide) (t0 + 2))
  refine triple_of_run r.1 c ?_ ⟨?_, by omega⟩
  · rw [ratio_euclid_mul_Ratio_T_run, hr]
    rfl
  · have hv := congrArg (fun p : Int × Int => Rat.divInt p.1 p.2) hp
    dsimp only at hv
    rw [hv]
    exact RatioMath.mul_value n d b 1 hd0 (by decide)

theorem ratio_euclid_mul_T_Ratio_input_value_bits (a m e : Int) (bits : Nat)
    (ha : a.natAbs ≤ 2 ^ bits) (hm : m.natAbs ≤ 2 ^ bits) (he : e.natAbs ≤ 2 ^ bits) (he0 : e ≠ 0) (heb : e.natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.op_mul_T_Ratio a (⟨m, e⟩ : cp.Ratio Int)
    ⦃⇓ q c => ⌜Rat.divInt q.n q.d = Rat.divInt a 1 * Rat.divInt m e ∧
      c ≤ t0 + 13 * (bits + 1)⌝⦄ := by
  obtain ⟨r, c, hr, _, hp, hc⟩ := run_of_triple
    (ratio_euclid_multiply_bits a 1 m e bits ha (by have h := Nat.two_pow_pos bits; omega) hm he (by decide) heb (t0 + 2))
  refine triple_of_run r.1 c ?_ ⟨?_, by omega⟩
  · rw [ratio_euclid_mul_T_Ratio_run, hr]
    rfl
  · have hv := congrArg (fun p : Int × Int => Rat.divInt p.1 p.2) hp
    dsimp only at hv
    rw [hv]
    exact RatioMath.mul_value a 1 m e (by decide) he0

theorem ratio_euclid_div_Ratio_Ratio_input_value_bits (n d m e : Int) (bits : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits) (hm : m.natAbs ≤ 2 ^ bits) (he : e.natAbs ≤ 2 ^ bits) (hd0 : d ≠ 0) (hm0 : m ≠ 0) (heb : e.natAbs < fuel) (hmb : m.natAbs < fuel) (hwb : (d / (Int.gcd d e : Int) * (m / (Int.gcd n m : Int))).natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.op_div_Ratio_Ratio (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)
    ⦃⇓ q c => ⌜Rat.divInt q.n q.d = Rat.divInt n d / Rat.divInt m e ∧
      c ≤ t0 + 25 * (bits + 1)⌝⦄ := by
  obtain ⟨r, c, hr, _, hp, hc⟩ := run_of_triple
    (ratio_euclid_divide_input_bits n d m e bits hn hd hm he hm0 hmb heb hwb (t0 + 1))
  refine triple_of_run r.1 c ?_ ⟨?_, by omega⟩
  · rw [ratio_euclid_div_Ratio_Ratio_run, hr]
    rfl
  · have hv := congrArg (fun p : Int × Int => Rat.divInt p.1 p.2) hp
    dsimp only at hv
    rw [hv]
    exact RatioMath.div_value n d m e hd0 hm0

theorem ratio_euclid_div_Ratio_T_input_value_bits (n d b : Int) (bits : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits) (hb : b.natAbs ≤ 2 ^ bits) (hd0 : d ≠ 0) (hm0 : b ≠ 0) (hmb : b.natAbs < fuel) (hwb : (d / (Int.gcd d 1 : Int) * (b / (Int.gcd n b : Int))).natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.op_div_Ratio_T (⟨n, d⟩ : cp.Ratio Int) b
    ⦃⇓ q c => ⌜Rat.divInt q.n q.d = Rat.divInt n d / Rat.divInt b 1 ∧
      c ≤ t0 + 25 * (bits + 1)⌝⦄ := by
  obtain ⟨r, c, hr, _, hp, hc⟩ := run_of_triple
    (ratio_euclid_divide_input_bits n d b 1 bits hn hd hb (by have h := Nat.two_pow_pos bits; omega) hm0 hmb (by decide) hwb (t0 + 2))
  refine triple_of_run r.1 c ?_ ⟨?_, by omega⟩
  · rw [ratio_euclid_div_Ratio_T_run, hr]
    rfl
  · have hv := congrArg (fun p : Int × Int => Rat.divInt p.1 p.2) hp
    dsimp only at hv
    rw [hv]
    exact RatioMath.div_value n d b 1 hd0 hm0

theorem ratio_euclid_div_T_Ratio_input_value_bits (a m e : Int) (bits : Nat)
    (ha : a.natAbs ≤ 2 ^ bits) (hm : m.natAbs ≤ 2 ^ bits) (he : e.natAbs ≤ 2 ^ bits) (hm0 : m ≠ 0) (heb : e.natAbs < fuel) (hmb : m.natAbs < fuel) (hwb : (1 / (Int.gcd 1 e : Int) * (m / (Int.gcd a m : Int))).natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.op_div_T_Ratio a (⟨m, e⟩ : cp.Ratio Int)
    ⦃⇓ q c => ⌜Rat.divInt q.n q.d = Rat.divInt a 1 / Rat.divInt m e ∧
      c ≤ t0 + 25 * (bits + 1)⌝⦄ := by
  obtain ⟨r, c, hr, _, hp, hc⟩ := run_of_triple
    (ratio_euclid_divide_input_bits a 1 m e bits ha (by have h := Nat.two_pow_pos bits; omega) hm he hm0 hmb heb hwb (t0 + 2))
  refine triple_of_run r.1 c ?_ ⟨?_, by omega⟩
  · rw [ratio_euclid_div_T_Ratio_run, hr]
    rfl
  · have hv := congrArg (fun p : Int × Int => Rat.divInt p.1 p.2) hp
    dsimp only at hv
    rw [hv]
    exact RatioMath.div_value a 1 m e (by decide) hm0

/-- One loop transition, exposing only the algorithm's current pair. -/
def ratio_euclid_body (s : Int × Int) : M (ForInStep (Int × Int)) := do
  tick
  if !(decide (s.2 ≠ 0)) then return .done s
  return .yield (s.2, s.1 % s.2)

theorem ratio_euclid_source_loop (a b : Int) :
    cp.Ratio.numeric_gcd_nonnegative a b = (do
      tick
      let s ← forIn forever (a, b) (fun _ s => ratio_euclid_body s)
      return s.1) := by
  rfl

theorem ratio_euclid_body_payload (a b : Int) (bits t : Nat)
    (ha : 0 ≤ a) (hb : 0 < b)
    (hasize : a.toNat ≤ 2 ^ bits) (hbsize : b.toNat ≤ 2 ^ bits) :
    (ratio_euclid_body (a, b)).run t = some (.yield (b, a % b), t + 1) ∧
    (b.toNat, (a % b).toNat) = RatioSpace.step (a.toNat, b.toNat) ∧
    RatioSpace.payloadBits (RatioSpace.frame (a.toNat, b.toNat)) ≤ 3 * (bits + 1) := by
  refine ⟨?_, RatioSpace.integer_step a b ha hb, RatioSpace.frame_bits _ bits ⟨hasize, hbsize⟩⟩
  have hne : b ≠ 0 := by omega
  simp [ratio_euclid_body, hne, tick, StateT.run, modify]
  rfl

/-- Positive LCM retains `a,b` across the Euclidean call for the final scaling. -/
theorem ratio_euclid_lcm_positive_source (a b : Int) (ha : 0 < a) (hb : 0 < b) :
    cp.Ratio.numeric_lcm a b = (do
      tick
      let g ← cp.Ratio.numeric_gcd_nonnegative a b
      return a / g * b) := by
  have ha0 : a ≠ 0 := by omega
  have hb0 : b ≠ 0 := by omega
  have han : ¬a < 0 := by omega
  have hbn : ¬b < 0 := by omega
  simp [cp.Ratio.numeric_lcm, ha0, hb0, han, hbn]

theorem ratio_euclid_lcm_positive_payload (a b : Int) (bits k : Nat)
    (ha : 0 < a) (hb : 0 < b)
    (hasize : a.toNat ≤ 2 ^ bits) (hbsize : b.toNat ≤ 2 ^ bits) :
    cp.Ratio.numeric_lcm a b = (do
      tick
      let g ← cp.Ratio.numeric_gcd_nonnegative a b
      return a / g * b) ∧
    (RatioSpace.lcmContext a.toNat b.toNat ++
      RatioSpace.frame (RatioSpace.stateAt k (a.toNat, b.toNat))).length = 5 ∧
    RatioSpace.payloadBits (RatioSpace.lcmContext a.toNat b.toNat ++
      RatioSpace.frame (RatioSpace.stateAt k (a.toNat, b.toNat))) ≤ 5 * (bits + 1) := by
  exact ⟨ratio_euclid_lcm_positive_source a b ha hb,
    RatioSpace.lcm_frames a.toNat b.toNat bits k hasize hbsize⟩

/-- Nonzero normalization first changes signs, then retains the two fields
while the signed GCD helper runs and divides each by its result. -/
theorem ratio_euclid_normalize_source (n d : Int) (hn : n ≠ 0) :
    cp.Ratio.normalize (⟨n, d⟩ : cp.Ratio Int) = (do
      tick
      let n' := if d < 0 then -n else n
      let d' := if d < 0 then -d else d
      let g ← cp.Ratio.numeric_gcd n' d'
      return (⟨n' / g, d' / g⟩ : cp.Ratio Int)) := by
  by_cases hd : d < 0
  · simp [cp.Ratio.normalize, hn, hd]
  · simp [cp.Ratio.normalize, hn, hd]

theorem ratio_euclid_normalize_payload (n d : Int) (bits k : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits) :
    max (RatioSpace.signedPayloadBits (RatioSpace.normalizeContext n d) +
      RatioSpace.payloadBits (RatioSpace.frame (RatioSpace.stateAt k (n.natAbs, d.natAbs))))
      (RatioSpace.signedPayloadBits (RatioSpace.normalizeScale n d)) ≤ 11 * (bits + 1) := by
  exact RatioSpace.normalize_peak_bits n d bits k hn hd

theorem ratio_euclid_add_source (n d m e : Int) :
    cp.Ratio.op_add_assign (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int) = (do
      tick
      let l ← cp.Ratio.numeric_lcm d e
      let q ← cp.Ratio.normalize (⟨l / d * n + l / e * m, l⟩ : cp.Ratio Int)
      return (q, q)) := by
  rfl

theorem ratio_euclid_add_payload (n d m e : Int) (bits k₁ k₂ : Nat)
    (hd0 : d ≠ 0) (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits)
    (hm : m.natAbs ≤ 2 ^ bits) (he : e.natAbs ≤ 2 ^ bits) :
    RatioArithmeticSpace.additivePeak false n d m e k₁ k₂ ≤ 81 * (bits + 1) := by
  exact RatioArithmeticSpace.additive_peak_bits false n d m e bits k₁ k₂ hd0 hn hd hm he

theorem ratio_euclid_sub_source (n d m e : Int) :
    cp.Ratio.op_sub_assign (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int) = (do
      tick
      let l ← cp.Ratio.numeric_lcm d e
      let q ← cp.Ratio.normalize (⟨l / d * n - l / e * m, l⟩ : cp.Ratio Int)
      return (q, q)) := by
  rfl

theorem ratio_euclid_sub_payload (n d m e : Int) (bits k₁ k₂ : Nat)
    (hd0 : d ≠ 0) (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits)
    (hm : m.natAbs ≤ 2 ^ bits) (he : e.natAbs ≤ 2 ^ bits) :
    RatioArithmeticSpace.additivePeak true n d m e k₁ k₂ ≤ 81 * (bits + 1) := by
  exact RatioArithmeticSpace.additive_peak_bits true n d m e bits k₁ k₂ hd0 hn hd hm he

theorem ratio_euclid_mul_source (n d m e : Int) :
    cp.Ratio.op_mul_assign (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int) = (do
      tick
      let g ← cp.Ratio.numeric_gcd n e
      let h ← cp.Ratio.numeric_gcd m d
      let q : cp.Ratio Int := ⟨n / g * (m / h), d / h * (e / g)⟩
      return (q, q)) := by
  rfl

theorem ratio_euclid_div_source (n d m e : Int) :
    cp.Ratio.op_div_assign (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int) = (do
      tick
      check (decide (m ≠ 0))
      let g ← cp.Ratio.numeric_gcd n m
      let h ← cp.Ratio.numeric_gcd d e
      let q ← cp.Ratio.normalize (⟨n / g * (e / h), d / h * (m / g)⟩ : cp.Ratio Int)
      return (q, q)) := by
  rfl

theorem ratio_euclid_mul_payload (n d m e : Int) (bits k₁ k₂ k₃ : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits)
    (hm : m.natAbs ≤ 2 ^ bits) (he : e.natAbs ≤ 2 ^ bits) :
    RatioArithmeticSpace.productPeak false n d m e k₁ k₂ k₃ ≤ 81 * (bits + 1) := by
  exact RatioArithmeticSpace.product_peak_bits false n d m e bits k₁ k₂ k₃ hn hd hm he

theorem ratio_euclid_div_payload (n d m e : Int) (bits k₁ k₂ k₃ : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits)
    (hm : m.natAbs ≤ 2 ^ bits) (he : e.natAbs ≤ 2 ^ bits) :
    RatioArithmeticSpace.productPeak true n d m e k₁ k₂ k₃ ≤ 81 * (bits + 1) := by
  exact RatioArithmeticSpace.product_peak_bits true n d m e bits k₁ k₂ k₃ hn hd hm he

theorem ratio_euclid_prefix_increment_value (n d : Int) (hd : d ≠ 0) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_inc_0 (⟨n, d⟩ : cp.Ratio Int)
    ⦃⇓ q c => ⌜Rat.divInt q.1.n q.1.d = Rat.divInt n d + 1 ∧
      Rat.divInt q.2.n q.2.d = Rat.divInt n d + 1 ∧ c = t0 + 1⌝⦄ := by
  have hv := RatioMath.increment_value n d hd
  refine triple_of_run ((⟨n + d, d⟩ : cp.Ratio Int), (⟨n + d, d⟩ : cp.Ratio Int)) (t0 + 1) ?_ ⟨hv, hv, rfl⟩
  exact ratio_euclid_prefix_increment_run n d t0

theorem ratio_euclid_postfix_increment_value (n d : Int) (hd : d ≠ 0) (tag : Int) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_inc_int (⟨n, d⟩ : cp.Ratio Int) tag
    ⦃⇓ q c => ⌜Rat.divInt q.1.n q.1.d = Rat.divInt n d ∧
      Rat.divInt q.2.n q.2.d = Rat.divInt n d + 1 ∧ c = t0 + 2⌝⦄ := by
  have hv := RatioMath.increment_value n d hd
  refine triple_of_run ((⟨n, d⟩ : cp.Ratio Int), (⟨n + d, d⟩ : cp.Ratio Int)) (t0 + 2) ?_ ⟨rfl, hv, rfl⟩
  exact ratio_euclid_postfix_increment_run n d tag t0

theorem ratio_euclid_prefix_decrement_value (n d : Int) (hd : d ≠ 0) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_dec_0 (⟨n, d⟩ : cp.Ratio Int)
    ⦃⇓ q c => ⌜Rat.divInt q.1.n q.1.d = Rat.divInt n d - 1 ∧
      Rat.divInt q.2.n q.2.d = Rat.divInt n d - 1 ∧ c = t0 + 1⌝⦄ := by
  have hv := RatioMath.decrement_value n d hd
  refine triple_of_run ((⟨n - d, d⟩ : cp.Ratio Int), (⟨n - d, d⟩ : cp.Ratio Int)) (t0 + 1) ?_ ⟨hv, hv, rfl⟩
  exact ratio_euclid_prefix_decrement_run n d t0

theorem ratio_euclid_postfix_decrement_value (n d : Int) (hd : d ≠ 0) (tag : Int) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_dec_int (⟨n, d⟩ : cp.Ratio Int) tag
    ⦃⇓ q c => ⌜Rat.divInt q.1.n q.1.d = Rat.divInt n d ∧
      Rat.divInt q.2.n q.2.d = Rat.divInt n d - 1 ∧ c = t0 + 2⌝⦄ := by
  have hv := RatioMath.decrement_value n d hd
  refine triple_of_run ((⟨n, d⟩ : cp.Ratio Int), (⟨n - d, d⟩ : cp.Ratio Int)) (t0 + 2) ?_ ⟨rfl, hv, rfl⟩
  exact ratio_euclid_postfix_decrement_run n d tag t0

theorem ratio_euclid_unary_plus_value (n d : Int) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_add (⟨n, d⟩ : cp.Ratio Int)
    ⦃⇓ q c => ⌜Rat.divInt q.n q.d = Rat.divInt n d ∧ c = t0 + 1⌝⦄ := by
  exact triple_of_run _ _ (ratio_euclid_unary_plus_run n d t0) ⟨rfl, rfl⟩

theorem ratio_euclid_negate_input_value_bits (n d : Int) (bits : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits)
    (hd0 : d ≠ 0) (hbound : d.natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_sub (⟨n, d⟩ : cp.Ratio Int)
    ⦃⇓ q c => ⌜Rat.divInt q.n q.d = -Rat.divInt n d ∧ c ≤ t0 + 8 * (bits + 1)⌝⦄ := by
  obtain ⟨q, c, hr, hp, hc⟩ := run_of_triple
    (ratio_euclid_negate_input_bits n d bits hn hd hbound t0)
  refine triple_of_run q c hr ⟨?_, hc⟩
  have hv := congrArg (fun p : Int × Int => Rat.divInt p.1 p.2) hp
  exact hv.trans (RatioMath.negate_value n d hd0)

theorem ratio_euclid_compare_source (n d m e : Int) :
    cp.Ratio.op_cmp (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int) = (do
      tick
      let g ← cp.Ratio.numeric_gcd d e
      return (if e / g * n < d / g * m then Ordering.lt
        else if d / g * m < e / g * n then Ordering.gt else Ordering.eq)) := by
  rfl

theorem ratio_euclid_negate_source (n d : Int) :
    cp.Ratio.op_sub (⟨n, d⟩ : cp.Ratio Int) = (do
      tick
      let q ← cp.Ratio.init_T_T (-n) d
      return q) := by
  rfl

theorem ratio_euclid_copy_payload (n d : Int) (bits : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits) :
    RatioSpace.signedPayloadBits (RatioArithmeticSpace.copyContext n d) ≤ 8 * (bits + 1) := by
  exact RatioArithmeticSpace.copy_context_bits n d bits hn hd

/-- The scalar constructor needs no Euclidean call or fuel premise. Its
copied-field envelope includes the input and the returned numerator/denominator. -/
theorem ratio_euclid_init_scalar_value_payload (n : Int) (bits t : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) :
    (cp.Ratio.init_T n).run t = some ((⟨n, 1⟩ : cp.Ratio Int), t + 1) ∧
    Rat.divInt n 1 = (n : Rat) ∧
    RatioSpace.signedPayloadBits (RatioArithmeticSpace.copyContext n 1) ≤
      8 * (bits + 1) := by
  refine ⟨ratio_euclid_init_scalar_run n t, ?_, ?_⟩
  · simp
  · exact RatioArithmeticSpace.copy_context_bits n 1 bits hn
      (by simpa using Nat.succ_le_of_lt (Nat.two_pow_pos bits))

theorem ratio_euclid_shift_payload (subtract : Bool) (n d : Int) (bits : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits) :
    RatioSpace.signedPayloadBits (RatioArithmeticSpace.shiftContext subtract n d) ≤ 24 * (bits + 1) := by
  exact RatioArithmeticSpace.shift_context_bits subtract n d bits hn hd

theorem ratio_euclid_compare_payload (n d m e : Int) (bits k : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits)
    (hm : m.natAbs ≤ 2 ^ bits) (he : e.natAbs ≤ 2 ^ bits) :
    RatioArithmeticSpace.comparePeak n d m e k ≤ 39 * (bits + 1) := by
  exact RatioArithmeticSpace.compare_peak_bits n d m e bits k hn hd hm he

theorem ratio_euclid_negate_payload (n d : Int) (bits k : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits) :
    RatioArithmeticSpace.negatePeak n d k ≤ 19 * (bits + 1) := by
  exact RatioArithmeticSpace.negate_peak_bits n d bits k hn hd

theorem ratio_euclid_init_payload (n d : Int) (bits k : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits) :
    RatioArithmeticSpace.constructPeak n d k ≤ 19 * (bits + 1) := by
  exact RatioArithmeticSpace.construct_peak_bits n d bits k hn hd

theorem ratio_euclid_equal_payload (n d m e : Int) (bits : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits)
    (hm : m.natAbs ≤ 2 ^ bits) (he : e.natAbs ≤ 2 ^ bits) :
    RatioSpace.signedPayloadBits [n, d, m, e] ≤ 8 * (bits + 1) := by
  exact RatioArithmeticSpace.equality_context_bits n d m e bits hn hd hm he

-- Appended to the full Euclid candidate after importing UnsignedMagnitude.
open Std.Do Proofs.Cpp Proofs.Cpp.Gen
open Proofs.Cpp.UnsignedMagnitude

@[spec] theorem ratio_unsigned_core {T : Type} [Zero T] [Mod T] [LT T]
    [DecidableEq T] [UnsignedMagnitude T] (a b : T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.numeric_gcd_nonnegative a b
    ⦃⇓ r c => ⌜magnitude r = Nat.gcd (magnitude a) (magnitude b) ∧
      c ≤ t0 + 2 + gcdCost (magnitude a) (magnitude b)⌝⦄ := by
  mvcgen [cp.Ratio.numeric_gcd_nonnegative]
  case inv =>
    exact ⟨fun ⟨x, y⟩ c => ⌜Nat.gcd (magnitude x) (magnitude y) = Nat.gcd (magnitude a) (magnitude b) ∧
      c + gcdCost (magnitude x) (magnitude y) ≤ t0 + 1 + gcdCost (magnitude a) (magnitude b)⌝,
      fun ⟨x, _⟩ c => ⌜magnitude x = Nat.gcd (magnitude a) (magnitude b) ∧
        c ≤ t0 + 2 + gcdCost (magnitude a) (magnitude b)⌝,
      fun ⟨_, y⟩ => magnitude y⟩
  all_goals simp +zetaDelta at *
  · obtain ⟨hg, hc⟩ := ‹_ ∧ _›
    have hy : (‹T × T›).2 = 0 := ‹_›
    simp only [hy, magnitude_zero, Nat.gcd_zero_right] at hg
    simp only [hy, magnitude_zero, gcdCost_zero] at hc
    exact ⟨hg, by omega⟩
  · obtain ⟨hg, hc⟩ := ‹_ ∧ _›
    have hy : (‹T × T›).2 ≠ 0 := ‹_›
    have hp : 0 < magnitude (‹T × T›).2 := by
      have hn : magnitude (‹T × T›).2 ≠ 0 := fun h => hy ((zero_iff _).mp h)
      omega
    have hcost := gcdCost_step (magnitude (‹T × T›).1) (magnitude (‹T × T›).2) hp
    refine ⟨⟨?_, by omega⟩, Nat.mod_lt _ hp⟩
    rw [← hg]
    conv_lhs => rw [Nat.gcd_comm]
    rw [← Nat.gcd_rec]
    exact Nat.gcd_comm _ _
  · exact ⟨by omega, bound b⟩
  · exact ‹_ ∧ _›

@[spec] theorem ratio_unsigned_gcd {T : Type} [Zero T] [Neg T] [Mod T] [LT T]
    [DecidableLT T] [DecidableEq T] [UnsignedMagnitude T] (a b : T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.numeric_gcd a b
    ⦃⇓ r c => ⌜magnitude r = Nat.gcd (magnitude a) (magnitude b) ∧
      c ≤ t0 + 3 + gcdCost (magnitude a) (magnitude b)⌝⦄ := by
  mvcgen [cp.Ratio.numeric_gcd]
  all_goals simp_all +zetaDelta [UnsignedMagnitude.not_lt_zero]

theorem ratio_gcd_uint32 (a b : UInt32) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.numeric_gcd a b
    ⦃⇓ r c => ⌜r.toNat = Nat.gcd a.toNat b.toNat ∧
      c ≤ t0 + 3 + gcdCost a.toNat b.toNat⌝⦄ := by
  exact ratio_unsigned_gcd a b t0

theorem ratio_gcd_uint64 (a b : UInt64) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.numeric_gcd a b
    ⦃⇓ r c => ⌜r.toNat = Nat.gcd a.toNat b.toNat ∧
      c ≤ t0 + 3 + gcdCost a.toNat b.toNat⌝⦄ := by
  exact ratio_unsigned_gcd a b t0

theorem ratio_gcd_uint8 (a b : UInt8) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.numeric_gcd a b
    ⦃⇓ r c => ⌜r.toNat = Nat.gcd a.toNat b.toNat ∧
      c ≤ t0 + 3 + gcdCost a.toNat b.toNat⌝⦄ := by
  exact ratio_unsigned_gcd a b t0

theorem ratio_gcd_uint16 (a b : UInt16) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.numeric_gcd a b
    ⦃⇓ r c => ⌜r.toNat = Nat.gcd a.toNat b.toNat ∧
      c ≤ t0 + 3 + gcdCost a.toNat b.toNat⌝⦄ := by
  exact ratio_unsigned_gcd a b t0

@[spec] theorem ratio_unsigned_normalize {T : Type}
    [Zero T] [One T] [Neg T] [Div T] [Mod T] [LT T] [DecidableLT T] [DecidableEq T]
    [UnsignedMagnitude T] [UnsignedDivision T] (n d : T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.normalize (⟨n, d⟩ : cp.Ratio T)
    ⦃⇓ q c => ⌜(magnitude q.n, magnitude q.d) =
      (if magnitude n = 0 then (0, 1) else
        (magnitude n / Nat.gcd (magnitude n) (magnitude d),
         magnitude d / Nat.gcd (magnitude n) (magnitude d))) ∧
      c ≤ t0 + 4 + gcdCost (magnitude n) (magnitude d)⌝⦄ := by
  mvcgen [cp.Ratio.normalize]
  all_goals simp_all +zetaDelta [UnsignedMagnitude.not_lt_zero, UnsignedMagnitude.zero_iff,
    UnsignedDivision.one_eq, UnsignedDivision.div_eq]
  all_goals omega

theorem ratio_unsigned_normalize_int {T : Type}
    [Zero T] [One T] [Neg T] [Div T] [Mod T] [LT T] [DecidableLT T] [DecidableEq T]
    [UnsignedMagnitude T] [UnsignedDivision T] (n d : T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.normalize (⟨n, d⟩ : cp.Ratio T)
    ⦃⇓ q c => ⌜((magnitude q.n : Int), (magnitude q.d : Int)) =
      RatioMath.normalize (magnitude n : Int) (magnitude d : Int) ∧
      c ≤ t0 + 4 + gcdCost (magnitude n) (magnitude d)⌝⦄ := by
  obtain ⟨q, c, hr, hp, hc⟩ := run_of_triple (ratio_unsigned_normalize n d t0)
  refine triple_of_run q c hr ⟨?_, hc⟩
  rw [RatioMath.normalize_nat_pair]
  exact congrArg (fun p : Nat × Nat => ((p.1 : Int), (p.2 : Int))) hp

theorem ratio_unsigned_normalize_canonical {T : Type}
    [Zero T] [One T] [Neg T] [Div T] [Mod T] [LT T] [DecidableLT T] [DecidableEq T]
    [UnsignedMagnitude T] [UnsignedDivision T] (n d : T) (hd : d ≠ 0) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.normalize (⟨n, d⟩ : cp.Ratio T)
    ⦃⇓ q c => ⌜((magnitude q.n : Int), (magnitude q.d : Int)) =
      ((Rat.divInt (magnitude n : Int) (magnitude d : Int)).num,
        ((Rat.divInt (magnitude n : Int) (magnitude d : Int)).den : Int)) ∧
      c ≤ t0 + 4 + gcdCost (magnitude n) (magnitude d)⌝⦄ := by
  obtain ⟨q, c, hr, hp, hc⟩ := run_of_triple (ratio_unsigned_normalize_int n d t0)
  refine triple_of_run q c hr ⟨?_, hc⟩
  have hdmag : magnitude d ≠ 0 := fun h => hd ((zero_iff _).mp h)
  rw [RatioMath.normalize_eq_canonical _ _ (by omega)] at hp
  exact hp

theorem ratio_unsigned_init {T : Type}
    [Zero T] [One T] [Neg T] [Div T] [Mod T] [LT T] [DecidableLT T] [DecidableEq T]
    [UnsignedMagnitude T] [UnsignedDivision T] (n d : T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.init_T_T n d
    ⦃⇓ q c => ⌜((magnitude q.n : Int), (magnitude q.d : Int)) =
      RatioMath.normalize (magnitude n : Int) (magnitude d : Int) ∧
      c ≤ t0 + 5 + gcdCost (magnitude n) (magnitude d)⌝⦄ := by
  obtain ⟨q, c, hr, hp, hc⟩ := run_of_triple (ratio_unsigned_normalize_int n d (t0 + 1))
  refine triple_of_run q c ?_ ⟨hp, by omega⟩
  change Option.bind ((cp.Ratio.normalize (⟨n, d⟩ : cp.Ratio T)).run (t0 + 1))
    (fun result => some ((⟨result.1.n, result.1.d⟩ : cp.Ratio T), result.2)) = some (q, c)
  rw [hr]
  rfl

theorem ratio_unsigned_normalize_bits {T : Type}
    [Zero T] [One T] [Neg T] [Div T] [Mod T] [LT T] [DecidableLT T] [DecidableEq T]
    [UnsignedMagnitude T] [UnsignedDivision T] (n d : T) (bits t0 : Nat)
    (hn : magnitude n ≤ 2 ^ bits) (hd : magnitude d ≤ 2 ^ bits) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.normalize (⟨n, d⟩ : cp.Ratio T)
    ⦃⇓ q c => ⌜((magnitude q.n : Int), (magnitude q.d : Int)) =
      RatioMath.normalize (magnitude n : Int) (magnitude d : Int) ∧
      c ≤ t0 + 6 * (bits + 1)⌝⦄ := by
  obtain ⟨q, c, hr, hp, hc⟩ := run_of_triple (ratio_unsigned_normalize_int n d t0)
  have hg := RatioCost.gcd_bits (magnitude n) (magnitude d) bits hn hd
  exact triple_of_run q c hr ⟨hp, by omega⟩

@[spec] theorem ratio_unsigned_lcm {T : Type}
    [Zero T] [One T] [Neg T] [Mul T] [Div T] [Mod T] [LT T] [DecidableLT T] [DecidableEq T]
    [UnsignedMagnitude T] [UnsignedDivision T] [UnsignedProduct T] (a b : T)
    (hfit : Nat.lcm (magnitude a) (magnitude b) < UnsignedProduct.capacity (T := T)) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.numeric_lcm a b
    ⦃⇓ r c => ⌜magnitude r = Nat.lcm (magnitude a) (magnitude b) ∧
      c ≤ t0 + 3 + gcdCost (magnitude a) (magnitude b)⌝⦄ := by
  by_cases ha : a = 0
  · refine triple_of_run (0 : T) (t0 + 1) ?_ ⟨?_, by omega⟩
    · simp [cp.Ratio.numeric_lcm, ha, tick, StateT.run, modify]
      rfl
    · simp [ha]
  by_cases hb : b = 0
  · refine triple_of_run (0 : T) (t0 + 1) ?_ ⟨?_, by omega⟩
    · simp [cp.Ratio.numeric_lcm, hb, tick, StateT.run, modify]
      rfl
    · simp [hb]
  obtain ⟨g, c, hr, hg, hc⟩ := run_of_triple (ratio_unsigned_core a b (t0 + 1))
  have hmfit : magnitude (a / g) * magnitude b < UnsignedProduct.capacity (T := T) := by
    rw [UnsignedDivision.div_eq, hg, RatioMath.lcm_nat_formula]
    exact hfit
  have hm : magnitude (a / g * b) = Nat.lcm (magnitude a) (magnitude b) := by
    rw [UnsignedProduct.mul_exact _ _ hmfit, UnsignedDivision.div_eq, hg]
    exact RatioMath.lcm_nat_formula _ _
  refine triple_of_run (a / g * b) c ?_ ⟨hm, by omega⟩
  have hs : cp.Ratio.numeric_lcm a b = (do
      tick
      let g ← cp.Ratio.numeric_gcd_nonnegative a b
      return a / g * b) := by
    simp [cp.Ratio.numeric_lcm, ha, hb, UnsignedMagnitude.not_lt_zero]
  rw [hs]
  change Option.bind ((cp.Ratio.numeric_gcd_nonnegative a b).run (t0 + 1))
    (fun result => some (a / result.1 * b, result.2)) = some (a / g * b, c)
  rw [hr]
  rfl

theorem ratio_unsigned_lcm_bits {T : Type}
    [Zero T] [One T] [Neg T] [Mul T] [Div T] [Mod T] [LT T] [DecidableLT T] [DecidableEq T]
    [UnsignedMagnitude T] [UnsignedDivision T] [UnsignedProduct T] (a b : T) (bits t0 : Nat)
    (hfit : Nat.lcm (magnitude a) (magnitude b) < UnsignedProduct.capacity (T := T))
    (ha : magnitude a ≤ 2 ^ bits) (hb : magnitude b ≤ 2 ^ bits) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.numeric_lcm a b
    ⦃⇓ r c => ⌜magnitude r = Nat.lcm (magnitude a) (magnitude b) ∧
      c ≤ t0 + 5 * (bits + 1)⌝⦄ := by
  obtain ⟨r, c, hr, hp, hc⟩ := run_of_triple (ratio_unsigned_lcm a b hfit t0)
  have hg := RatioCost.gcd_bits (magnitude a) (magnitude b) bits ha hb
  exact triple_of_run r c hr ⟨hp, by omega⟩

theorem ratio_unsigned_lcm_int {T : Type}
    [Zero T] [One T] [Neg T] [Mul T] [Div T] [Mod T] [LT T] [DecidableLT T] [DecidableEq T]
    [UnsignedMagnitude T] [UnsignedDivision T] [UnsignedProduct T] (a b : T)
    (hfit : Nat.lcm (magnitude a) (magnitude b) < UnsignedProduct.capacity (T := T)) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.numeric_lcm a b
    ⦃⇓ r c => ⌜(magnitude r : Int) =
      (Int.lcm (magnitude a : Int) (magnitude b : Int) : Int) ∧
      c ≤ t0 + 3 + gcdCost (magnitude a) (magnitude b)⌝⦄ := by
  obtain ⟨r, c, hr, hp, hc⟩ := run_of_triple (ratio_unsigned_lcm a b hfit t0)
  refine triple_of_run r c hr ⟨?_, hc⟩
  simp only [Int.lcm_def, Int.natAbs_natCast, hp]

theorem ratio_lcm_uint8 (a b : UInt8)
    (hfit : Nat.lcm a.toNat b.toNat < 2 ^ 8) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.numeric_lcm a b
    ⦃⇓ r c => ⌜r.toNat = Nat.lcm a.toNat b.toNat ∧
      c ≤ t0 + 3 + gcdCost a.toNat b.toNat⌝⦄ := by
  exact ratio_unsigned_lcm a b hfit t0

theorem ratio_lcm_uint16 (a b : UInt16)
    (hfit : Nat.lcm a.toNat b.toNat < 2 ^ 16) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.numeric_lcm a b
    ⦃⇓ r c => ⌜r.toNat = Nat.lcm a.toNat b.toNat ∧
      c ≤ t0 + 3 + gcdCost a.toNat b.toNat⌝⦄ := by
  exact ratio_unsigned_lcm a b hfit t0

theorem ratio_lcm_uint32 (a b : UInt32)
    (hfit : Nat.lcm a.toNat b.toNat < 2 ^ 32) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.numeric_lcm a b
    ⦃⇓ r c => ⌜r.toNat = Nat.lcm a.toNat b.toNat ∧
      c ≤ t0 + 3 + gcdCost a.toNat b.toNat⌝⦄ := by
  exact ratio_unsigned_lcm a b hfit t0

theorem ratio_lcm_uint64 (a b : UInt64)
    (hfit : Nat.lcm a.toNat b.toNat < 2 ^ 64) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.numeric_lcm a b
    ⦃⇓ r c => ⌜r.toNat = Nat.lcm a.toNat b.toNat ∧
      c ≤ t0 + 3 + gcdCost a.toNat b.toNat⌝⦄ := by
  exact ratio_unsigned_lcm a b hfit t0

theorem ratio_unsigned_multiply {T : Type}
    [Zero T] [One T] [Neg T] [Mul T] [Div T] [Mod T] [LT T] [DecidableLT T] [DecidableEq T]
    [UnsignedMagnitude T] [UnsignedDivision T] [UnsignedProduct T] (n d m e : T)
    (hnum : magnitude n / Nat.gcd (magnitude n) (magnitude e) *
      (magnitude m / Nat.gcd (magnitude m) (magnitude d)) < UnsignedProduct.capacity (T := T))
    (hden : magnitude d / Nat.gcd (magnitude m) (magnitude d) *
      (magnitude e / Nat.gcd (magnitude n) (magnitude e)) < UnsignedProduct.capacity (T := T))
    (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_mul_assign (⟨n, d⟩ : cp.Ratio T) (⟨m, e⟩ : cp.Ratio T)
    ⦃⇓ q c => ⌜q.1 = q.2 ∧ (magnitude q.1.n, magnitude q.1.d) =
      (magnitude n / Nat.gcd (magnitude n) (magnitude e) *
        (magnitude m / Nat.gcd (magnitude m) (magnitude d)),
       magnitude d / Nat.gcd (magnitude m) (magnitude d) *
        (magnitude e / Nat.gcd (magnitude n) (magnitude e))) ∧
      c ≤ t0 + 7 + gcdCost (magnitude n) (magnitude e) + gcdCost (magnitude m) (magnitude d)⌝⦄ := by
  obtain ⟨g, c₁, hr₁, hg, hc₁⟩ := run_of_triple (ratio_unsigned_gcd n e (t0 + 1))
  obtain ⟨h, c₂, hr₂, hh, hc₂⟩ := run_of_triple (ratio_unsigned_gcd m d c₁)
  have hnfit : magnitude (n / g) * magnitude (m / h) < UnsignedProduct.capacity (T := T) := by
    simpa only [UnsignedDivision.div_eq, hg, hh] using hnum
  have hdfit : magnitude (d / h) * magnitude (e / g) < UnsignedProduct.capacity (T := T) := by
    simpa only [UnsignedDivision.div_eq, hg, hh] using hden
  let q : cp.Ratio T := ⟨n / g * (m / h), d / h * (e / g)⟩
  refine triple_of_run (q, q) c₂ ?_ ⟨rfl, ?_, by omega⟩
  · change Option.bind ((cp.Ratio.numeric_gcd n e).run (t0 + 1)) (fun r₁ =>
      Option.bind ((cp.Ratio.numeric_gcd m d).run r₁.2) (fun r₂ =>
        some (((⟨n / r₁.1 * (m / r₂.1), d / r₂.1 * (e / r₁.1)⟩ : cp.Ratio T),
          (⟨n / r₁.1 * (m / r₂.1), d / r₂.1 * (e / r₁.1)⟩ : cp.Ratio T)), r₂.2))) = _
    rw [hr₁]
    simp only [Option.bind_some]
    rw [hr₂]
    rfl
  · change (magnitude (n / g * (m / h)), magnitude (d / h * (e / g))) = _
    rw [UnsignedProduct.mul_exact _ _ hnfit, UnsignedProduct.mul_exact _ _ hdfit]
    simp only [UnsignedDivision.div_eq, hg, hh]

theorem ratio_unsigned_multiply_value {T : Type}
    [Zero T] [One T] [Neg T] [Mul T] [Div T] [Mod T] [LT T] [DecidableLT T] [DecidableEq T]
    [UnsignedMagnitude T] [UnsignedDivision T] [UnsignedProduct T] (n d m e : T)
    (hnum : magnitude n / Nat.gcd (magnitude n) (magnitude e) *
      (magnitude m / Nat.gcd (magnitude m) (magnitude d)) < UnsignedProduct.capacity (T := T))
    (hden : magnitude d / Nat.gcd (magnitude m) (magnitude d) *
      (magnitude e / Nat.gcd (magnitude n) (magnitude e)) < UnsignedProduct.capacity (T := T))
    (hd : d ≠ 0) (he : e ≠ 0) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_mul_assign (⟨n, d⟩ : cp.Ratio T) (⟨m, e⟩ : cp.Ratio T)
    ⦃⇓ q c => ⌜q.1 = q.2 ∧
      Rat.divInt (magnitude q.1.n : Int) (magnitude q.1.d : Int) =
        Rat.divInt (magnitude n : Int) (magnitude d : Int) *
        Rat.divInt (magnitude m : Int) (magnitude e : Int) ∧
      c ≤ t0 + 7 + gcdCost (magnitude n) (magnitude e) + gcdCost (magnitude m) (magnitude d)⌝⦄ := by
  obtain ⟨r, c, hr, heq, hp, hc⟩ := run_of_triple (ratio_unsigned_multiply n d m e hnum hden t0)
  refine triple_of_run r c hr ⟨heq, ?_, hc⟩
  have hcast := congrArg (fun p : Nat × Nat => ((p.1 : Int), (p.2 : Int))) hp
  rw [← RatioMath.mul_nat_pair] at hcast
  have hv := congrArg (fun p : Int × Int => Rat.divInt p.1 p.2) hcast
  dsimp only at hv
  rw [hv]
  have hdmag : magnitude d ≠ 0 := fun h => hd ((zero_iff _).mp h)
  have hemag : magnitude e ≠ 0 := fun h => he ((zero_iff _).mp h)
  exact RatioMath.mul_value _ _ _ _ (by omega) (by omega)

theorem ratio_unsigned_divide {T : Type}
    [Zero T] [One T] [Neg T] [Mul T] [Div T] [Mod T] [LT T] [DecidableLT T] [DecidableEq T]
    [UnsignedMagnitude T] [UnsignedDivision T] [UnsignedProduct T] (n d m e : T)
    (hm : m ≠ 0)
    (hnum : magnitude n / Nat.gcd (magnitude n) (magnitude m) *
      (magnitude e / Nat.gcd (magnitude d) (magnitude e)) < UnsignedProduct.capacity (T := T))
    (hden : magnitude d / Nat.gcd (magnitude d) (magnitude e) *
      (magnitude m / Nat.gcd (magnitude n) (magnitude m)) < UnsignedProduct.capacity (T := T))
    (t0 : Nat) :
    let z := magnitude n / Nat.gcd (magnitude n) (magnitude m) *
      (magnitude e / Nat.gcd (magnitude d) (magnitude e))
    let w := magnitude d / Nat.gcd (magnitude d) (magnitude e) *
      (magnitude m / Nat.gcd (magnitude n) (magnitude m))
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_div_assign (⟨n, d⟩ : cp.Ratio T) (⟨m, e⟩ : cp.Ratio T)
    ⦃⇓ q c => ⌜q.1 = q.2 ∧ ((magnitude q.1.n : Int), (magnitude q.1.d : Int)) =
      RatioMath.div (magnitude n : Int) (magnitude d : Int) (magnitude m : Int) (magnitude e : Int) ∧
      c ≤ t0 + 11 + gcdCost (magnitude n) (magnitude m) +
        gcdCost (magnitude d) (magnitude e) + gcdCost z w⌝⦄ := by
  dsimp only
  obtain ⟨g, c₁, hr₁, hg, hc₁⟩ := run_of_triple (ratio_unsigned_gcd n m (t0 + 1))
  obtain ⟨h, c₂, hr₂, hh, hc₂⟩ := run_of_triple (ratio_unsigned_gcd d e c₁)
  have hnfit : magnitude (n / g) * magnitude (e / h) < UnsignedProduct.capacity (T := T) := by
    simpa only [UnsignedDivision.div_eq, hg, hh] using hnum
  have hdfit : magnitude (d / h) * magnitude (m / g) < UnsignedProduct.capacity (T := T) := by
    simpa only [UnsignedDivision.div_eq, hg, hh] using hden
  let zn := n / g * (e / h)
  let wd := d / h * (m / g)
  have hz : magnitude zn = magnitude n / Nat.gcd (magnitude n) (magnitude m) *
      (magnitude e / Nat.gcd (magnitude d) (magnitude e)) := by
    rw [UnsignedProduct.mul_exact _ _ hnfit, UnsignedDivision.div_eq,
      UnsignedDivision.div_eq, hg, hh]
  have hw : magnitude wd = magnitude d / Nat.gcd (magnitude d) (magnitude e) *
      (magnitude m / Nat.gcd (magnitude n) (magnitude m)) := by
    rw [UnsignedProduct.mul_exact _ _ hdfit, UnsignedDivision.div_eq,
      UnsignedDivision.div_eq, hg, hh]
  obtain ⟨q, c₃, hr₃, hp, hc₃⟩ := run_of_triple (ratio_unsigned_normalize_int zn wd c₂)
  refine triple_of_run (q, q) c₃ ?_ ⟨rfl, ?_, ?_⟩
  · simp only [cp.Ratio.op_div_assign, check, decide_eq_true hm, ite_true]
    change Option.bind ((cp.Ratio.numeric_gcd n m).run (t0 + 1)) (fun r₁ =>
      Option.bind ((cp.Ratio.numeric_gcd d e).run r₁.2) (fun r₂ =>
        Option.bind ((cp.Ratio.normalize
          (⟨n / r₁.1 * (e / r₂.1), d / r₂.1 * (m / r₁.1)⟩ : cp.Ratio T)).run r₂.2)
          (fun r₃ => some ((r₃.1, r₃.1), r₃.2)))) = _
    rw [hr₁]
    simp only [Option.bind_some]
    rw [hr₂]
    simp only [Option.bind_some]
    rw [hr₃]
    rfl
  · rw [RatioMath.div_nat_pair, ← hz, ← hw]
    exact hp
  · rw [hz, hw] at hc₃
    omega

theorem ratio_unsigned_divide_value {T : Type}
    [Zero T] [One T] [Neg T] [Mul T] [Div T] [Mod T] [LT T] [DecidableLT T] [DecidableEq T]
    [UnsignedMagnitude T] [UnsignedDivision T] [UnsignedProduct T] (n d m e : T)
    (hm : m ≠ 0)
    (hnum : magnitude n / Nat.gcd (magnitude n) (magnitude m) *
      (magnitude e / Nat.gcd (magnitude d) (magnitude e)) < UnsignedProduct.capacity (T := T))
    (hden : magnitude d / Nat.gcd (magnitude d) (magnitude e) *
      (magnitude m / Nat.gcd (magnitude n) (magnitude m)) < UnsignedProduct.capacity (T := T))
    (hd : d ≠ 0) (he : e ≠ 0) (t0 : Nat) :
    let z := magnitude n / Nat.gcd (magnitude n) (magnitude m) *
      (magnitude e / Nat.gcd (magnitude d) (magnitude e))
    let w := magnitude d / Nat.gcd (magnitude d) (magnitude e) *
      (magnitude m / Nat.gcd (magnitude n) (magnitude m))
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_div_assign (⟨n, d⟩ : cp.Ratio T) (⟨m, e⟩ : cp.Ratio T)
    ⦃⇓ q c => ⌜q.1 = q.2 ∧
      Rat.divInt (magnitude q.1.n : Int) (magnitude q.1.d : Int) =
        Rat.divInt (magnitude n : Int) (magnitude d : Int) /
        Rat.divInt (magnitude m : Int) (magnitude e : Int) ∧
      c ≤ t0 + 11 + gcdCost (magnitude n) (magnitude m) +
        gcdCost (magnitude d) (magnitude e) + gcdCost z w⌝⦄ := by
  dsimp only
  obtain ⟨r, c, hr, heq, hp, hc⟩ := run_of_triple (ratio_unsigned_divide n d m e hm hnum hden t0)
  refine triple_of_run r c hr ⟨heq, ?_, hc⟩
  have hv := congrArg (fun p : Int × Int => Rat.divInt p.1 p.2) hp
  dsimp only at hv
  rw [hv]
  have hdmag : magnitude d ≠ 0 := fun h => hd ((zero_iff _).mp h)
  have hmmag : magnitude m ≠ 0 := fun h => hm ((zero_iff _).mp h)
  exact RatioMath.div_value _ _ _ _ (by omega) (by omega)

theorem ratio_unsigned_add {T : Type}
    [Zero T] [One T] [Neg T] [Add T] [Sub T] [Mul T] [Div T] [Mod T] [LT T]
    [DecidableLT T] [DecidableEq T]
    [UnsignedMagnitude T] [UnsignedDivision T] [UnsignedProduct T] [UnsignedAddSub T]
    (n d m e : T)
    (hlfit : Nat.lcm (magnitude d) (magnitude e) < UnsignedProduct.capacity (T := T))
    (hsum : Nat.lcm (magnitude d) (magnitude e) / magnitude d * magnitude n +
      Nat.lcm (magnitude d) (magnitude e) / magnitude e * magnitude m <
        UnsignedProduct.capacity (T := T)) (t0 : Nat) :
    let l := Nat.lcm (magnitude d) (magnitude e)
    let z := l / magnitude d * magnitude n + l / magnitude e * magnitude m
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_add_assign (⟨n, d⟩ : cp.Ratio T) (⟨m, e⟩ : cp.Ratio T)
    ⦃⇓ q c => ⌜q.1 = q.2 ∧ ((magnitude q.1.n : Int), (magnitude q.1.d : Int)) =
      RatioMath.add (magnitude n : Int) (magnitude d : Int) (magnitude m : Int) (magnitude e : Int) ∧
      c ≤ t0 + 8 + gcdCost (magnitude d) (magnitude e) + gcdCost z l⌝⦄ := by
  dsimp only
  obtain ⟨l, c₁, hr₁, hl, hc₁⟩ := run_of_triple (ratio_unsigned_lcm d e hlfit (t0 + 1))
  have hxfit : magnitude (l / d) * magnitude n < UnsignedProduct.capacity (T := T) := by
    rw [UnsignedDivision.div_eq, hl]
    omega
  have hyfit : magnitude (l / e) * magnitude m < UnsignedProduct.capacity (T := T) := by
    rw [UnsignedDivision.div_eq, hl]
    omega
  have hx : magnitude (l / d * n) = Nat.lcm (magnitude d) (magnitude e) / magnitude d * magnitude n := by
    rw [UnsignedProduct.mul_exact _ _ hxfit, UnsignedDivision.div_eq, hl]
  have hy : magnitude (l / e * m) = Nat.lcm (magnitude d) (magnitude e) / magnitude e * magnitude m := by
    rw [UnsignedProduct.mul_exact _ _ hyfit, UnsignedDivision.div_eq, hl]
  let z := l / d * n + l / e * m
  have hz : magnitude z = Nat.lcm (magnitude d) (magnitude e) / magnitude d * magnitude n +
      Nat.lcm (magnitude d) (magnitude e) / magnitude e * magnitude m := by
    exact (UnsignedAddSub.add_exact _ _ (by rw [hx, hy]; exact hsum)).trans (by rw [hx, hy])
  obtain ⟨q, c₂, hr₂, hp, hc₂⟩ := run_of_triple (ratio_unsigned_normalize_int z l c₁)
  refine triple_of_run (q, q) c₂ ?_ ⟨rfl, ?_, ?_⟩
  · change Option.bind ((cp.Ratio.numeric_lcm d e).run (t0 + 1)) (fun r₁ =>
      Option.bind ((cp.Ratio.normalize
        (⟨r₁.1 / d * n + r₁.1 / e * m, r₁.1⟩ : cp.Ratio T)).run r₁.2)
        (fun r₂ => some ((r₂.1, r₂.1), r₂.2))) = _
    rw [hr₁]
    simp only [Option.bind_some]
    rw [hr₂]
    rfl
  · rw [RatioMath.add_nat_pair, ← hz, ← hl]
    exact hp
  · rw [hz, hl] at hc₂
    omega

theorem ratio_unsigned_subtract {T : Type}
    [Zero T] [One T] [Neg T] [Add T] [Sub T] [Mul T] [Div T] [Mod T] [LT T]
    [DecidableLT T] [DecidableEq T]
    [UnsignedMagnitude T] [UnsignedDivision T] [UnsignedProduct T] [UnsignedAddSub T]
    (n d m e : T)
    (hlfit : Nat.lcm (magnitude d) (magnitude e) < UnsignedProduct.capacity (T := T))
    (hxbound : Nat.lcm (magnitude d) (magnitude e) / magnitude d * magnitude n <
      UnsignedProduct.capacity (T := T))
    (hybound : Nat.lcm (magnitude d) (magnitude e) / magnitude e * magnitude m <
      UnsignedProduct.capacity (T := T))
    (horder : Nat.lcm (magnitude d) (magnitude e) / magnitude e * magnitude m ≤
      Nat.lcm (magnitude d) (magnitude e) / magnitude d * magnitude n) (t0 : Nat) :
    let l := Nat.lcm (magnitude d) (magnitude e)
    let z := l / magnitude d * magnitude n - l / magnitude e * magnitude m
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_sub_assign (⟨n, d⟩ : cp.Ratio T) (⟨m, e⟩ : cp.Ratio T)
    ⦃⇓ q c => ⌜q.1 = q.2 ∧ ((magnitude q.1.n : Int), (magnitude q.1.d : Int)) =
      RatioMath.sub (magnitude n : Int) (magnitude d : Int) (magnitude m : Int) (magnitude e : Int) ∧
      c ≤ t0 + 8 + gcdCost (magnitude d) (magnitude e) + gcdCost z l⌝⦄ := by
  dsimp only
  obtain ⟨l, c₁, hr₁, hl, hc₁⟩ := run_of_triple (ratio_unsigned_lcm d e hlfit (t0 + 1))
  have hxfit : magnitude (l / d) * magnitude n < UnsignedProduct.capacity (T := T) := by
    rw [UnsignedDivision.div_eq, hl]
    omega
  have hyfit : magnitude (l / e) * magnitude m < UnsignedProduct.capacity (T := T) := by
    rw [UnsignedDivision.div_eq, hl]
    omega
  have hx : magnitude (l / d * n) = Nat.lcm (magnitude d) (magnitude e) / magnitude d * magnitude n := by
    rw [UnsignedProduct.mul_exact _ _ hxfit, UnsignedDivision.div_eq, hl]
  have hy : magnitude (l / e * m) = Nat.lcm (magnitude d) (magnitude e) / magnitude e * magnitude m := by
    rw [UnsignedProduct.mul_exact _ _ hyfit, UnsignedDivision.div_eq, hl]
  let z := l / d * n - l / e * m
  have hz : magnitude z = Nat.lcm (magnitude d) (magnitude e) / magnitude d * magnitude n -
      Nat.lcm (magnitude d) (magnitude e) / magnitude e * magnitude m := by
    exact (UnsignedAddSub.sub_exact _ _ (by rw [hx, hy]; exact horder)).trans (by rw [hx, hy])
  obtain ⟨q, c₂, hr₂, hp, hc₂⟩ := run_of_triple (ratio_unsigned_normalize_int z l c₁)
  refine triple_of_run (q, q) c₂ ?_ ⟨rfl, ?_, ?_⟩
  · change Option.bind ((cp.Ratio.numeric_lcm d e).run (t0 + 1)) (fun r₁ =>
      Option.bind ((cp.Ratio.normalize
        (⟨r₁.1 / d * n - r₁.1 / e * m, r₁.1⟩ : cp.Ratio T)).run r₁.2)
        (fun r₂ => some ((r₂.1, r₂.1), r₂.2))) = _
    rw [hr₁]
    simp only [Option.bind_some]
    rw [hr₂]
    rfl
  · rw [RatioMath.sub_nat_pair _ _ _ _ horder, ← hz, ← hl]
    exact hp
  · rw [hz, hl] at hc₂
    omega

theorem ratio_unsigned_add_value {T : Type}
    [Zero T] [One T] [Neg T] [Add T] [Sub T] [Mul T] [Div T] [Mod T] [LT T]
    [DecidableLT T] [DecidableEq T]
    [UnsignedMagnitude T] [UnsignedDivision T] [UnsignedProduct T] [UnsignedAddSub T]
    (n d m e : T)
    (hlfit : Nat.lcm (magnitude d) (magnitude e) < UnsignedProduct.capacity (T := T))
    (hsum : Nat.lcm (magnitude d) (magnitude e) / magnitude d * magnitude n +
      Nat.lcm (magnitude d) (magnitude e) / magnitude e * magnitude m <
        UnsignedProduct.capacity (T := T)) (hd : d ≠ 0) (he : e ≠ 0) (t0 : Nat) :
    let l := Nat.lcm (magnitude d) (magnitude e)
    let z := l / magnitude d * magnitude n + l / magnitude e * magnitude m
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_add_assign (⟨n, d⟩ : cp.Ratio T) (⟨m, e⟩ : cp.Ratio T)
    ⦃⇓ q c => ⌜q.1 = q.2 ∧ Rat.divInt (magnitude q.1.n : Int) (magnitude q.1.d : Int) =
      Rat.divInt (magnitude n : Int) (magnitude d : Int) +
        Rat.divInt (magnitude m : Int) (magnitude e : Int) ∧
      c ≤ t0 + 8 + gcdCost (magnitude d) (magnitude e) + gcdCost z l⌝⦄ := by
  dsimp only
  obtain ⟨r, c, hr, heq, hp, hc⟩ := run_of_triple (ratio_unsigned_add n d m e hlfit hsum t0)
  refine triple_of_run r c hr ⟨heq, ?_, hc⟩
  have hv := congrArg (fun p : Int × Int => Rat.divInt p.1 p.2) hp
  dsimp only at hv
  rw [hv]
  have hdmag : magnitude d ≠ 0 := fun h => hd ((zero_iff _).mp h)
  have hemag : magnitude e ≠ 0 := fun h => he ((zero_iff _).mp h)
  exact RatioMath.add_value _ _ _ _ (by omega) (by omega)

theorem ratio_unsigned_subtract_value {T : Type}
    [Zero T] [One T] [Neg T] [Add T] [Sub T] [Mul T] [Div T] [Mod T] [LT T]
    [DecidableLT T] [DecidableEq T]
    [UnsignedMagnitude T] [UnsignedDivision T] [UnsignedProduct T] [UnsignedAddSub T]
    (n d m e : T)
    (hlfit : Nat.lcm (magnitude d) (magnitude e) < UnsignedProduct.capacity (T := T))
    (hxbound : Nat.lcm (magnitude d) (magnitude e) / magnitude d * magnitude n <
      UnsignedProduct.capacity (T := T))
    (hybound : Nat.lcm (magnitude d) (magnitude e) / magnitude e * magnitude m <
      UnsignedProduct.capacity (T := T))
    (horder : Nat.lcm (magnitude d) (magnitude e) / magnitude e * magnitude m ≤
      Nat.lcm (magnitude d) (magnitude e) / magnitude d * magnitude n) (hd : d ≠ 0) (he : e ≠ 0) (t0 : Nat) :
    let l := Nat.lcm (magnitude d) (magnitude e)
    let z := l / magnitude d * magnitude n - l / magnitude e * magnitude m
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_sub_assign (⟨n, d⟩ : cp.Ratio T) (⟨m, e⟩ : cp.Ratio T)
    ⦃⇓ q c => ⌜q.1 = q.2 ∧ Rat.divInt (magnitude q.1.n : Int) (magnitude q.1.d : Int) =
      Rat.divInt (magnitude n : Int) (magnitude d : Int) -
        Rat.divInt (magnitude m : Int) (magnitude e : Int) ∧
      c ≤ t0 + 8 + gcdCost (magnitude d) (magnitude e) + gcdCost z l⌝⦄ := by
  dsimp only
  obtain ⟨r, c, hr, heq, hp, hc⟩ := run_of_triple (ratio_unsigned_subtract n d m e hlfit hxbound hybound horder t0)
  refine triple_of_run r c hr ⟨heq, ?_, hc⟩
  have hv := congrArg (fun p : Int × Int => Rat.divInt p.1 p.2) hp
  dsimp only at hv
  rw [hv]
  have hdmag : magnitude d ≠ 0 := fun h => hd ((zero_iff _).mp h)
  have hemag : magnitude e ≠ 0 := fun h => he ((zero_iff _).mp h)
  exact RatioMath.sub_value _ _ _ _ (by omega) (by omega)

theorem ratio_unsigned_compare {T : Type}
    [Zero T] [Neg T] [Mul T] [Div T] [Mod T] [LT T] [DecidableLT T] [DecidableEq T]
    [UnsignedMagnitude T] [One T] [UnsignedDivision T] [UnsignedProduct T] [UnsignedOrder T]
    (n d m e : T)
    (hxfit : magnitude e / Nat.gcd (magnitude d) (magnitude e) * magnitude n <
      UnsignedProduct.capacity (T := T))
    (hyfit : magnitude d / Nat.gcd (magnitude d) (magnitude e) * magnitude m <
      UnsignedProduct.capacity (T := T)) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_cmp (⟨n, d⟩ : cp.Ratio T) (⟨m, e⟩ : cp.Ratio T)
    ⦃⇓ q c => ⌜q = (if magnitude e / Nat.gcd (magnitude d) (magnitude e) * magnitude n <
        magnitude d / Nat.gcd (magnitude d) (magnitude e) * magnitude m then Ordering.lt
      else if magnitude d / Nat.gcd (magnitude d) (magnitude e) * magnitude m <
        magnitude e / Nat.gcd (magnitude d) (magnitude e) * magnitude n then Ordering.gt else Ordering.eq) ∧
      c ≤ t0 + 4 + gcdCost (magnitude d) (magnitude e)⌝⦄ := by
  obtain ⟨g, c, hr, hg, hc⟩ := run_of_triple (ratio_unsigned_gcd d e (t0 + 1))
  have hxbound : magnitude (e / g) * magnitude n < UnsignedProduct.capacity (T := T) := by
    simpa only [UnsignedDivision.div_eq, hg] using hxfit
  have hybound : magnitude (d / g) * magnitude m < UnsignedProduct.capacity (T := T) := by
    simpa only [UnsignedDivision.div_eq, hg] using hyfit
  have hx : magnitude (e / g * n) = magnitude e / Nat.gcd (magnitude d) (magnitude e) * magnitude n := by
    rw [UnsignedProduct.mul_exact _ _ hxbound, UnsignedDivision.div_eq, hg]
  have hy : magnitude (d / g * m) = magnitude d / Nat.gcd (magnitude d) (magnitude e) * magnitude m := by
    rw [UnsignedProduct.mul_exact _ _ hybound, UnsignedDivision.div_eq, hg]
  refine triple_of_run (if e / g * n < d / g * m then Ordering.lt
    else if d / g * m < e / g * n then Ordering.gt else Ordering.eq) c ?_ ⟨?_, by omega⟩
  · change Option.bind ((cp.Ratio.numeric_gcd d e).run (t0 + 1)) (fun r =>
      some ((if e / r.1 * n < d / r.1 * m then Ordering.lt
        else if d / r.1 * m < e / r.1 * n then Ordering.gt else Ordering.eq), r.2)) = _
    rw [hr]
    rfl
  · simp only [UnsignedOrder.lt_iff, hx, hy]

theorem ratio_unsigned_compare_value {T : Type}
    [Zero T] [Neg T] [Mul T] [Div T] [Mod T] [LT T] [DecidableLT T] [DecidableEq T]
    [UnsignedMagnitude T] [One T] [UnsignedDivision T] [UnsignedProduct T] [UnsignedOrder T]
    (n d m e : T)
    (hxfit : magnitude e / Nat.gcd (magnitude d) (magnitude e) * magnitude n <
      UnsignedProduct.capacity (T := T))
    (hyfit : magnitude d / Nat.gcd (magnitude d) (magnitude e) * magnitude m <
      UnsignedProduct.capacity (T := T)) (hd : d ≠ 0) (he : e ≠ 0) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_cmp (⟨n, d⟩ : cp.Ratio T) (⟨m, e⟩ : cp.Ratio T)
    ⦃⇓ q c => ⌜q = (if Rat.divInt (magnitude n : Int) (magnitude d : Int) <
        Rat.divInt (magnitude m : Int) (magnitude e : Int) then Ordering.lt
      else if Rat.divInt (magnitude m : Int) (magnitude e : Int) <
        Rat.divInt (magnitude n : Int) (magnitude d : Int) then Ordering.gt else Ordering.eq) ∧
      c ≤ t0 + 4 + gcdCost (magnitude d) (magnitude e)⌝⦄ := by
  obtain ⟨q, c, hr, hp, hc⟩ := run_of_triple (ratio_unsigned_compare n d m e hxfit hyfit t0)
  refine triple_of_run q c hr ⟨?_, hc⟩
  have hdmag : 0 < magnitude d := by
    have hn : magnitude d ≠ 0 := fun h => hd ((zero_iff _).mp h)
    omega
  have hemag : 0 < magnitude e := by
    have hn : magnitude e ≠ 0 := fun h => he ((zero_iff _).mp h)
    omega
  have hforward := RatioMath.compare_nat_lt (magnitude n) (magnitude d)
    (magnitude m) (magnitude e) hdmag hemag
  have hreverse := RatioMath.compare_nat_lt (magnitude m) (magnitude e)
    (magnitude n) (magnitude d) hemag hdmag
  rw [Nat.gcd_comm (magnitude e) (magnitude d)] at hreverse
  simpa only [hforward, hreverse] using hp

theorem ratio_unsigned_compare_value_bits {T : Type}
    [Zero T] [Neg T] [Mul T] [Div T] [Mod T] [LT T] [DecidableLT T] [DecidableEq T]
    [UnsignedMagnitude T] [One T] [UnsignedDivision T] [UnsignedProduct T] [UnsignedOrder T]
    (n d m e : T)
    (hxfit : magnitude e / Nat.gcd (magnitude d) (magnitude e) * magnitude n <
      UnsignedProduct.capacity (T := T))
    (hyfit : magnitude d / Nat.gcd (magnitude d) (magnitude e) * magnitude m <
      UnsignedProduct.capacity (T := T)) (hd : d ≠ 0) (he : e ≠ 0) (bits t0 : Nat)
    (hdb : magnitude d ≤ 2 ^ bits) (heb : magnitude e ≤ 2 ^ bits) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_cmp (⟨n, d⟩ : cp.Ratio T) (⟨m, e⟩ : cp.Ratio T)
    ⦃⇓ q c => ⌜q = (if Rat.divInt (magnitude n : Int) (magnitude d : Int) <
        Rat.divInt (magnitude m : Int) (magnitude e : Int) then Ordering.lt
      else if Rat.divInt (magnitude m : Int) (magnitude e : Int) <
        Rat.divInt (magnitude n : Int) (magnitude d : Int) then Ordering.gt else Ordering.eq) ∧
      c ≤ t0 + 6 * (bits + 1)⌝⦄ := by
  obtain ⟨q, c, hr, hp, hc⟩ := run_of_triple
    (ratio_unsigned_compare_value n d m e hxfit hyfit hd he t0)
  have hg := RatioCost.gcd_bits (magnitude d) (magnitude e) bits hdb heb
  exact triple_of_run q c hr ⟨hp, by omega⟩

theorem ratio_unsigned_increment_value {T : Type}
    [Zero T] [Mod T] [LT T] [Mul T] [Add T] [Sub T]
    [UnsignedMagnitude T] [UnsignedProduct T] [UnsignedAddSub T]
    (n d : T) (hfit : magnitude n + magnitude d < UnsignedProduct.capacity (T := T)) (hd : d ≠ 0) :
    Rat.divInt (magnitude (n + d) : Int) (magnitude d : Int) =
      Rat.divInt (magnitude n : Int) (magnitude d : Int) + 1 := by
  have hdmag : magnitude d ≠ 0 := fun h => hd ((zero_iff _).mp h)
  rw [UnsignedAddSub.add_exact _ _ hfit, Int.natCast_add]
  exact RatioMath.increment_value _ _ (by omega)

theorem ratio_unsigned_prefix_increment {T : Type}
    [Zero T] [Mod T] [LT T] [Mul T] [Add T] [Sub T]
    [UnsignedMagnitude T] [UnsignedProduct T] [UnsignedAddSub T]
    (n d : T) (hfit : magnitude n + magnitude d < UnsignedProduct.capacity (T := T)) (hd : d ≠ 0) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_inc_0 (⟨n, d⟩ : cp.Ratio T)
    ⦃⇓ q c => ⌜Rat.divInt (magnitude q.1.n : Int) (magnitude q.1.d : Int) =
        Rat.divInt (magnitude n : Int) (magnitude d : Int) + 1 ∧
      Rat.divInt (magnitude q.2.n : Int) (magnitude q.2.d : Int) =
        Rat.divInt (magnitude n : Int) (magnitude d : Int) + 1 ∧ c = t0 + 1⌝⦄ := by
  have hv := ratio_unsigned_increment_value n d hfit hd
  refine triple_of_run ((⟨n + d, d⟩ : cp.Ratio T), (⟨n + d, d⟩ : cp.Ratio T)) (t0 + 1) ?_ ⟨hv, hv, rfl⟩
  exact ratio_euclid_prefix_increment_run n d t0

theorem ratio_unsigned_postfix_increment {T : Type}
    [Zero T] [Mod T] [LT T] [Mul T] [Add T] [Sub T]
    [UnsignedMagnitude T] [UnsignedProduct T] [UnsignedAddSub T]
    (n d : T) (hfit : magnitude n + magnitude d < UnsignedProduct.capacity (T := T)) (hd : d ≠ 0) (tag : Int) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_inc_int (⟨n, d⟩ : cp.Ratio T) tag
    ⦃⇓ q c => ⌜Rat.divInt (magnitude q.1.n : Int) (magnitude q.1.d : Int) =
        Rat.divInt (magnitude n : Int) (magnitude d : Int) ∧
      Rat.divInt (magnitude q.2.n : Int) (magnitude q.2.d : Int) =
        Rat.divInt (magnitude n : Int) (magnitude d : Int) + 1 ∧ c = t0 + 2⌝⦄ := by
  have hv := ratio_unsigned_increment_value n d hfit hd
  refine triple_of_run ((⟨n, d⟩ : cp.Ratio T), (⟨n + d, d⟩ : cp.Ratio T)) (t0 + 2) ?_ ⟨rfl, hv, rfl⟩
  exact ratio_euclid_postfix_increment_run n d tag t0

theorem ratio_unsigned_decrement_value {T : Type}
    [Zero T] [Mod T] [LT T] [Mul T] [Add T] [Sub T]
    [UnsignedMagnitude T] [UnsignedProduct T] [UnsignedAddSub T]
    (n d : T) (hfit : magnitude d ≤ magnitude n) (hd : d ≠ 0) :
    Rat.divInt (magnitude (n - d) : Int) (magnitude d : Int) =
      Rat.divInt (magnitude n : Int) (magnitude d : Int) - 1 := by
  have hdmag : magnitude d ≠ 0 := fun h => hd ((zero_iff _).mp h)
  rw [UnsignedAddSub.sub_exact _ _ hfit, Int.natCast_sub hfit]
  exact RatioMath.decrement_value _ _ (by omega)

theorem ratio_unsigned_prefix_decrement {T : Type}
    [Zero T] [Mod T] [LT T] [Mul T] [Add T] [Sub T]
    [UnsignedMagnitude T] [UnsignedProduct T] [UnsignedAddSub T]
    (n d : T) (hfit : magnitude d ≤ magnitude n) (hd : d ≠ 0) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_dec_0 (⟨n, d⟩ : cp.Ratio T)
    ⦃⇓ q c => ⌜Rat.divInt (magnitude q.1.n : Int) (magnitude q.1.d : Int) =
        Rat.divInt (magnitude n : Int) (magnitude d : Int) - 1 ∧
      Rat.divInt (magnitude q.2.n : Int) (magnitude q.2.d : Int) =
        Rat.divInt (magnitude n : Int) (magnitude d : Int) - 1 ∧ c = t0 + 1⌝⦄ := by
  have hv := ratio_unsigned_decrement_value n d hfit hd
  refine triple_of_run ((⟨n - d, d⟩ : cp.Ratio T), (⟨n - d, d⟩ : cp.Ratio T)) (t0 + 1) ?_ ⟨hv, hv, rfl⟩
  exact ratio_euclid_prefix_decrement_run n d t0

theorem ratio_unsigned_postfix_decrement {T : Type}
    [Zero T] [Mod T] [LT T] [Mul T] [Add T] [Sub T]
    [UnsignedMagnitude T] [UnsignedProduct T] [UnsignedAddSub T]
    (n d : T) (hfit : magnitude d ≤ magnitude n) (hd : d ≠ 0) (tag : Int) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_dec_int (⟨n, d⟩ : cp.Ratio T) tag
    ⦃⇓ q c => ⌜Rat.divInt (magnitude q.1.n : Int) (magnitude q.1.d : Int) =
        Rat.divInt (magnitude n : Int) (magnitude d : Int) ∧
      Rat.divInt (magnitude q.2.n : Int) (magnitude q.2.d : Int) =
        Rat.divInt (magnitude n : Int) (magnitude d : Int) - 1 ∧ c = t0 + 2⌝⦄ := by
  have hv := ratio_unsigned_decrement_value n d hfit hd
  refine triple_of_run ((⟨n, d⟩ : cp.Ratio T), (⟨n - d, d⟩ : cp.Ratio T)) (t0 + 2) ?_ ⟨rfl, hv, rfl⟩
  exact ratio_euclid_postfix_decrement_run n d tag t0

theorem ratio_unsigned_unary_plus_value {T : Type} [Zero T] [Mod T] [LT T]
    [UnsignedMagnitude T] (n d : T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_add (⟨n, d⟩ : cp.Ratio T)
    ⦃⇓ q c => ⌜Rat.divInt (magnitude q.n : Int) (magnitude q.d : Int) =
      Rat.divInt (magnitude n : Int) (magnitude d : Int) ∧ c = t0 + 1⌝⦄ := by
  exact triple_of_run _ _ (ratio_euclid_unary_plus_run n d t0) ⟨rfl, rfl⟩

/-- Only zero has a representable mathematical negative in an unsigned type.
The concrete zero-negation equations are checked below for all four widths. -/
theorem ratio_unsigned_negate_zero {T : Type}
    [Zero T] [One T] [Neg T] [Div T] [Mod T] [LT T] [DecidableLT T] [DecidableEq T]
    (hneg : -(0 : T) = 0) (d : T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_sub (⟨0, d⟩ : cp.Ratio T)
    ⦃⇓ q c => ⌜q = ⟨0, 1⟩ ∧ c = t0 + 3⌝⦄ := by
  refine triple_of_run (⟨0, 1⟩ : cp.Ratio T) (t0 + 3) ?_ ⟨rfl, rfl⟩
  simp [cp.Ratio.op_sub, cp.Ratio.init_T_T, cp.Ratio.normalize, hneg,
    tick, StateT.run, modify]
  rfl

theorem ratio_negate_zero_uint8 (d : UInt8) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_sub (⟨0, d⟩ : cp.Ratio UInt8)
    ⦃⇓ q c => ⌜q = ⟨0, 1⟩ ∧ c = t0 + 3⌝⦄ := by
  exact ratio_unsigned_negate_zero UInt8.neg_zero d t0

theorem ratio_negate_zero_uint16 (d : UInt16) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_sub (⟨0, d⟩ : cp.Ratio UInt16)
    ⦃⇓ q c => ⌜q = ⟨0, 1⟩ ∧ c = t0 + 3⌝⦄ := by
  exact ratio_unsigned_negate_zero UInt16.neg_zero d t0

theorem ratio_negate_zero_uint32 (d : UInt32) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_sub (⟨0, d⟩ : cp.Ratio UInt32)
    ⦃⇓ q c => ⌜q = ⟨0, 1⟩ ∧ c = t0 + 3⌝⦄ := by
  exact ratio_unsigned_negate_zero UInt32.neg_zero d t0

theorem ratio_negate_zero_uint64 (d : UInt64) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Ratio.op_sub (⟨0, d⟩ : cp.Ratio UInt64)
    ⦃⇓ q c => ⌜q = ⟨0, 1⟩ ∧ c = t0 + 3⌝⦄ := by
  exact ratio_unsigned_negate_zero UInt64.neg_zero d t0

end Proofs.Cpp.Ratio
