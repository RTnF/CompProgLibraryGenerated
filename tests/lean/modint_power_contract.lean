open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.ModIntPowerModel

/-- The binary-power model carries only result, squared base and remaining
exponent. This counts its data, not the Lean evaluator's or C++ object's heap. -/
def loopStateBits (state : UInt64 × UInt64 × UInt64) : Nat :=
  bitWidth state.1.toNat + bitWidth state.2.1.toNat + bitWidth state.2.2.toNat

theorem loop_state_bits_bounded (state : UInt64 × UInt64 × UInt64) :
    loopStateBits state ≤ 192 := by
  have h₁ := bitWidth_lt_pow state.1.toNat 64 (UInt64.toNat_lt state.1)
  have h₂ := bitWidth_lt_pow state.2.1.toNat 64 (UInt64.toNat_lt state.2.1)
  have h₃ := bitWidth_lt_pow state.2.2.toNat 64 (UInt64.toNat_lt state.2.2)
  unfold loopStateBits
  omega

/-- A fixed caller envelope. The signed source exponent is encoded in its
64-bit source width; input range premises appear on the public power spec. -/
structure CallerFrame where
  modulus : UInt32
  base : UInt32
  exponentWord : UInt64
  magnitude : UInt64
  powered : UInt32
  normalized : UInt32
  result : UInt32

def CallerFrame.bits (_ : CallerFrame) : Nat := 5 * 32 + 2 * 64

theorem caller_frame_bits (frame : CallerFrame) : frame.bits = 288 := rfl

/-- Two fixed caller envelopes cover the public power-to-inverse nesting;
the binary loop has its own three-word state. This is model working data,
excluding the evaluator stack, C++ heap/lifetimes and atomic primitive internals. -/
theorem power_working_bits (power inverse : CallerFrame) (state : UInt64 × UInt64 × UInt64) :
    power.bits + inverse.bits + loopStateBits state ≤ 768 := by
  rw [caller_frame_bits, caller_frame_bits]
  have h := loop_state_bits_bounded state
  omega

theorem helper_eq (m base : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)] (exponent : UInt64) :
    cp.ModInt.pow_nonnegative (m := m) base exponent = (do
      let result ← cp.pow_mod base.toUInt64 exponent m.toUInt64
      pure result.toUInt32) := by
  simp only [cp.ModInt.pow_nonnegative, cp.pow_mod, bind_assoc, pure_bind]

theorem helper_run (m base : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (exponent : UInt64) (hm : 2 ≤ m.toNat) (start : Nat) :
    ∃ result : UInt32,
      (cp.ModInt.pow_nonnegative (m := m) base exponent).run start =
        some (result, start + 2 + bitWidth exponent.toNat) ∧
      result.toNat = base.toNat ^ exponent.toNat % m.toNat ∧ result.toNat < m.toNat := by
  have hbound := UInt32.toNat_lt m
  have h := PowMod.pow_mod_spec base.toUInt64 exponent m.toUInt64
    (by simpa using (show 1 ≤ m.toNat by omega)) (by simp; omega) start
  obtain ⟨result, ticks, hrun, hvalue, hticks⟩ := run_of_triple h
  have hrange : result.toNat < m.toNat := by
    simpa only [UInt32.toNat_toUInt64] using hvalue ▸ Nat.mod_lt
      (base.toUInt64.toNat ^ exponent.toNat) (show 0 < m.toUInt64.toNat by simpa using (show 0 < m.toNat by omega))
  have hcast : result.toUInt32.toNat = result.toNat := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  refine ⟨result.toUInt32, ?_, ?_, ?_⟩
  · rw [helper_eq]
    change Option.bind ((cp.pow_mod base.toUInt64 exponent m.toUInt64).run start)
      (fun r => some (r.1.toUInt32, r.2)) = _
    rw [hrun]
    simpa using congrArg (fun c => some (result.toUInt32, c)) hticks
  · simpa only [hcast, UInt32.toNat_toUInt64] using hvalue
  · simpa only [hcast] using hrange

theorem reduced_word_mod (x m : UInt32) (hx : x.toNat < m.toNat) : x % m = x := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_mod, Nat.mod_eq_of_lt hx]

theorem inverse_exponent (m : UInt32) (hm : 2 ≤ m.toNat) :
    (m - 2).toUInt64.toNat = m.toNat - 2 := by
  rw [UInt32.toNat_toUInt64, UInt32.toNat_sub_of_le _ _
    (UInt32.le_iff_toNat_le.mpr (by simpa using hm))]
  rfl

theorem inverse_run (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (value : cp.ModInt m) (hm : 2 ≤ m.toNat) (hx : value.x ≠ 0) (start : Nat) :
    ∃ result : cp.ModInt m,
      (cp.ModInt.inv value).run start =
        some (result, start + 4 + bitWidth (m.toNat - 2)) ∧
      result.x.toNat = value.x.toNat ^ (m.toNat - 2) % m.toNat ∧
      result.x.toNat < m.toNat := by
  obtain ⟨r, hr, hv, hb⟩ := helper_run m value.x (m - 2).toUInt64 hm (start + 1)
  simp only [inverse_exponent m hm] at hr hv
  refine ⟨⟨r⟩, ?_, hv, hb⟩
  dsimp only [cp.ModInt.inv]
  simp only [check]
  rw [show decide (value.x ≠ 0) = true from decide_eq_true hx]
  simp only [↓reduceIte, pure_bind]
  change Option.bind ((cp.ModInt.pow_nonnegative (m := m) value.x (m - 2).toUInt64).run (start + 1))
    (fun p => some ((⟨p.1 % m⟩ : cp.ModInt m), p.2 + 1)) = _
  rw [hr, Option.bind_some, reduced_word_mod r m hb]
  congr 2
  omega

theorem inverse_zero_fails (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)] (start : Nat) :
    (cp.ModInt.inv (⟨0⟩ : cp.ModInt m)).run start = none := by
  rfl

theorem inverse_correct (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (value : cp.ModInt m) (hp : Proofs.Fermat.IsPrime m.toNat)
    (hx : value.x.toNat < m.toNat) (hx0 : value.x ≠ 0) (start : Nat) :
    ∃ result : cp.ModInt m,
      (cp.ModInt.inv value).run start = some (result, start + 4 + bitWidth (m.toNat - 2)) ∧
      result.x.toNat < m.toNat ∧ (value.x.toNat * result.x.toNat) % m.toNat = 1 := by
  obtain ⟨r, hr, hv, hb⟩ := inverse_run m value hp.1 hx0 start
  refine ⟨r, hr, hb, ?_⟩
  rw [hv]
  apply ModIntMath.inverse_residue_unit m.toNat value.x.toNat hp _ hx
  have hn : value.x.toNat ≠ 0 := by
    intro h
    apply hx0
    exact UInt32.toNat_inj.mp (by simpa using h)
  omega

theorem nonnegative_exponent_word (n : Int) (hn : 0 ≤ n) (hmax : n ≤ 9223372036854775807) :
    (UInt64.ofInt n).toNat = n.toNat := by
  simp only [UInt64.ofInt, UInt64.toNat_ofNat']
  rw [Int.emod_eq_of_lt hn (by omega), Nat.mod_eq_of_lt (by omega)]

theorem power_nonnegative_run (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (value : cp.ModInt m) (n : Int) (hm : 2 ≤ m.toNat)
    (hn : 0 ≤ n) (hmax : n ≤ 9223372036854775807) (start : Nat) :
    ∃ result : cp.ModInt m,
      (cp.ModInt.pow value n).run start = some (result, start + 4 + bitWidth n.toNat) ∧
      result.x.toNat = value.x.toNat ^ n.toNat % m.toNat ∧ result.x.toNat < m.toNat := by
  obtain ⟨r, hr, hv, hb⟩ := helper_run m value.x (UInt64.ofInt n) hm (start + 1)
  simp only [nonnegative_exponent_word n hn hmax] at hr hv
  refine ⟨⟨r⟩, ?_, hv, hb⟩
  simp only [cp.ModInt.pow, show ¬n < 0 by omega, decide_false, Bool.false_eq_true, ↓reduceIte]
  change Option.bind ((cp.ModInt.pow_nonnegative (m := m) value.x (UInt64.ofInt n)).run (start + 1))
    (fun p => some ((⟨p.1 % m⟩ : cp.ModInt m), p.2 + 1)) = _
  rw [hr, Option.bind_some, reduced_word_mod r m hb]
  congr 2
  omega

theorem power_negative_run (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (value : cp.ModInt m) (n : Int) (hp : Proofs.Fermat.IsPrime m.toNat)
    (hx : value.x.toNat < m.toNat) (hx0 : value.x ≠ 0)
    (hn : n < 0) (hmin : -9223372036854775808 ≤ n) (start : Nat) :
    ∃ result : cp.ModInt m,
      (cp.ModInt.pow value n).run start = some
        (result, start + 8 + bitWidth n.natAbs + bitWidth (m.toNat - 2)) ∧
      result.x.toNat = (value.x.toNat ^ n.natAbs % m.toNat) ^ (m.toNat - 2) % m.toNat ∧
      result.x.toNat < m.toNat := by
  let magnitude : UInt64 := UInt64.ofInt (-(n + 1)) + 1
  have hmag : magnitude.toNat = n.natAbs := ModIntMath.negative_magnitude_word n hmin hn
  obtain ⟨r, hr, hv, hb⟩ := helper_run m value.x magnitude hp.1 (start + 1)
  rw [hmag] at hr hv
  have hxNat : 0 < value.x.toNat := by
    have : value.x.toNat ≠ 0 := fun h => hx0 (UInt32.toNat_inj.mp (by simpa using h))
    omega
  have hrNat : r.toNat ≠ 0 := by
    rw [hv]
    exact ModIntMath.power_residue_nonzero m.toNat value.x.toNat n.natAbs hp hxNat hx
  have hr0 : r ≠ 0 := fun h => hrNat (by rw [h]; rfl)
  obtain ⟨i, hi, hvi, hbi⟩ := inverse_run m (⟨r⟩ : cp.ModInt m) hp.1 hr0
    (start + 4 + bitWidth n.natAbs)
  refine ⟨i, ?_, ?_, hbi⟩
  · simp only [cp.ModInt.pow, hn, decide_true, ↓reduceIte]
    change Option.bind ((cp.ModInt.pow_nonnegative (m := m) value.x magnitude).run (start + 1))
      (fun p => (cp.ModInt.inv (⟨p.1 % m⟩ : cp.ModInt m)).run (p.2 + 1)) = _
    rw [hr, Option.bind_some, reduced_word_mod r m hb]
    rw [show (start + 1 + 2 + bitWidth n.natAbs) + 1 = start + 4 + bitWidth n.natAbs by omega]
    rw [show (start + 4 + bitWidth n.natAbs) + 4 + bitWidth (m.toNat - 2) =
      start + 8 + bitWidth n.natAbs + bitWidth (m.toNat - 2) by omega] at hi
    exact hi
  · simpa only [hv] using hvi

theorem power_negative_correct (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (value : cp.ModInt m) (n : Int) (hp : Proofs.Fermat.IsPrime m.toNat)
    (hx : value.x.toNat < m.toNat) (hx0 : value.x ≠ 0)
    (hn : n < 0) (hmin : -9223372036854775808 ≤ n) (start : Nat) :
    ∃ result : cp.ModInt m,
      (cp.ModInt.pow value n).run start = some
        (result, start + 8 + bitWidth n.natAbs + bitWidth (m.toNat - 2)) ∧
      result.x.toNat < m.toNat ∧ result.x.toNat * value.x.toNat ^ n.natAbs % m.toNat = 1 := by
  obtain ⟨r, hr, hv, hb⟩ := power_negative_run m value n hp hx hx0 hn hmin start
  have hxNat : 0 < value.x.toNat := by
    have : value.x.toNat ≠ 0 := fun h => hx0 (UInt32.toNat_inj.mp (by simpa using h))
    omega
  have hp0 := ModIntMath.power_residue_nonzero m.toNat value.x.toNat n.natAbs hp hxNat hx
  have hunit := ModIntMath.inverse_residue_unit m.toNat (value.x.toNat ^ n.natAbs % m.toNat)
    hp (by omega) (Nat.mod_lt _ (by have := hp.1; omega))
  refine ⟨r, hr, hb, ?_⟩
  rw [← Nat.mul_mod_mod, hv, Nat.mul_comm]
  exact hunit

theorem power_negative_zero_fails (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (n : Int) (hm : 2 ≤ m.toNat) (hn : n < 0) (hmin : -9223372036854775808 ≤ n) (start : Nat) :
    (cp.ModInt.pow (⟨0⟩ : cp.ModInt m) n).run start = none := by
  let magnitude : UInt64 := UInt64.ofInt (-(n + 1)) + 1
  have hmag : magnitude.toNat = n.natAbs := ModIntMath.negative_magnitude_word n hmin hn
  obtain ⟨r, hr, hv, hb⟩ := helper_run m 0 magnitude hm (start + 1)
  rw [hmag] at hr hv
  have habs : 0 < n.natAbs := by omega
  simp only [UInt32.toNat_zero, Nat.zero_pow habs, Nat.zero_mod] at hv
  have hz : r = 0 := UInt32.toNat_inj.mp (by simpa using hv)
  simp only [cp.ModInt.pow, hn, decide_true, ↓reduceIte]
  change Option.bind ((cp.ModInt.pow_nonnegative (m := m) 0 magnitude).run (start + 1))
    (fun p => (cp.ModInt.inv (⟨p.1 % m⟩ : cp.ModInt m)).run (p.2 + 1)) = _
  rw [hr, Option.bind_some, hz, reduced_word_mod 0 m (by simp; omega)]
  exact inverse_zero_fails m _

theorem division_assign_step (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (a b inverse : cp.ModInt m) (start finish : Nat)
    (hi : (cp.ModInt.inv b).run (start + 1) = some (inverse, finish)) :
    (cp.ModInt.op_div_assign a b).run start = some
      (((⟨ModIntMath.mulWord32 m a.x inverse.x⟩ : cp.ModInt m),
        ⟨ModIntMath.mulWord32 m a.x inverse.x⟩), finish + 1) := by
  change Option.bind ((cp.ModInt.inv b).run (start + 1)) (fun p => some
    (((⟨ModIntMath.mulWord32 m a.x p.1.x⟩ : cp.ModInt m),
      (⟨ModIntMath.mulWord32 m a.x p.1.x⟩ : cp.ModInt m)), p.2 + 1)) = _
  rw [hi]
  rfl

theorem division_assign_run (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (a b : cp.ModInt m) (hm : 2 ≤ m.toNat) (hb0 : b.x ≠ 0) (start : Nat) :
    ∃ result : cp.ModInt m,
      (cp.ModInt.op_div_assign a b).run start =
        some ((result, result), start + 6 + bitWidth (m.toNat - 2)) ∧
      result.x.toNat = a.x.toNat * (b.x.toNat ^ (m.toNat - 2) % m.toNat) % m.toNat ∧
      result.x.toNat < m.toNat := by
  obtain ⟨i, hi, hv, hb⟩ := inverse_run m b hm hb0 (start + 1)
  refine ⟨⟨ModIntMath.mulWord32 m a.x i.x⟩, ?_, ?_, ?_⟩
  · have step := division_assign_step m a b i _ _ hi
    rw [show (start + 1 + 4 + bitWidth (m.toNat - 2)) + 1 =
      start + 6 + bitWidth (m.toNat - 2) by omega] at step
    exact step
  · rw [ModIntMath.mulWord32_toNat m a.x i.x (by omega), hv]
  · rw [ModIntMath.mulWord32_toNat m a.x i.x (by omega)]
    exact Nat.mod_lt _ (by omega)

theorem division_assign_correct (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (a b : cp.ModInt m) (hp : Proofs.Fermat.IsPrime m.toNat)
    (ha : a.x.toNat < m.toNat) (hb : b.x.toNat < m.toNat) (hb0 : b.x ≠ 0) (start : Nat) :
    ∃ result : cp.ModInt m,
      (cp.ModInt.op_div_assign a b).run start =
        some ((result, result), start + 6 + bitWidth (m.toNat - 2)) ∧
      result.x.toNat < m.toNat ∧ result.x.toNat * b.x.toNat % m.toNat = a.x.toNat := by
  obtain ⟨r, hr, hv, hbnd⟩ := division_assign_run m a b hp.1 hb0 start
  refine ⟨r, hr, hbnd, ?_⟩
  rw [hv]
  apply ModIntMath.quotient_residue_unit m.toNat a.x.toNat b.x.toNat hp ha _ hb
  have hn : b.x.toNat ≠ 0 := by
    intro h
    exact hb0 (UInt32.toNat_inj.mp (by simpa using h))
  omega

theorem division_run (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (a b : cp.ModInt m) (hm : 2 ≤ m.toNat) (hb0 : b.x ≠ 0) (start : Nat) :
    ∃ result : cp.ModInt m,
      (cp.op_div_ModInt_ModInt a b).run start = some (result, start + 7 + bitWidth (m.toNat - 2)) ∧
      result.x.toNat = a.x.toNat * (b.x.toNat ^ (m.toNat - 2) % m.toNat) % m.toNat ∧
      result.x.toNat < m.toNat := by
  obtain ⟨r, hr, hv, hb⟩ := division_assign_run m a b hm hb0 (start + 1)
  refine ⟨r, ?_, hv, hb⟩
  change Option.bind ((cp.ModInt.op_div_assign a b).run (start + 1))
    (fun p => some (p.1.1, p.2)) = _
  rw [hr]
  rfl

theorem division_correct (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (a b : cp.ModInt m) (hp : Proofs.Fermat.IsPrime m.toNat)
    (ha : a.x.toNat < m.toNat) (hb : b.x.toNat < m.toNat) (hb0 : b.x ≠ 0) (start : Nat) :
    ∃ result : cp.ModInt m,
      (cp.op_div_ModInt_ModInt a b).run start = some (result, start + 7 + bitWidth (m.toNat - 2)) ∧
      result.x.toNat < m.toNat ∧ result.x.toNat * b.x.toNat % m.toNat = a.x.toNat := by
  obtain ⟨r, hr, hv, hbnd⟩ := division_run m a b hp.1 hb0 start
  refine ⟨r, hr, hbnd, ?_⟩
  rw [hv]
  apply ModIntMath.quotient_residue_unit m.toNat a.x.toNat b.x.toNat hp ha _ hb
  have hn : b.x.toNat ≠ 0 := by
    intro h
    exact hb0 (UInt32.toNat_inj.mp (by simpa using h))
  omega

theorem bitwidth_log_succ (n : Nat) : bitWidth n ≤ Nat.log2 (n + 1) + 1 := by
  calc
    bitWidth n ≤ bitWidth (n + 1) := bitWidth_mono (Nat.le_succ n)
    _ = Nat.log2 (n + 1) + 1 := by simp [bitWidth]

theorem inverse_bitwidth_log (m : Nat) (hm : 2 ≤ m) : bitWidth (m - 2) ≤ Nat.log2 m + 1 := by
  calc
    bitWidth (m - 2) ≤ bitWidth m := bitWidth_mono (Nat.sub_le m 2)
    _ = Nat.log2 m + 1 := by simp [bitWidth, show m ≠ 0 by omega]

theorem power_correct_and_log_work (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (value : cp.ModInt m) (n : Int) (hp : Proofs.Fermat.IsPrime m.toNat)
    (hx : value.x.toNat < m.toNat) (hx0 : n < 0 → value.x ≠ 0)
    (hmin : -9223372036854775808 ≤ n) (hmax : n ≤ 9223372036854775807) (start : Nat) :
    ∃ result : cp.ModInt m, ∃ finish : Nat,
      (cp.ModInt.pow value n).run start = some (result, finish) ∧
      result.x.toNat = ModIntMath.signedPowerResidue m.toNat value.x.toNat n ∧
      result.x.toNat < m.toNat ∧
      finish ≤ start + 10 * (1 + Nat.log2 (n.natAbs + 1) + Nat.log2 m.toNat) := by
  by_cases hn : n < 0
  · obtain ⟨r, hr, hv, hb⟩ := power_negative_run m value n hp hx (hx0 hn) hn hmin start
    refine ⟨r, _, hr, ?_, hb, ?_⟩
    · simpa only [ModIntMath.signedPowerResidue, hn, ↓reduceIte] using hv
    · have h₁ := bitwidth_log_succ n.natAbs
      have h₂ := inverse_bitwidth_log m.toNat hp.1
      omega
  · obtain ⟨r, hr, hv, hb⟩ := power_nonnegative_run m value n hp.1 (by omega) hmax start
    refine ⟨r, _, hr, ?_, hb, ?_⟩
    · simpa only [ModIntMath.signedPowerResidue, hn, ↓reduceIte] using hv
    · have h₁ := bitwidth_log_succ n.toNat
      have hn' := Int.natAbs_of_nonneg (show 0 ≤ n by omega)
      have h₂ : n.natAbs = n.toNat := by omega
      rw [h₂]
      omega

theorem inverse_log_work (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (value : cp.ModInt m) (hm : 2 ≤ m.toNat) (hx : value.x ≠ 0) (start : Nat) :
    ∃ result : cp.ModInt m, ∃ finish : Nat,
      (cp.ModInt.inv value).run start = some (result, finish) ∧
      finish ≤ start + 5 + Nat.log2 m.toNat := by
  obtain ⟨r, hr, _, _⟩ := inverse_run m value hm hx start
  refine ⟨r, _, hr, ?_⟩
  have h := inverse_bitwidth_log m.toNat hm
  omega

theorem division_log_work (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (a b : cp.ModInt m) (hm : 2 ≤ m.toNat) (hb0 : b.x ≠ 0) (start : Nat) :
    ∃ result : cp.ModInt m, ∃ finish : Nat,
      (cp.op_div_ModInt_ModInt a b).run start = some (result, finish) ∧
      finish ≤ start + 8 + Nat.log2 m.toNat := by
  obtain ⟨r, hr, _, _⟩ := division_run m a b hm hb0 start
  refine ⟨r, _, hr, ?_⟩
  have h := inverse_bitwidth_log m.toNat hm
  omega

end Proofs.Cpp.ModIntPowerModel
