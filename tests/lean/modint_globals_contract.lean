-- Appended to the freshly generated entire original ModInt file.
-- Arithmetic correctness of the modular operators is a separate obligation.
open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.ModIntGlobalsModel

variable [TemplateConstraint ((2 : UInt32) ≤ (998244353 : UInt32))]

local instance : Mod Int := ⟨Int.tmod⟩

def indexWord (i : Int) : UInt32 := UInt32.ofInt (ModIntMath.signedNormalize i 998244353)

theorem indexWord_toNat (i : Int) (hi : 0 ≤ i) (hiN : i < 20000003) :
    (indexWord i).toNat = i.toNat := by
  unfold indexWord
  rw [ModIntMath.signed_normalize_eq i 998244353 (by decide),
      Int.emod_eq_of_lt hi (by omega), ModIntMath.u32_ofInt_toNat i hi (by omega)]

theorem init_step (fac : Array cp.mint) (L : Nat) (hL : L < 20000002)
    (hsz : fac.size = 20000003)
    (hp : ∀ k, k ≤ L → fac[k]!.x.toNat = ModIntFactorial.factorialResidue 998244353 k) :
    ∀ k, k ≤ L + 1 →
      (set fac (1 + (L : Int))
        (⟨ModIntMath.mulWord32 998244353 (get fac (1 + (L : Int) - 1)).x
          (indexWord (1 + (L : Int)))⟩ : cp.mint))[k]!.x.toNat =
        ModIntFactorial.factorialResidue 998244353 k := by
  intro k hk
  have e1 : (1 + (L : Int)).toNat = L + 1 := by omega
  have e2 : 1 + (L : Int) - 1 = (L : Int) := by omega
  rw [getElemBang_set _ _ _ k (by omega), e1]
  by_cases he : k = L + 1
  · subst k
    simp only [ite_true]
    rw [ModIntMath.mulWord32_toNat _ _ _ (by decide), e2, get_natCast, hp L (Nat.le_refl _),
        indexWord_toNat _ (by omega) (by omega), e1]
    exact ModIntFactorial.factorial_step 998244353 L
  · simp only [he, ite_false]
    exact hp k (by omega)

/-- Functional array update model with a symbolic loop endpoint. Each loop
body accounts for its loop, constructor, binary wrapper and multiplication. -/
def initModel (limit : Int) (state : cp.GlobalState) : M cp.GlobalState := do
  tick
  check (decide (state.fac.size = 20000003))
  tick
  let mut fac := set state.fac 0 (⟨indexWord 1⟩ : cp.mint)
  for i in range 1 limit do
    tick
    tick
    tick
    tick
    fac := set fac i
      (⟨ModIntMath.mulWord32 998244353 (get fac (i - 1)).x (indexWord i)⟩ : cp.mint)
  return { fac }

theorem init_model_eq (state : cp.GlobalState) : cp.init state = initModel cp.MAX_FAC state := by
  rfl

theorem init_model_spec (limit : Int) (hl : limit = 20000003)
    (state : cp.GlobalState) (hs : state.fac.size = 20000003) (start : Nat) :
    ⦃fun c => ⌜c = start⌝⦄ initModel limit state
    ⦃⇓ result c => ⌜result.fac.size = 20000003 ∧
      (∀ k, k < 20000003 → result.fac[k]!.x.toNat = ModIntFactorial.factorialResidue 998244353 k) ∧
      c = start + 2 + 4 * 20000002⌝⦄ := by
  mvcgen [initModel]
  case inv1 =>
    exact ⇓⟨xs, fac⟩ c => ⌜fac.size = 20000003 ∧
      (∀ k, k ≤ xs.prefix.length → fac[k]!.x.toNat = ModIntFactorial.factorialResidue 998244353 k) ∧
      c = start + 2 + 4 * xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  all_goals try contradiction
  · have hlr := range_prefix_length ‹range _ _ = _ ++ _ :: _›
    have he := range_cursor ‹range _ _ = _ ++ _ :: _›
    subst he
    obtain ⟨hsz, hp, hc⟩ := ‹_ ∧ _ ∧ _›
    exact ⟨hsz, init_step _ _ (by omega) hsz hp, by omega⟩
  · refine ⟨hs, ?_, ‹_›⟩
    rw [getElemBang_set _ _ _ _ (by omega)]
    rfl
  · obtain ⟨hsz, hp, hc⟩ := ‹_ ∧ _ ∧ _›
    have hlen : (range 1 limit).length = 20000002 := by
      unfold range
      rw [List.length_map, List.length_range]
      omega
    rw [hlen] at hp hc
    exact ⟨hsz, fun k hk => hp k (by omega), by omega⟩

def initialModel (count : Nat) : M cp.GlobalState := do
  tick
  let mut fac : Array cp.mint := Array.empty
  for _ in [:count] do
    tick
    tick
    fac := fac.push (⟨0⟩ : cp.mint)
  return { fac }

theorem initial_model_eq : cp.initializeGlobals = initialModel 20000003 := by rfl

theorem initial_spec (count start : Nat) :
    ⦃fun c => ⌜c = start⌝⦄ initialModel count
    ⦃⇓ result c => ⌜result.fac = Array.replicate count (⟨0⟩ : cp.mint) ∧
      c = start + 1 + 2 * count⌝⦄ := by
  mvcgen [initialModel]
  case inv1 =>
    exact ⇓⟨xs, fac⟩ c => ⌜fac = Array.replicate xs.prefix.length (⟨0⟩ : cp.mint) ∧
      c = start + 1 + 2 * xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  · obtain ⟨ha, hc⟩ := ‹_ ∧ _›
    rw [ha, ← Array.replicate_succ]
    exact ⟨rfl, by omega⟩
  · exact ⟨rfl, ‹_ = start›⟩
  · assumption

theorem initial_model_run (count start : Nat) :
    ∃ state : cp.GlobalState,
      (initialModel count).run start = some (state, start + 1 + 2 * count) ∧
      state.fac = Array.replicate count (⟨0⟩ : cp.mint) := by
  obtain ⟨state, finish, hr, ha, hc⟩ := run_of_triple (initial_spec count start)
  exact ⟨state, hc ▸ hr, ha⟩

theorem initial_run (start : Nat) :
    ∃ state : cp.GlobalState,
      cp.initializeGlobals.run start = some (state, start + 1 + 2 * 20000003) ∧
      state.fac = Array.replicate 20000003 (⟨0⟩ : cp.mint) := by
  rw [initial_model_eq]
  exact initial_model_run 20000003 start

/-- Evaluate the quotient using a read-only factorial table. -/
def tableQuotient (fac : Array cp.mint) (n k : Int) : M cp.mint := do
  tick
  check (decide (fac.size = 20000003))
  let denominator ← cp.op_mul_ModInt_ModInt (m := (998244353 : UInt32))
    (Cpp.get fac k) (Cpp.get fac (n - k))
  cp.op_div_ModInt_ModInt (m := (998244353 : UInt32)) (Cpp.get fac n) denominator

theorem combination_eq (state : cp.GlobalState) (n k : Int) :
    cp.C n k state = (do
      let result ← tableQuotient state.fac n k
      pure (result, state)) := by
  cases state
  simp only [cp.C, tableQuotient, bind_assoc, pure_bind]

theorem combination_run (state : cp.GlobalState) (n k : Int)
    (result : cp.mint) (start finish : Nat)
    (h : (tableQuotient state.fac n k).run start = some (result, finish)) :
    (cp.C n k state).run start = some ((result, state), finish) := by
  rw [combination_eq]
  change Option.bind ((tableQuotient state.fac n k).run start)
    (fun r => some ((r.1, state), r.2)) = _
  rw [h]
  rfl

theorem combination_preserves_state (state after : cp.GlobalState) (n k : Int)
    (result : cp.mint) (start finish : Nat)
    (h : (cp.C n k state).run start = some ((result, after), finish)) : after = state := by
  rw [combination_eq] at h
  change Option.bind ((tableQuotient state.fac n k).run start)
    (fun r => some ((r.1, state), r.2)) = _ at h
  cases hr : (tableQuotient state.fac n k).run start with
  | none => simp only [hr, Option.bind_none, reduceCtorEq] at h
  | some value =>
    simp only [hr, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
    exact h.1.2.symm

def TableRep (fac : Array cp.mint) : Prop :=
  fac.size = 20000003 ∧
    ∀ k, k < 20000003 → fac[k]!.x.toNat = ModIntFactorial.factorialResidue 998244353 k

theorem table_run_of_spec (action : M cp.GlobalState) (start : Nat)
    (h : ⦃fun c => ⌜c = start⌝⦄ action
      ⦃⇓ result c => ⌜result.fac.size = 20000003 ∧
        (∀ k, k < 20000003 → result.fac[k]!.x.toNat = ModIntFactorial.factorialResidue 998244353 k) ∧
        c = start + 2 + 4 * 20000002⌝⦄) :
    ∃ result : cp.GlobalState,
      action.run start = some (result, start + 2 + 4 * 20000002) ∧ TableRep result.fac := by
  obtain ⟨r, finish, hr, hsz, hv, hc⟩ := run_of_triple h
  exact ⟨r, hc ▸ hr, hsz, hv⟩

theorem init_model_run (limit : Int) (hl : limit = 20000003)
    (state : cp.GlobalState) (hs : state.fac.size = 20000003) (start : Nat) :
    ∃ result : cp.GlobalState,
      (initModel limit state).run start = some (result, start + 2 + 4 * 20000002) ∧ TableRep result.fac := by
  exact table_run_of_spec _ start (init_model_spec limit hl state hs start)

theorem init_run (state : cp.GlobalState) (hs : state.fac.size = 20000003) (start : Nat) :
    ∃ result : cp.GlobalState,
      (cp.init state).run start = some (result, start + 2 + 4 * 20000002) ∧ TableRep result.fac := by
  rw [init_model_eq]
  exact init_model_run cp.MAX_FAC rfl state hs start

theorem combination_correct (state : cp.GlobalState) (n k : Nat) (hrep : TableRep state.fac)
    (hn : n < 20000003) (hk : k ≤ n) (start : Nat) :
    ∃ result : cp.mint,
      (cp.C (n : Int) (k : Int) state).run start = some ((result, state), start + 40) ∧
      result.x.toNat = n.choose k % 998244353 ∧ result.x.toNat < 998244353 := by
  let a : cp.mint := get state.fac (n : Int)
  let b : cp.mint := get state.fac (k : Int)
  let c : cp.mint := get state.fac ((n : Int) - (k : Int))
  have ha : a.x.toNat = ModIntFactorial.factorialResidue 998244353 n := by
    exact hrep.2 n hn
  have hb : b.x.toNat = ModIntFactorial.factorialResidue 998244353 k := by
    exact hrep.2 k (by omega)
  have hc : c.x.toNat = ModIntFactorial.factorialResidue 998244353 (n - k) := by
    dsimp [c]
    rw [show (n : Int) - (k : Int) = ((n - k : Nat) : Int) by omega, get_natCast]
    exact hrep.2 _ (by omega)
  let d : cp.mint := ⟨ModIntMath.mulWord32 998244353 b.x c.x⟩
  have hd : d.x.toNat = ModIntFactorial.denominator 998244353 n k := by
    dsimp [d]
    rw [ModIntMath.mulWord32_toNat _ _ _ (by decide), hb, hc]
    exact (Nat.mul_mod _ _ _).symm
  have hp := ModIntFactorial.fixed_modulus_prime
  have hd0 : d.x ≠ 0 := by
    intro hz
    have hv := congrArg UInt32.toNat hz
    rw [hd] at hv
    exact ModIntFactorial.denominator_nonzero 998244353 n k hp (by omega) hk hv
  obtain ⟨r, hr, hv, hrange⟩ := ModIntPowerModel.division_run 998244353 a d (by decide) hd0 (start + 3)
  have hbw : bitWidth (998244353 - 2) = 30 := by decide
  refine ⟨r, ?_, ?_, hrange⟩
  · rw [combination_eq]
    unfold tableQuotient
    rw [show state.fac.size = 20000003 from hrep.1]
    simp only [decide_true, check, ↓reduceIte, pure_bind]
    change Option.bind ((cp.op_mul_ModInt_ModInt b c).run (start + 1)) (fun p =>
      Option.bind ((cp.op_div_ModInt_ModInt a p.1).run p.2)
        (fun q => some ((q.1, state), q.2))) = _
    rw [ModIntArithmeticModel.mul_run 998244353 b c (start + 1), Option.bind_some]
    change Option.bind ((cp.op_div_ModInt_ModInt a d).run (start + 3))
      (fun q => some ((q.1, state), q.2)) = _
    rw [hr, Option.bind_some]
    change some ((r, state), start + 3 + 7 + bitWidth (998244353 - 2)) = _
    rw [hbw]
  · rw [hv, ha, hd]
    exact ModIntFactorial.binomial_correct 998244353 n k hp (by omega) hk

/-- The full source initialization followed by a query. The returned table
is retained, allowing subsequent queries without rebuilding it. -/
theorem init_combination_run (state : cp.GlobalState) (hs : state.fac.size = 20000003)
    (n k : Nat) (hn : n < 20000003) (hk : k ≤ n) (start : Nat) :
    ∃ result : cp.mint, ∃ after : cp.GlobalState,
      ((do
        let ready ← cp.init state
        cp.C (n : Int) (k : Int) ready) : M (cp.mint × cp.GlobalState)).run start =
        some ((result, after), (start + 2 + 4 * 20000002) + 40) ∧
      TableRep after.fac ∧ result.x.toNat = n.choose k % 998244353 := by
  obtain ⟨after, hi, ht⟩ := init_run state hs start
  obtain ⟨result, hc, hv, _⟩ := combination_correct after n k ht hn hk _
  refine ⟨result, after, ?_, ht, hv⟩
  change Option.bind ((cp.init state).run start) _ = _
  rw [hi, Option.bind_some]
  exact hc

/-- Startup, initialization, and a query are all connected to the original
entry points. No concrete table is evaluated while checking this theorem. -/
theorem startup_combination_run (n k : Nat) (hn : n < 20000003) (hk : k ≤ n)
    (start : Nat) :
    ∃ result : cp.mint, ∃ after : cp.GlobalState,
      ((do
        let zero ← cp.initializeGlobals
        let ready ← cp.init zero
        cp.C (n : Int) (k : Int) ready) : M (cp.mint × cp.GlobalState)).run start =
        some ((result, after), ((start + 1 + 2 * 20000003) + 2 + 4 * 20000002) + 40) ∧
      TableRep after.fac ∧ result.x.toNat = n.choose k % 998244353 := by
  obtain ⟨zero, hz, ha⟩ := initial_run start
  have hs : zero.fac.size = 20000003 := by rw [ha, Array.size_replicate]
  obtain ⟨result, after, hc, ht, hv⟩ := init_combination_run zero hs n k hn hk _
  refine ⟨result, after, ?_, ht, hv⟩
  change Option.bind (cp.initializeGlobals.run start) _ = _
  rw [hz, Option.bind_some]
  exact hc

/-- Array data in the model consists of one 32-bit word per table entry.
This excludes C++ heap/lifetime and the evaluator's own storage. -/
def tableDataBits (state : cp.GlobalState) : Nat := 32 * state.fac.size

theorem table_data_bound (state : cp.GlobalState) (h : TableRep state.fac) :
    tableDataBits state = 32 * 20000003 := by
  exact congrArg (32 * ·) h.1

theorem initialization_linear_work (count : Nat) :
    1 + 2 * count ≤ 3 * (count + 1) := by omega

theorem factorial_linear_work (count : Nat) :
    2 + 4 * count ≤ 4 * (count + 1) := by omega

end Proofs.Cpp.ModIntGlobalsModel
