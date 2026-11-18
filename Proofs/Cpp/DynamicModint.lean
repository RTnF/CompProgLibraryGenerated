import Proofs.Cpp.Gen.DynamicModint
import Proofs.Cpp.Lib.DynamicModIntFactorial
import Proofs.Cpp.Lib.Basic
import Proofs.Cpp.PowMod

namespace Proofs.Cpp.DynamicModint

open Proofs.Cpp.Gen

abbrev DynamicModIntState := cp.GlobalState_7c88ab5d43806a08
abbrev dynamicModIntStartup := cp.initializeGlobals_7c88ab5d43806a08

end Proofs.Cpp.DynamicModint

namespace Proofs.Cpp.DynamicModint

open Proofs.Cpp Proofs.Cpp.Gen

theorem startup_run (start : Nat) :
    dynamicModIntStartup.run start =
      some (({ DynamicModInt_m := 998244353
               factorial_cached_modulus := 0
               factorial_fac := Array.empty
               factorial_inv_cached_modulus := 0
               factorial_inv_fac_inv := Array.empty } : DynamicModIntState), start + 1) := by
  rfl

theorem add_run (state : DynamicModIntState) (a b : cp.DynamicModInt) (start : Nat) :
    let result : cp.DynamicModInt := ⟨ModIntMath.addWord32 state.DynamicModInt_m a.x b.x⟩
    (cp.DynamicModInt.op_add_assign a b state).run start =
      some ((result, result, state), start + 1) := by
  cases state
  rfl

theorem sub_run (state : DynamicModIntState) (a b : cp.DynamicModInt) (start : Nat) :
    let result : cp.DynamicModInt := ⟨ModIntMath.subWord32 state.DynamicModInt_m a.x b.x⟩
    (cp.DynamicModInt.op_sub_assign a b state).run start =
      some ((result, result, state), start + 1) := by
  cases state
  rfl

theorem mul_run (state : DynamicModIntState) (a b : cp.DynamicModInt) (start : Nat) :
    let result : cp.DynamicModInt := ⟨ModIntMath.mulWord32 state.DynamicModInt_m a.x b.x⟩
    (cp.DynamicModInt.op_mul_assign a b state).run start =
      some ((result, result, state), start + 1) := by
  cases state
  rfl

theorem power_word_eq (base : UInt32) (exponent : UInt64) (m : UInt32) :
    cp.dynamic_modint_pow_word base exponent m = (do
      let result ← cp.pow_mod base.toUInt64 exponent m.toUInt64
      pure result.toUInt32) := by
  simp only [cp.dynamic_modint_pow_word, cp.pow_mod, bind_assoc, pure_bind]

theorem power_helper_eq (state : DynamicModIntState) (base : UInt32) (exponent : UInt64) :
    cp.DynamicModInt.pow_nonnegative base exponent state = (do
      tick
      let result ← cp.dynamic_modint_pow_word base exponent state.DynamicModInt_m
      pure (result, state)) := by
  cases state
  rfl

/-- Three cache operations are sequenced in source order. Their returned
state is threaded into the two modular multiplications. -/
theorem combination_eq (state : DynamicModIntState)
    (n k : Nat) (hk : k ≤ n) :
    cp.dynamic_modint.C (n : Int) (k : Int) state = (do
      tick
      let (numerator, afterNumerator) ← cp.factorial (n : Int) state
      let (left, afterLeft) ← cp.factorial_inv (k : Int) afterNumerator
      let (right, afterRight) ← cp.factorial_inv ((n - k : Nat) : Int) afterLeft
      let (partialProduct, afterProduct) ←
        cp.op_mul_DynamicModInt_DynamicModInt numerator left afterRight
      cp.op_mul_DynamicModInt_DynamicModInt partialProduct right afterProduct) := by
  have hkn : (k : Int) ≤ (n : Int) := by omega
  have hsub : (n : Int) - (k : Int) = ((n - k : Nat) : Int) := by omega
  simp only [cp.dynamic_modint.C, Int.natCast_nonneg, hkn, decide_true, check, ite_true, pure_bind, hsub]
  rfl

end Proofs.Cpp.DynamicModint

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.DynamicModint

def FactorialPrefix (m : UInt32) (used : Nat) (fac : Array cp.DynamicModInt) : Prop :=
  ∀ i, i < used → fac[i]!.x.toNat = ModIntFactorial.factorialResidue m.toNat i

def factorWord (m : UInt32) (i : Int) : UInt32 :=
  (UInt64.ofInt i % m.toUInt64).toUInt32

theorem factorWord_value (m : UInt32) (i : Nat) (hm : 0 < m.toNat) (hi : i < 2^64) :
    (factorWord m (i : Int)).toNat = i % m.toNat := by
  have hi64 : (UInt64.ofInt (i : Int)).toNat = i := by
    have hh : (i : Int) % (2 ^ 64 : Int) = (i : Int) :=
      Int.emod_eq_of_lt (by omega) (by exact_mod_cast hi)
    rw [UInt64.ofInt, hh, Int.toNat_natCast, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt hi
  rw [factorWord, UInt64.toNat_toUInt32, UInt64.toNat_mod, UInt32.toNat_toUInt64, hi64]
  exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hm) m.toNat_lt)

theorem factorial_set_step (m : UInt32) (fac : Array cp.DynamicModInt) (i : Nat)
    (hm : 0 < m.toNat) (hi : 0 < i) (bound : i < fac.size) (hi64 : i < 2^64)
    (hprefix : FactorialPrefix m i fac) :
    FactorialPrefix m (i + 1)
      (set fac (i : Int) ⟨ModIntMath.mulWord32 m fac[i-1]!.x (factorWord m (i : Int))⟩) := by
  intro k hk
  rw [getElemBang_set _ _ _ _ (by simpa using bound)]
  simp only [Int.toNat_natCast]
  by_cases he : k = i
  · subst k
    simp only [ite_true, eq_self]
    rw [ModIntMath.mulWord32_toNat _ _ _ hm, factorWord_value _ _ hm hi64,
      hprefix (i - 1) (by omega), Nat.mul_mod_mod]
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using
      (ModIntFactorial.factorial_step m.toNat (i - 1))
  · simp only [he, ite_false]
    exact hprefix k (by omega)

/-- Extend a preallocated array, starting just beyond its verified prefix.
Each insertion accounts for the loop and construction of the resulting record. -/
def factorialGrowth (m : UInt32) (used limit : Int) (fac : Array cp.DynamicModInt) :
    M (Array cp.DynamicModInt) := do
  let mut values := fac
  for i in range used limit do
    tick
    tick
    values := set values i ⟨ModIntMath.mulWord32 m (get values (i - 1)).x
      (factorWord m i)⟩
  return values

theorem factorial_growth_spec (m : UInt32) (used limit start : Nat)
    (fac : Array cp.DynamicModInt) (hm : 0 < m.toNat) (hu : 0 < used)
    (hul : used ≤ limit) (hlimit : limit ≤ 2^64) (hs : fac.size = limit) (hp : FactorialPrefix m used fac) :
    ⦃fun c => ⌜c = start⌝⦄ factorialGrowth m used limit fac
    ⦃⇓ result c => ⌜result.size = limit ∧ FactorialPrefix m limit result ∧
      c = start + 2 * (limit - used)⌝⦄ := by
  mvcgen [factorialGrowth]
  case inv1 =>
    exact ⇓⟨xs, values⟩ c => ⌜values.size = limit ∧
      FactorialPrefix m (used + xs.prefix.length) values ∧ c = start + 2 * xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  · have hlr := range_prefix_length ‹range _ _ = _ ++ _ :: _›
    have he := range_cursor ‹range _ _ = _ ++ _ :: _›
    subst he
    rename_i pre suffix values clock hstate hlist hupdate
    obtain ⟨hsize, hprefix, hclock⟩ := ‹_ ∧ _ ∧ _›
    have hprev : ((used : Int) + pre.length - 1) = ((used + pre.length - 1 : Nat) : Int) := by omega
    rw [hprev, get_natCast, ← Int.natCast_add]
    refine ⟨hsize, ?_, by omega⟩
    rw [← Nat.add_assoc]
    exact factorial_set_step m values (used + pre.length) hm (by omega) (by omega) (by omega) hprefix
  · exact ⟨hs, hp, ‹_ = start›⟩
  · obtain ⟨hsize, hprefix, hclock⟩ := ‹_ ∧ _ ∧ _›
    have hlen : (range (used : Int) (limit : Int)).length = limit - used := by
      rw [range_length]
      omega
    rw [hlen, Nat.add_sub_of_le hul] at hprefix
    exact ⟨hsize, hprefix, by rw [hlen] at hclock; exact hclock⟩

/-- Factorial query model. The two inverse-cache fields are carried through. -/
def factorialModel (n : Int) (state : DynamicModIntState) :
    M (cp.DynamicModInt × DynamicModIntState) := do
  tick
  check (decide (0 ≤ n))
  let m := state.DynamicModInt_m
  check (decide ((2 : UInt32) ≤ m))
  let mut marker := state.factorial_cached_modulus
  let mut fac := state.factorial_fac
  if decide (marker ≠ m) then
    tick
    tickN 1
    tick
    fac := set (resize fac 1 ⟨0⟩) 0 ⟨1⟩
    marker := m
  let required := n + 1
  let used := size fac
  if decide (required > used) then
    let limit := if decide (required > 100000) then required else 100000
    tick
    tickN limit.toNat
    fac ← factorialGrowth m used limit (resize fac limit ⟨0⟩)
  return (get fac n, { state with factorial_fac := fac, factorial_cached_modulus := marker })

theorem factorial_model_eq (n : Int) (state : DynamicModIntState) :
    cp.factorial n state = factorialModel n state := by
  cases state
  simp only [cp.factorial, factorialModel, factorialGrowth, cp.DynamicModInt.init_0,
    factorWord, ModIntMath.mulWord32, bind_assoc, pure_bind]
  rfl

theorem resize_retains_prefix (fac : Array cp.DynamicModInt)
    (limit : Nat) (h : fac.size < limit) :
    let grown := resize fac (limit : Int) ⟨0⟩
    grown.size = limit ∧ ∀ i, i < fac.size → grown[i]! = fac[i]! := by
  unfold resize
  simp only [Int.toNat_natCast, show ¬limit ≤ fac.size by omega, ite_false, Array.size_append,
    Array.size_replicate]
  refine ⟨by omega, ?_⟩
  intro i hi
  have hbig : i < (fac ++ Array.replicate (limit - fac.size) (⟨0⟩ : cp.DynamicModInt)).size := by
    simp
    omega
  rw [getElem!_pos (fac ++ Array.replicate (limit - fac.size) (⟨0⟩ : cp.DynamicModInt)) i hbig,
    getElem!_pos fac i hi]
  exact Array.getElem_append_left hi

theorem factorial_resize_prefix (m : UInt32) (fac : Array cp.DynamicModInt)
    (limit : Nat) (h : fac.size < limit) (hp : FactorialPrefix m fac.size fac) :
    let grown := resize fac (limit : Int) ⟨0⟩
    grown.size = limit ∧ FactorialPrefix m fac.size grown := by
  obtain ⟨hs, same⟩ := resize_retains_prefix fac limit h
  refine ⟨hs, ?_⟩
  intro i hi
  rw [same i hi]
  exact hp i hi

theorem factorial_reset_prefix (m : UInt32) (fac : Array cp.DynamicModInt)
    (hm : 2 ≤ m.toNat) :
    let reset := set (resize fac 1 ⟨0⟩) 0 ⟨1⟩
    reset.size = 1 ∧ FactorialPrefix m 1 reset := by
  have hs : (resize fac 1 (⟨0⟩ : cp.DynamicModInt)).size = 1 := by
    unfold resize
    have hnat : (1 : Int).toNat = 1 := rfl
    rw [hnat]
    split <;> simp <;> omega
  refine ⟨by rwa [size_set], ?_⟩
  intro i hi
  have he : i = 0 := by omega
  subst i
  rw [getElemBang_set _ _ _ _ (by rw [hs]; decide)]
  change (1 : UInt32).toNat = 1 % m.toNat
  change (1 : Nat) = 1 % m.toNat
  exact (Nat.mod_eq_of_lt (by omega)).symm

@[spec]
theorem factorial_growth_wp (m : UInt32) (used limit : Int) (fac : Array cp.DynamicModInt)
    (Q : PostCond (Array cp.DynamicModInt) PS) :
    ⦃fun start => ⌜0 < m.toNat ∧ 0 < used ∧ used ≤ limit ∧ limit.toNat ≤ 2^64 ∧
      fac.size = limit.toNat ∧ FactorialPrefix m used.toNat fac ∧
      ∀ result, result.size = limit.toNat → FactorialPrefix m limit.toNat result →
        (Q.1 result (start + 2 * (limit.toNat - used.toNat))).down⌝⦄
      factorialGrowth m used limit fac ⦃Q⦄ := by
  apply Triple.iff.mpr
  intro start h
  obtain ⟨hm, hu, hul, hl, hs, hp, next⟩ := h
  have spec := factorial_growth_spec m used.toNat limit.toNat start fac hm (by omega)
    (by omega) hl hs hp
  rw [Int.toNat_of_nonneg (by omega : 0 ≤ used), Int.toNat_of_nonneg (by omega : 0 ≤ limit)] at spec
  obtain ⟨result, clock, run, hsize, hprefix, ht⟩ := run_of_triple spec
  rw [ht] at run
  simp [wp, run]
  exact next result hsize hprefix

/-- A table associated with an older modulus can be discarded. A matching
table must have a nonempty and correct prefix for its current size. -/
def FactorialCacheOK (state : DynamicModIntState) : Prop :=
  state.factorial_cached_modulus = state.DynamicModInt_m →
    0 < state.factorial_fac.size ∧
    FactorialPrefix state.DynamicModInt_m state.factorial_fac.size state.factorial_fac

theorem factorial_spec (n start : Nat) (state : DynamicModIntState)
    (hn : n < 2^31) (hm : (2 : UInt32) ≤ state.DynamicModInt_m)
    (hstate : FactorialCacheOK state) :
    ⦃fun c => ⌜c = start⌝⦄ cp.factorial (n : Int) state
    ⦃⇓ result c => ⌜result.1.x.toNat =
        ModIntFactorial.factorialResidue state.DynamicModInt_m.toNat n ∧
      result.2.DynamicModInt_m = state.DynamicModInt_m ∧ FactorialCacheOK result.2 ∧
      result.2.factorial_cached_modulus = state.DynamicModInt_m ∧
      result.2.factorial_inv_cached_modulus = state.factorial_inv_cached_modulus ∧
      result.2.factorial_inv_fac_inv = state.factorial_inv_fac_inv ∧
      result.2.factorial_fac.size ≤ max state.factorial_fac.size (max 100000 (n + 1)) ∧
      c ≤ start + 5 + 3 * max 100000 (n + 1)⌝⦄ := by
  rw [factorial_model_eq]
  have hm' : 2 ≤ state.DynamicModInt_m.toNat := UInt32.le_iff_toNat_le.mp hm
  obtain ⟨hresetSize, hresetPrefix⟩ := factorial_reset_prefix state.DynamicModInt_m state.factorial_fac hm'
  let limit := max 100000 (n + 1)
  have hlimitEq : (if (100000 : Int) < (n : Int) + 1 then (n : Int) + 1 else 100000) =
      (limit : Int) := by dsimp [limit]; split <;> omega
  have hlimitLower : n + 1 ≤ limit := Nat.le_max_right _ _
  have hlimitUpper : limit ≤ 2^31 := by dsimp [limit]; omega
  mvcgen [factorialModel]
  all_goals simp +zetaDelta [size, FactorialCacheOK, hresetSize, hlimitEq] at *
  all_goals try rw [← show (limit : Int) = max 100000 ((n : Int) + 1) by simp [limit]]
  all_goals try simp only [Int.toNat_natCast]
  · have hr := (factorial_reset_prefix state.DynamicModInt_m state.factorial_fac hm').1
    have hgrow := factorial_resize_prefix state.DynamicModInt_m
      (set (resize state.factorial_fac 1 ⟨0⟩) 0 ⟨1⟩) limit (by rw [hr]; omega)
      (by rwa [hr])
    rw [hr] at hgrow
    refine ⟨by omega, by omega, hgrow.1, hgrow.2, ?_⟩
    intro result hsize hp
    exact ⟨hp n (by omega), ⟨by omega, hsize ▸ hp⟩, by omega, by omega⟩
  · exact ⟨hresetPrefix n (by omega), hresetPrefix, by omega⟩
  · have hmarker := ‹state.factorial_cached_modulus = state.DynamicModInt_m›
    obtain ⟨hused, hp⟩ := hstate hmarker
    have hgrow := factorial_resize_prefix state.DynamicModInt_m state.factorial_fac limit (by omega) hp
    refine ⟨by omega, hused, by omega, by omega, hgrow.1, hgrow.2, ?_⟩
    intro result hsize hp
    simp only [hmarker, true_implies, true_and]
    exact ⟨hp n (by omega), ⟨by omega, hsize ▸ hp⟩, by omega, by omega⟩
  · have hmarker := ‹state.factorial_cached_modulus = state.DynamicModInt_m›
    exact ⟨(hstate hmarker).2 n (by omega), hstate, hmarker, by omega⟩
  · have hlt := UInt32.lt_iff_toNat_lt.mp ‹state.DynamicModInt_m < 2›
    change state.DynamicModInt_m.toNat < 2 at hlt
    omega

/-- When the matching cache already contains the index, the source just
returns the entry in one tick and leaves both caches untouched. -/
theorem factorial_hit_run (n start : Nat) (state : DynamicModIntState)
    (hm : (2 : UInt32) ≤ state.DynamicModInt_m)
    (hmarker : state.factorial_cached_modulus = state.DynamicModInt_m)
    (hn : n < state.factorial_fac.size) :
    (cp.factorial (n : Int) state).run start =
      some ((state.factorial_fac[n]!, state), start + 1) := by
  rw [factorial_model_eq]
  have hsize : ¬size state.factorial_fac < (n : Int) + 1 := by
    unfold size
    omega
  simp [factorialModel, hm, hmarker, hsize, check]
  refine ⟨⟨(), rfl⟩, ?_⟩
  cases state
  simp_all

end Proofs.Cpp.DynamicModint

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.DynamicModint

def InversePrefix (m : UInt32) (used : Nat) (fac : Array cp.DynamicModInt) : Prop :=
  ∀ i, i < used → ModIntFactorial.factorialResidue m.toNat i * fac[i]!.x.toNat % m.toNat = 1

def inverseExponent (m : UInt32) : UInt64 := (m - 2).toUInt64

theorem inverseExponent_value (m : UInt32) (hm : 2 ≤ m.toNat) :
    (inverseExponent m).toNat = m.toNat - 2 := by
  unfold inverseExponent
  rw [UInt32.toNat_toUInt64, UInt32.toNat_sub_of_le _ _
    (UInt32.le_iff_toNat_le.mpr (by simpa using hm))]
  rfl

@[spec]
theorem pow_word_wp (base : UInt32) (e : UInt64) (m : UInt32) (Q : PostCond UInt32 PS) :
    ⦃fun start => ⌜1 ≤ m.toNat ∧ ∀ result,
      result.toNat = base.toNat ^ e.toNat % m.toNat →
      (Q.1 result (start + 2 + bitWidth e.toNat)).down⌝⦄
      cp.dynamic_modint_pow_word base e m ⦃Q⦄ := by
  apply Triple.iff.mpr
  intro start h
  obtain ⟨hm, next⟩ := h
  have hb := m.toNat_lt
  obtain ⟨word, clock, hr, hv, hc⟩ := run_of_triple
    (PowMod.pow_mod_spec base.toUInt64 e m.toUInt64 (by simpa) (by simp; omega) start)
  simp only [UInt32.toNat_toUInt64] at hv
  have hword : word.toNat < m.toNat := hv ▸ Nat.mod_lt _ (by omega)
  have hv' : word.toUInt32.toNat = base.toNat ^ e.toNat % m.toNat := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega), hv]
  have result : (cp.dynamic_modint_pow_word base e m).run start =
      some (word.toUInt32, start + 2 + bitWidth e.toNat) := by
    rw [power_word_eq]
    change Option.bind ((cp.pow_mod base.toUInt64 e m.toUInt64).run start)
      (fun r => some (r.1.toUInt32, r.2)) = _
    rw [hr, Option.bind_some, hc]
  simp [wp, result]
  exact next word.toUInt32 hv'

theorem inverse_set_step (m : UInt32) (fac : Array cp.DynamicModInt) (i : Nat) (inverse : UInt32)
    (hp : Proofs.Fermat.IsPrime m.toNat) (him : i < m.toNat) (hi : 0 < i) (his : i < fac.size)
    (hprev : InversePrefix m i fac) (hinv : inverse.toNat = i ^ (m.toNat - 2) % m.toNat) :
    InversePrefix m (i + 1)
      (set fac (i : Int) ⟨ModIntMath.mulWord32 m fac[i-1]!.x inverse⟩) := by
  intro k hk
  rw [getElemBang_set _ _ _ _ (by simpa using his)]
  simp only [Int.toNat_natCast]
  by_cases he : k = i
  · subst k
    simp only [ite_true, eq_self]
    have hm := hp.1
    rw [ModIntMath.mulWord32_toNat _ _ _ (by omega), hinv]
    have step := DynamicModIntFactorial.inverse_factorial_step
      m.toNat (i - 1) fac[i-1]!.x.toNat hp (by omega) (hprev (i - 1) (by omega))
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ i)] at step
  · simp only [he, ite_false]
    exact hprev k (by omega)

def inverseGrowth (m : UInt32) (used limit : Int) (fac : Array cp.DynamicModInt) :
    M (Array cp.DynamicModInt) := do
  let mut values := fac
  for i in range used limit do
    tick
    let inverse ← cp.dynamic_modint_pow_word (UInt32.ofInt i) (inverseExponent m) m
    tick
    values := set values i ⟨ModIntMath.mulWord32 m (get values (i - 1)).x inverse⟩
  return values

theorem inverse_growth_spec (m : UInt32) (used limit start : Nat)
    (fac : Array cp.DynamicModInt) (hp : Proofs.Fermat.IsPrime m.toNat) (hu : 0 < used)
    (hul : used ≤ limit) (hlimit : limit ≤ m.toNat)
    (hs : fac.size = limit) (hprefix : InversePrefix m used fac) :
    ⦃fun c => ⌜c = start⌝⦄ inverseGrowth m used limit fac
    ⦃⇓ result c => ⌜result.size = limit ∧ InversePrefix m limit result ∧
      c = start + (4 + bitWidth (m.toNat - 2)) * (limit - used)⌝⦄ := by
  mvcgen [inverseGrowth]
  case inv1 =>
    exact ⇓⟨xs, values⟩ c => ⌜values.size = limit ∧
      InversePrefix m (used + xs.prefix.length) values ∧
      c = start + (4 + bitWidth (m.toNat - 2)) * xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  · have hm := hp.1
    refine ⟨by omega, ?_⟩
    intro inverse hinv
    rename_i pre cur suffix hlist values clock hstate
    have hlr := range_prefix_length hlist
    have he := range_cursor hlist
    subst cur
    obtain ⟨hsize, hprefix, hclock⟩ := hstate
    have hprev : ((used : Int) + pre.length - 1) =
        ((used + pre.length - 1 : Nat) : Int) := by omega
    have hi : (UInt32.ofInt ((used : Int) + pre.length)).toNat = used + pre.length := by
      rw [ModIntMath.u32_ofInt_toNat _ (by omega) (by have := m.toNat_lt; omega)]
      omega
    rw [hi, inverseExponent_value _ hm] at hinv
    have e := inverseExponent_value m hm
    change values.size = limit ∧ InversePrefix m (used + (pre.length + 1))
      (set values _ ⟨ModIntMath.mulWord32 m (get values _).x inverse⟩) ∧
      clock + 1 + 2 + bitWidth (inverseExponent m).toNat + 1 =
        start + (4 + bitWidth (m.toNat - 2)) * (pre.length + 1)
    rw [hprev, get_natCast, ← Int.natCast_add, ← Nat.add_assoc, e]
    refine ⟨hsize, inverse_set_step m values _ inverse hp (by omega) (by omega) (by omega) hprefix hinv, ?_⟩
    rw [hclock]
    ring
  · exact ⟨hs, hprefix, ‹_ = start›⟩
  · obtain ⟨hsize, hprefix, hclock⟩ := ‹_ ∧ _ ∧ _›
    have hlen : (range (used : Int) (limit : Int)).length = limit - used := by
      rw [range_length]
      omega
    rw [hlen, Nat.add_sub_of_le hul] at hprefix
    exact ⟨hsize, hprefix, by rwa [hlen] at hclock⟩

def inverseLimit (m : UInt32) (n : Int) : Int :=
  let preferred := if decide (n + 1 > 100000) then n + 1 else 100000
  if decide (preferred < (m.toNat : Int)) then preferred else (m.toNat : Int)

theorem inverse_limit_eq (m : UInt32) (n : Int) :
    inverseLimit m n = min (max 100000 (n + 1)) (m.toNat : Int) := by
  unfold inverseLimit
  have hpreferred : (if decide (n + 1 > 100000) then n + 1 else 100000) =
      max 100000 (n + 1) := by
    simp only [decide_eq_true_eq]
    split <;> omega
  simp only [hpreferred, decide_eq_true_eq]
  split <;> omega

def inverseModel (n : Int) (state : DynamicModIntState) :
    M (cp.DynamicModInt × DynamicModIntState) := do
  tick
  check (decide (0 ≤ n))
  let m := state.DynamicModInt_m
  check (decide ((2 : UInt32) ≤ m))
  check (decide (n < (m.toNat : Int)))
  let mut marker := state.factorial_inv_cached_modulus
  let mut fac := state.factorial_inv_fac_inv
  if decide (marker ≠ m) then
    tick
    tickN 1
    tick
    fac := set (resize fac 1 ⟨0⟩) 0 ⟨1⟩
    marker := m
  let required := n + 1
  let used := size fac
  if decide (required > used) then
    let limit := inverseLimit m n
    tick
    tickN limit.toNat
    fac ← inverseGrowth m used limit (resize fac limit ⟨0⟩)
  return (get fac n, { state with factorial_inv_fac_inv := fac, factorial_inv_cached_modulus := marker })

theorem inverse_model_eq (n : Int) (state : DynamicModIntState) :
    cp.factorial_inv n state = inverseModel n state := by
  cases state
  simp only [cp.factorial_inv, inverseModel, inverseGrowth, inverseLimit, inverseExponent, cp.DynamicModInt.init_0,
    ModIntMath.mulWord32, bind_assoc, pure_bind]
  rfl

theorem inverse_resize_prefix (m : UInt32) (fac : Array cp.DynamicModInt)
    (limit : Nat) (h : fac.size < limit) (hp : InversePrefix m fac.size fac) :
    let grown := resize fac (limit : Int) ⟨0⟩
    grown.size = limit ∧ InversePrefix m fac.size grown := by
  obtain ⟨hs, same⟩ := resize_retains_prefix fac limit h
  refine ⟨hs, ?_⟩
  intro i hi
  rw [same i hi]
  exact hp i hi

theorem inverse_reset_prefix (m : UInt32) (fac : Array cp.DynamicModInt) (hm : 2 ≤ m.toNat) :
    let reset := set (resize fac 1 ⟨0⟩) 0 ⟨1⟩
    reset.size = 1 ∧ InversePrefix m 1 reset := by
  obtain ⟨hs, hp⟩ := factorial_reset_prefix m fac hm
  refine ⟨hs, ?_⟩
  intro i hi
  rw [hp i hi]
  have he : i = 0 := by omega
  subst i
  have hmod : 1 % m.toNat = 1 := Nat.mod_eq_of_lt (by omega)
  simp [ModIntFactorial.factorialResidue, hmod]

@[spec]
theorem inverse_growth_wp (m : UInt32) (used limit : Int) (fac : Array cp.DynamicModInt)
    (Q : PostCond (Array cp.DynamicModInt) PS) :
    ⦃fun start => ⌜Fermat.IsPrime m.toNat ∧ 0 < used ∧ used ≤ limit ∧ limit.toNat ≤ m.toNat ∧
      fac.size = limit.toNat ∧ InversePrefix m used.toNat fac ∧
      ∀ result, result.size = limit.toNat → InversePrefix m limit.toNat result →
        (Q.1 result (start + (4 + bitWidth (m.toNat - 2)) * (limit.toNat - used.toNat))).down⌝⦄
      inverseGrowth m used limit fac ⦃Q⦄ := by
  apply Triple.iff.mpr
  intro start h
  obtain ⟨hp, hu, hul, hl, hs, hpre, next⟩ := h
  have spec := inverse_growth_spec m used.toNat limit.toNat start fac hp (by omega)
    (by omega) hl hs hpre
  rw [Int.toNat_of_nonneg (by omega : 0 ≤ used), Int.toNat_of_nonneg (by omega : 0 ≤ limit)] at spec
  obtain ⟨result, clock, run, hsize, hprefix, ht⟩ := run_of_triple spec
  rw [ht] at run
  simp [wp, run]
  exact next result hsize hprefix

def InverseCacheOK (state : DynamicModIntState) : Prop :=
  state.factorial_inv_cached_modulus = state.DynamicModInt_m →
    0 < state.factorial_inv_fac_inv.size ∧
    InversePrefix state.DynamicModInt_m state.factorial_inv_fac_inv.size state.factorial_inv_fac_inv

theorem inverse_factorial_spec (n start : Nat) (state : DynamicModIntState)
    (hn : n < 2^31) (hnm : n < state.DynamicModInt_m.toNat)
    (hp : Fermat.IsPrime state.DynamicModInt_m.toNat) (hstate : InverseCacheOK state) :
    let m := state.DynamicModInt_m.toNat
    let limit := min (max 100000 (n + 1)) m
    ⦃fun c => ⌜c = start⌝⦄ cp.factorial_inv (n : Int) state
    ⦃⇓ result c => ⌜ModIntFactorial.factorialResidue m n * result.1.x.toNat % m = 1 ∧
      result.2.DynamicModInt_m = state.DynamicModInt_m ∧ InverseCacheOK result.2 ∧
      result.2.factorial_inv_cached_modulus = state.DynamicModInt_m ∧
      result.2.factorial_cached_modulus = state.factorial_cached_modulus ∧
      result.2.factorial_fac = state.factorial_fac ∧
      result.2.factorial_inv_fac_inv.size ≤ max state.factorial_inv_fac_inv.size limit ∧
      c ≤ start + 5 + limit + (4 + bitWidth (m - 2)) * limit⌝⦄ := by
  dsimp only
  rw [inverse_model_eq]
  have hm' := hp.1
  have hm : (2 : UInt32) ≤ state.DynamicModInt_m := UInt32.le_iff_toNat_le.mpr (by simpa using hm')
  obtain ⟨hresetSize, hresetPrefix⟩ := inverse_reset_prefix state.DynamicModInt_m state.factorial_inv_fac_inv hm'
  let limit := min (max 100000 (n + 1)) state.DynamicModInt_m.toNat
  have hlimitEq : inverseLimit state.DynamicModInt_m (n : Int) = (limit : Int) := by
    simp [limit, inverse_limit_eq]
  have hlimitLower : n < limit := (DynamicModIntFactorial.inverse_cache_bound _ _ hnm).1
  have hlimitUpper : limit ≤ state.DynamicModInt_m.toNat := (DynamicModIntFactorial.inverse_cache_bound _ _ hnm).2
  mvcgen [inverseModel]
  all_goals simp +zetaDelta [size, InverseCacheOK, hresetSize, hlimitEq] at *
  all_goals try rw [← show (limit : Int) =
    min (max 100000 ((n : Int) + 1)) (state.DynamicModInt_m.toNat : Int) by simp [limit]]
  all_goals try simp only [Int.toNat_natCast]
  · have hr := (inverse_reset_prefix state.DynamicModInt_m state.factorial_inv_fac_inv hm').1
    have hgrow := inverse_resize_prefix state.DynamicModInt_m
      (set (resize state.factorial_inv_fac_inv 1 ⟨0⟩) 0 ⟨1⟩) limit (by rw [hr]; omega)
      (by rwa [hr])
    rw [hr] at hgrow
    refine ⟨hp, by omega, hgrow.1, hgrow.2, ?_⟩
    intro result hsize hprefix
    have hsteps := Nat.mul_le_mul_left (4 + bitWidth (state.DynamicModInt_m.toNat - 2))
      (Nat.sub_le limit 1)
    refine ⟨hprefix n (by omega), ⟨by omega, hsize ▸ hprefix⟩, by omega, ?_⟩
    dsimp only [limit] at hsteps ⊢
    omega
  · exact ⟨hresetPrefix n (by omega), hresetPrefix, by omega, by omega⟩
  · have hmarker := ‹state.factorial_inv_cached_modulus = state.DynamicModInt_m›
    obtain ⟨hused, hprefix⟩ := hstate hmarker
    have hgrow := inverse_resize_prefix state.DynamicModInt_m state.factorial_inv_fac_inv limit (by omega) hprefix
    refine ⟨hp, hused, by omega, hgrow.1, hgrow.2, ?_⟩
    intro result hsize hprefix
    have hsteps := Nat.mul_le_mul_left (4 + bitWidth (state.DynamicModInt_m.toNat - 2))
      (Nat.sub_le limit state.factorial_inv_fac_inv.size)
    simp only [hmarker, true_implies, true_and]
    refine ⟨hprefix n (by omega), ⟨by omega, hsize ▸ hprefix⟩, by omega, ?_⟩
    dsimp only [limit] at hsteps ⊢
    omega
  · have hmarker := ‹state.factorial_inv_cached_modulus = state.DynamicModInt_m›
    exact ⟨(hstate hmarker).2 n (by omega), hstate, hmarker, by omega⟩
  · exact False.elim (by omega)
  · have hlt := UInt32.lt_iff_toNat_lt.mp ‹state.DynamicModInt_m < 2›
    change state.DynamicModInt_m.toNat < 2 at hlt
    omega

theorem inverse_hit_run (n start : Nat) (state : DynamicModIntState)
    (hm : (2 : UInt32) ≤ state.DynamicModInt_m)
    (hnm : n < state.DynamicModInt_m.toNat)
    (hmarker : state.factorial_inv_cached_modulus = state.DynamicModInt_m)
    (hn : n < state.factorial_inv_fac_inv.size) :
    (cp.factorial_inv (n : Int) state).run start =
      some ((state.factorial_inv_fac_inv[n]!, state), start + 1) := by
  rw [inverse_model_eq]
  have hsize : ¬size state.factorial_inv_fac_inv < (n : Int) + 1 := by
    unfold size
    omega
  simp [inverseModel, hm, hnm, hmarker, hsize, check]
  refine ⟨⟨(), rfl⟩, ?_⟩
  cases state
  simp_all

end Proofs.Cpp.DynamicModint

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.DynamicModint

theorem mul_free_run (state : DynamicModIntState) (a b : cp.DynamicModInt) (start : Nat) :
    (cp.op_mul_DynamicModInt_DynamicModInt a b state).run start =
      some ((⟨ModIntMath.mulWord32 state.DynamicModInt_m a.x b.x⟩, state), start + 2) := by
  cases state
  rfl

/-- The original domain only requires both denominator indices to be below
the prime modulus. The numerator is allowed to reach the modulus. -/
theorem combination_run (state : DynamicModIntState) (n k start : Nat) (hk : k ≤ n)
    (hn : n < 2^31) (hleft : k < state.DynamicModInt_m.toNat)
    (hright : n - k < state.DynamicModInt_m.toNat)
    (hp : Fermat.IsPrime state.DynamicModInt_m.toNat)
    (hfact : FactorialCacheOK state) (hinv : InverseCacheOK state) :
    let p := state.DynamicModInt_m.toNat
    let budget := fun j => let limit := min (max 100000 (j + 1)) p
      5 + limit + (4 + bitWidth (p - 2)) * limit
    ∃ result after finish,
      (cp.dynamic_modint.C (n : Int) (k : Int) state).run start = some ((result, after), finish) ∧
      result.x.toNat = n.choose k % p ∧ after.DynamicModInt_m = state.DynamicModInt_m ∧
      FactorialCacheOK after ∧ InverseCacheOK after ∧
      finish ≤ start + 10 + 3 * max 100000 (n + 1) + budget k + budget (n - k) := by
  dsimp only
  have hm : (2 : UInt32) ≤ state.DynamicModInt_m := UInt32.le_iff_toNat_le.mpr (by simpa using hp.1)
  obtain ⟨⟨numerator, s1⟩, t1, run1, value1, modulus1, fact1, _, invMarker1, invTable1, _, time1⟩ :=
    run_of_triple (factorial_spec n (start + 1) state hn hm hfact)
  have inv1 : InverseCacheOK s1 := by
    unfold InverseCacheOK
    rw [modulus1, invMarker1, invTable1]
    exact hinv
  obtain ⟨⟨left, s2⟩, t2, run2, value2, modulus2, inv2, _, factMarker2, factTable2, _, time2⟩ :=
    run_of_triple (inverse_factorial_spec k t1 s1 (by omega) (by rwa [modulus1]) (by rwa [modulus1]) inv1)
  obtain ⟨⟨right, after⟩, t3, run3, value3, modulus3, inv3, _, factMarker3, factTable3, _, time3⟩ :=
    run_of_triple (inverse_factorial_spec (n - k) t2 s2 (by omega)
      (by rwa [modulus2, modulus1]) (by rwa [modulus2, modulus1]) inv2)
  have modulus := modulus3.trans (modulus2.trans modulus1)
  have fa : FactorialCacheOK after := by
    unfold FactorialCacheOK
    rw [factMarker3, factTable3, factMarker2, factTable2, modulus3, modulus2]
    exact fact1
  let partialProduct : cp.DynamicModInt := ⟨ModIntMath.mulWord32 after.DynamicModInt_m numerator.x left.x⟩
  let result : cp.DynamicModInt := ⟨ModIntMath.mulWord32 after.DynamicModInt_m partialProduct.x right.x⟩
  refine ⟨result, after, t3 + 2 + 2, ?_, ?_, modulus, fa, inv3, ?_⟩
  · rw [combination_eq _ _ _ hk]
    change (do
      let r1 ← (cp.factorial (n : Int) state).run (start + 1)
      let r2 ← (cp.factorial_inv (k : Int) r1.1.2).run r1.2
      let r3 ← (cp.factorial_inv ((n - k : Nat) : Int) r2.1.2).run r2.2
      let product ← (cp.op_mul_DynamicModInt_DynamicModInt r1.1.1 r2.1.1 r3.1.2).run r3.2
      (cp.op_mul_DynamicModInt_DynamicModInt product.1.1 r3.1.1 product.1.2).run product.2) = _
    simp only [Option.bind_eq_bind, run1, Option.bind_some, run2, run3, mul_free_run]
    rfl
  · change (ModIntMath.mulWord32 after.DynamicModInt_m
      (ModIntMath.mulWord32 after.DynamicModInt_m numerator.x left.x) right.x).toNat = _
    have hm' := hp.1
    rw [modulus, ModIntMath.mulWord32_toNat _ _ _ (by omega),
      ModIntMath.mulWord32_toNat _ _ _ (by omega), value1]
    rw [modulus1] at value2
    rw [modulus2, modulus1] at value3
    exact DynamicModIntFactorial.choose_from_caches _ _ _ _ _ hk value2 value3
  · rw [modulus1] at time2
    rw [modulus2, modulus1] at time3
    omega

/-- A query whose three reads hit the caches takes eight ticks and returns
the original state. The result is the product of the three cached words. -/
theorem combination_hit_run (state : DynamicModIntState) (n k start : Nat) (hk : k ≤ n)
    (hm : (2 : UInt32) ≤ state.DynamicModInt_m)
    (hleft : k < state.DynamicModInt_m.toNat) (hright : n - k < state.DynamicModInt_m.toNat)
    (hf : state.factorial_cached_modulus = state.DynamicModInt_m)
    (hi : state.factorial_inv_cached_modulus = state.DynamicModInt_m)
    (hn : n < state.factorial_fac.size)
    (hl : k < state.factorial_inv_fac_inv.size) (hr : n - k < state.factorial_inv_fac_inv.size) :
    let m := state.DynamicModInt_m
    let result : cp.DynamicModInt := ⟨ModIntMath.mulWord32 m
      (ModIntMath.mulWord32 m state.factorial_fac[n]!.x state.factorial_inv_fac_inv[k]!.x)
      state.factorial_inv_fac_inv[n - k]!.x⟩
    (cp.dynamic_modint.C (n : Int) (k : Int) state).run start = some ((result, state), start + 8) := by
  dsimp only
  rw [combination_eq _ _ _ hk]
  change (do
      let r1 ← (cp.factorial (n : Int) state).run (start + 1)
      let r2 ← (cp.factorial_inv (k : Int) r1.1.2).run r1.2
      let r3 ← (cp.factorial_inv ((n - k : Nat) : Int) r2.1.2).run r2.2
      let product ← (cp.op_mul_DynamicModInt_DynamicModInt r1.1.1 r2.1.1 r3.1.2).run r3.2
      (cp.op_mul_DynamicModInt_DynamicModInt product.1.1 r3.1.1 product.1.2).run product.2) = _
  simp only [Option.bind_eq_bind, factorial_hit_run _ _ _ hm hf hn, Option.bind_some,
    inverse_hit_run _ _ _ hm hleft hi hl, inverse_hit_run _ _ _ hm hright hi hr, mul_free_run]

end Proofs.Cpp.DynamicModint

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.DynamicModint

theorem power_word_run (m base : UInt32) (e : UInt64) (hm : 1 ≤ m.toNat) (start : Nat) :
    ∃ result, (cp.dynamic_modint_pow_word base e m).run start =
        some (result, start + 2 + bitWidth e.toNat) ∧
      result.toNat = base.toNat ^ e.toNat % m.toNat ∧ result.toNat < m.toNat := by
  have h : ⦃fun c => ⌜c = start⌝⦄ cp.dynamic_modint_pow_word base e m
      ⦃⇓ r c => ⌜r.toNat = base.toNat ^ e.toNat % m.toNat ∧
        c = start + 2 + bitWidth e.toNat⌝⦄ :=
    Triple.iff.mpr (fun c h => by
      have hc : c = start := h
      subst c
      exact Triple.iff.mp (pow_word_wp base e m _) start ⟨hm, fun _ hv => ⟨hv, rfl⟩⟩)
  obtain ⟨r, c, hr, hv, hc⟩ := run_of_triple h
  exact ⟨r, hc ▸ hr, hv, hv ▸ Nat.mod_lt _ (by omega)⟩

theorem reduced_word_mod (x m : UInt32) (hx : x.toNat < m.toNat) : x % m = x := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_mod, Nat.mod_eq_of_lt hx]

def powerValue (m x : UInt32) (e : UInt64) : M cp.DynamicModInt := do
  tick
  tick
  let word ← cp.dynamic_modint_pow_word x e m
  tick
  return ⟨word % m⟩

def inverseValue (m x : UInt32) : M cp.DynamicModInt := do
  tick
  check (decide (x ≠ 0))
  tick
  let word ← cp.dynamic_modint_pow_word x (inverseExponent m) m
  tick
  return ⟨word % m⟩

theorem inverse_eq (state : DynamicModIntState) (a : cp.DynamicModInt) :
    cp.DynamicModInt.inv a state = (do
      let result ← inverseValue state.DynamicModInt_m a.x
      pure (result, state)) := by
  cases state
  simp only [cp.DynamicModInt.inv, cp.DynamicModInt.init_U, power_helper_eq,
    inverseValue, inverseExponent, bind_assoc, pure_bind]
  rfl

theorem power_eq (state : DynamicModIntState) (a : cp.DynamicModInt) (n : Int) :
    cp.DynamicModInt.pow a n state = (do
      let m := state.DynamicModInt_m
      let result ← if decide (n < 0) then do
        let absPower ← powerValue m a.x (UInt64.ofInt (-(n + 1)) + 1)
        inverseValue m absPower.x
      else powerValue m a.x (UInt64.ofInt n)
      pure (result, state)) := by
  cases state
  by_cases hn : n < 0 <;>
    (simp only [cp.DynamicModInt.pow, hn, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false,
      powerValue, cp.DynamicModInt.init_U, power_helper_eq, inverse_eq, bind_assoc, pure_bind]; rfl)

theorem inverse_value_run (m x : UInt32) (hm : 2 ≤ m.toNat) (hx : x ≠ 0) (start : Nat) :
    ∃ result : cp.DynamicModInt,
      (inverseValue m x).run start = some (result, start + 5 + bitWidth (m.toNat - 2)) ∧
      result.x.toNat = x.toNat ^ (m.toNat - 2) % m.toNat ∧ result.x.toNat < m.toNat := by
  obtain ⟨r, hr, hv, hb⟩ := power_word_run m x (inverseExponent m) (by omega) (start + 1 + 1)
  rw [inverseExponent_value _ hm] at hr hv
  refine ⟨⟨r⟩, ?_, hv, hb⟩
  dsimp only [inverseValue, check]
  rw [show decide (x ≠ 0) = true from decide_eq_true hx]
  simp only [↓reduceIte, pure_bind]
  change Option.bind ((cp.dynamic_modint_pow_word x (inverseExponent m) m).run (start + 1 + 1))
    (fun p => some ((⟨p.1 % m⟩ : cp.DynamicModInt), p.2 + 1)) = _
  rw [hr, Option.bind_some, reduced_word_mod _ _ hb]
  congr 2
  omega

theorem inverse_run (state : DynamicModIntState) (a : cp.DynamicModInt)
    (hm : 2 ≤ state.DynamicModInt_m.toNat) (ha : a.x ≠ 0) (start : Nat) :
    let m := state.DynamicModInt_m.toNat
    ∃ result : cp.DynamicModInt,
      (cp.DynamicModInt.inv a state).run start = some ((result, state), start + 5 + bitWidth (m - 2)) ∧
      result.x.toNat = a.x.toNat ^ (m - 2) % m ∧ result.x.toNat < m := by
  obtain ⟨r, hr, hv, hb⟩ := inverse_value_run state.DynamicModInt_m a.x hm ha start
  refine ⟨r, ?_, hv, hb⟩
  rw [inverse_eq]
  change Option.bind ((inverseValue state.DynamicModInt_m a.x).run start)
    (fun p => some ((p.1, state), p.2)) = _
  rw [hr]
  rfl

theorem inverse_zero_fails (state : DynamicModIntState) (start : Nat) :
    (cp.DynamicModInt.inv (⟨0⟩ : cp.DynamicModInt) state).run start = none := by
  rw [inverse_eq]
  rfl

theorem power_value_run (m x : UInt32) (e : UInt64) (hm : 2 ≤ m.toNat) (start : Nat) :
    ∃ r : cp.DynamicModInt, (powerValue m x e).run start = some (r, start + 5 + bitWidth e.toNat) ∧
      r.x.toNat = x.toNat ^ e.toNat % m.toNat ∧ r.x.toNat < m.toNat := by
  obtain ⟨r, hr, hv, hb⟩ := power_word_run m x e (by omega) (start + 1 + 1)
  refine ⟨⟨r⟩, ?_, hv, hb⟩
  change Option.bind ((cp.dynamic_modint_pow_word x e m).run (start + 1 + 1))
    (fun p => some ((⟨p.1 % m⟩ : cp.DynamicModInt), p.2 + 1)) = _
  rw [hr, Option.bind_some, reduced_word_mod _ _ hb]
  congr 2
  omega

theorem power_nonnegative_run (state : DynamicModIntState) (a : cp.DynamicModInt) (n : Int)
    (hm : 2 ≤ state.DynamicModInt_m.toNat) (hn : 0 ≤ n) (hmax : n ≤ 9223372036854775807)
    (start : Nat) :
    ∃ r : cp.DynamicModInt,
      (cp.DynamicModInt.pow a n state).run start = some ((r, state), start + 5 + bitWidth n.toNat) ∧
      r.x.toNat = a.x.toNat ^ n.toNat % state.DynamicModInt_m.toNat ∧
      r.x.toNat < state.DynamicModInt_m.toNat := by
  have he : (UInt64.ofInt n).toNat = n.toNat := by
    simp only [UInt64.ofInt, UInt64.toNat_ofNat']
    rw [Int.emod_eq_of_lt hn (by omega), Nat.mod_eq_of_lt (by omega)]
  obtain ⟨r, hr, hv, hb⟩ := power_value_run state.DynamicModInt_m a.x (UInt64.ofInt n) hm start
  rw [he] at hr hv
  refine ⟨r, ?_, hv, hb⟩
  rw [power_eq]
  simp only [show ¬ n < 0 by omega, decide_false, Bool.false_eq_true, ite_false]
  change Option.bind ((powerValue state.DynamicModInt_m a.x (UInt64.ofInt n)).run start)
    (fun p => some ((p.1, state), p.2)) = _
  rw [hr]
  rfl

theorem power_negative_run (state : DynamicModIntState) (a : cp.DynamicModInt) (n : Int)
    (hp : Proofs.Fermat.IsPrime state.DynamicModInt_m.toNat)
    (ha : a.x.toNat < state.DynamicModInt_m.toNat) (ha0 : a.x ≠ 0)
    (hn : n < 0) (hmin : -9223372036854775808 ≤ n) (start : Nat) :
    let m := state.DynamicModInt_m.toNat
    ∃ r : cp.DynamicModInt,
      (cp.DynamicModInt.pow a n state).run start =
        some ((r, state), start + 10 + bitWidth n.natAbs + bitWidth (m - 2)) ∧
      r.x.toNat = (a.x.toNat ^ n.natAbs % m) ^ (m - 2) % m ∧ r.x.toNat < m := by
  let magnitude : UInt64 := UInt64.ofInt (-(n + 1)) + 1
  have he : magnitude.toNat = n.natAbs := ModIntMath.negative_magnitude_word n hmin hn
  obtain ⟨p, hrun, hv, _⟩ := power_value_run state.DynamicModInt_m a.x magnitude hp.1 start
  rw [he] at hrun hv
  have haNat : 0 < a.x.toNat := by
    have : a.x.toNat ≠ 0 := fun h => ha0 (UInt32.toNat_inj.mp (by simpa using h))
    omega
  have hpNat : p.x.toNat ≠ 0 := by
    rw [hv]
    exact ModIntMath.power_residue_nonzero _ _ _ hp haNat ha
  have hp0 : p.x ≠ 0 := fun h => hpNat (by rw [h]; rfl)
  obtain ⟨r, hr, hrv, hrb⟩ := inverse_value_run state.DynamicModInt_m p.x hp.1 hp0
    (start + 5 + bitWidth n.natAbs)
  refine ⟨r, ?_, hv ▸ hrv, hrb⟩
  rw [power_eq]
  simp only [hn, decide_true, ite_true]
  change Option.bind ((powerValue state.DynamicModInt_m a.x magnitude).run start)
    (fun p => Option.bind ((inverseValue state.DynamicModInt_m p.1.x).run p.2)
      (fun r => some ((r.1, state), r.2))) = _
  rw [hrun, Option.bind_some, hr, Option.bind_some]
  congr 2
  omega

theorem inverse_correct (state : DynamicModIntState) (a : cp.DynamicModInt)
    (hp : Proofs.Fermat.IsPrime state.DynamicModInt_m.toNat)
    (ha : a.x.toNat < state.DynamicModInt_m.toNat) (ha0 : a.x ≠ 0) (start : Nat) :
    let m := state.DynamicModInt_m.toNat
    ∃ r : cp.DynamicModInt,
      (cp.DynamicModInt.inv a state).run start = some ((r, state), start + 5 + bitWidth (m - 2)) ∧
      r.x.toNat < m ∧ a.x.toNat * r.x.toNat % m = 1 := by
  obtain ⟨r, hr, hv, hb⟩ := inverse_run state a hp.1 ha0 start
  refine ⟨r, hr, hb, ?_⟩
  rw [hv]
  apply ModIntMath.inverse_residue_unit _ _ hp _ ha
  have : a.x.toNat ≠ 0 := fun h => ha0 (UInt32.toNat_inj.mp (by simpa using h))
  omega

theorem division_assign_step (state : DynamicModIntState) (a b i : cp.DynamicModInt)
    (start finish : Nat)
    (hi : (cp.DynamicModInt.inv b state).run (start + 1) = some ((i, state), finish)) :
    let r : cp.DynamicModInt := ⟨ModIntMath.mulWord32 state.DynamicModInt_m a.x i.x⟩
    (cp.DynamicModInt.op_div_assign a b state).run start = some ((r, r, state), finish + 1) := by
  cases a
  cases state
  change Option.bind ((cp.DynamicModInt.inv b _).run (start + 1)) (fun p =>
    Option.bind ((cp.DynamicModInt.op_mul_assign _ p.1.1 p.1.2).run p.2)
      (fun q => some ((q.1.1, q.1.2.1, q.1.2.2), q.2))) = _
  rw [hi, Option.bind_some, mul_run, Option.bind_some]

theorem division_assign_run (state : DynamicModIntState) (a b : cp.DynamicModInt)
    (hm : 2 ≤ state.DynamicModInt_m.toNat) (hb0 : b.x ≠ 0) (start : Nat) :
    let m := state.DynamicModInt_m.toNat
    ∃ r : cp.DynamicModInt,
      (cp.DynamicModInt.op_div_assign a b state).run start =
        some ((r, r, state), start + 7 + bitWidth (m - 2)) ∧
      r.x.toNat = a.x.toNat * (b.x.toNat ^ (m - 2) % m) % m ∧ r.x.toNat < m := by
  obtain ⟨i, hi, hv, _⟩ := inverse_run state b hm hb0 (start + 1)
  refine ⟨⟨ModIntMath.mulWord32 state.DynamicModInt_m a.x i.x⟩, ?_, ?_, ?_⟩
  · have step := division_assign_step state a b i _ _ hi
    rw [show (start + 1 + 5 + bitWidth (state.DynamicModInt_m.toNat - 2)) + 1 =
      start + 7 + bitWidth (state.DynamicModInt_m.toNat - 2) by omega] at step
    exact step
  · rw [ModIntMath.mulWord32_toNat _ _ _ (by omega), hv]
  · rw [ModIntMath.mulWord32_toNat _ _ _ (by omega)]
    exact Nat.mod_lt _ (by omega)

theorem division_run (state : DynamicModIntState) (a b : cp.DynamicModInt)
    (hm : 2 ≤ state.DynamicModInt_m.toNat) (hb0 : b.x ≠ 0) (start : Nat) :
    let m := state.DynamicModInt_m.toNat
    ∃ r : cp.DynamicModInt,
      (cp.op_div_DynamicModInt_DynamicModInt a b state).run start =
        some ((r, state), start + 8 + bitWidth (m - 2)) ∧
      r.x.toNat = a.x.toNat * (b.x.toNat ^ (m - 2) % m) % m ∧ r.x.toNat < m := by
  obtain ⟨r, hr, hv, hb⟩ := division_assign_run state a b hm hb0 (start + 1)
  refine ⟨r, ?_, hv, hb⟩
  cases state
  change Option.bind ((cp.DynamicModInt.op_div_assign a b _).run (start + 1))
    (fun p => some ((p.1.2.1, p.1.2.2), p.2)) = _
  rw [hr]
  rfl

theorem division_correct (state : DynamicModIntState) (a b : cp.DynamicModInt)
    (hp : Proofs.Fermat.IsPrime state.DynamicModInt_m.toNat)
    (ha : a.x.toNat < state.DynamicModInt_m.toNat) (hb : b.x.toNat < state.DynamicModInt_m.toNat)
    (hb0 : b.x ≠ 0) (start : Nat) :
    let m := state.DynamicModInt_m.toNat
    ∃ r : cp.DynamicModInt,
      (cp.op_div_DynamicModInt_DynamicModInt a b state).run start =
        some ((r, state), start + 8 + bitWidth (m - 2)) ∧
      r.x.toNat < m ∧ r.x.toNat * b.x.toNat % m = a.x.toNat := by
  obtain ⟨r, hr, hv, hrb⟩ := division_run state a b hp.1 hb0 start
  refine ⟨r, hr, hrb, ?_⟩
  rw [hv]
  apply ModIntMath.quotient_residue_unit _ _ _ hp ha _ hb
  have : b.x.toNat ≠ 0 := fun h => hb0 (UInt32.toNat_inj.mp (by simpa using h))
  omega

private theorem bitWidth_le_log (n m : Nat) (hnm : n ≤ m) (hm : m ≠ 0) :
    bitWidth n ≤ Nat.log2 m + 1 := by
  calc
    bitWidth n ≤ bitWidth m := bitWidth_mono hnm
    _ = Nat.log2 m + 1 := by simp [bitWidth, hm]

theorem power_correct_and_log_work (state : DynamicModIntState) (a : cp.DynamicModInt) (n : Int)
    (hm : 2 ≤ state.DynamicModInt_m.toNat)
    (hneg : n < 0 → Proofs.Fermat.IsPrime state.DynamicModInt_m.toNat ∧
      a.x.toNat < state.DynamicModInt_m.toNat ∧ a.x ≠ 0)
    (hmin : -9223372036854775808 ≤ n) (hmax : n ≤ 9223372036854775807) (start : Nat) :
    let m := state.DynamicModInt_m.toNat
    ∃ r : cp.DynamicModInt, ∃ finish : Nat,
      (cp.DynamicModInt.pow a n state).run start = some ((r, state), finish) ∧
      r.x.toNat = ModIntMath.signedPowerResidue m a.x.toNat n ∧ r.x.toNat < m ∧
      finish ≤ start + 12 + Nat.log2 (n.natAbs + 1) + (if n < 0 then Nat.log2 m else 0) := by
  by_cases hn : n < 0
  · obtain ⟨hp, ha, ha0⟩ := hneg hn
    obtain ⟨r, hr, hv, hb⟩ := power_negative_run state a n hp ha ha0 hn hmin start
    refine ⟨r, _, hr, ?_, hb, ?_⟩
    · simpa only [ModIntMath.signedPowerResidue, hn, ↓reduceIte] using hv
    · have hexp := bitWidth_le_log n.natAbs (n.natAbs + 1) (by omega) (by omega)
      have hmod := bitWidth_le_log (state.DynamicModInt_m.toNat - 2)
        state.DynamicModInt_m.toNat (by omega) (by omega)
      simp only [hn, ↓reduceIte]
      omega
  · obtain ⟨r, hr, hv, hb⟩ := power_nonnegative_run state a n hm (by omega) hmax start
    refine ⟨r, _, hr, ?_, hb, ?_⟩
    · simpa only [ModIntMath.signedPowerResidue, hn, ↓reduceIte] using hv
    · have hexp := bitWidth_le_log n.toNat (n.natAbs + 1) (by omega) (by omega)
      simp only [hn, ↓reduceIte]
      omega

end Proofs.Cpp.DynamicModint
open Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.DynamicModint

variable (state : DynamicModIntState)

theorem default_ctor_run (start : Nat) :
    cp.DynamicModInt.init_0.run start = some ((⟨0⟩ : cp.DynamicModInt), start + 1) := by
  rfl

theorem get_run (a : cp.DynamicModInt) (start : Nat) :
    (cp.DynamicModInt.get_ a).run start = some (a.x, start + 1) := by
  rfl

theorem unary_plus_run (a : cp.DynamicModInt) (start : Nat) :
    (cp.DynamicModInt.op_add a).run start = some (a, start + 1) := by
  rfl

theorem equal_run (a b : cp.DynamicModInt) (start : Nat) :
    (cp.op_eq_DynamicModInt_DynamicModInt a b).run start =
      some (decide (a.x.toNat = b.x.toNat), start + 1) := by
  simp only [UInt32.toNat_inj]
  rfl

theorem unequal_run (a b : cp.DynamicModInt) (start : Nat) :
    (cp.op_ne_DynamicModInt_DynamicModInt a b).run start =
      some (decide (a.x.toNat ≠ b.x.toNat), start + 1) := by
  change some (decide (a.x ≠ b.x), start + 1) = _
  by_cases h : a.x = b.x
  · simp [h]
  · have hn : a.x.toNat ≠ b.x.toNat := (not_congr UInt32.toNat_inj).mpr h
    simp [h, hn]

section Unsigned
variable {U : Type} [TypeTraits "U" U] [ModToUInt32 "U" U]
  [TemplateConstraint ((TypeTraits.isSigned (tag := "U") (α := U) ||
    TypeTraits.isCvInt128 (tag := "U") (α := U)) = false)]

theorem unsigned_normalize (a : cp.DynamicModInt) (x : U) (start value : Nat)
    (hm : 0 < state.DynamicModInt_m.toNat)
    (hv : (ModToUInt32.apply (tag := "U") x state.DynamicModInt_m).toNat =
      value % state.DynamicModInt_m.toNat) :
    ∃ r : cp.DynamicModInt,
      (cp.DynamicModInt.init_U x state).run start = some ((r, state), start + 1) ∧
      (cp.DynamicModInt.set__U a x state).run start = some ((r, state), start + 1) ∧
      r.x.toNat = value % state.DynamicModInt_m.toNat ∧ r.x.toNat < state.DynamicModInt_m.toNat := by
  cases state
  exact ⟨⟨ModToUInt32.apply (tag := "U") x _⟩, rfl, rfl, hv, hv ▸ Nat.mod_lt _ hm⟩
end Unsigned

theorem signed_value (m : UInt32) (x : Int) (hm : 0 < m.toNat) :
    (UInt32.ofInt (ModIntMath.signedNormalize x m.toNat)).toNat =
      (Int.emod x m.toNat).toNat ∧ (Int.emod x m.toNat).toNat < m.toNat := by
  rw [ModIntMath.signed_normalize_eq x m.toNat (by omega)]
  have hlo := Int.emod_nonneg x (by omega : (m.toNat : Int) ≠ 0)
  have hhi := Int.emod_lt_of_pos x (by omega : (0 : Int) < m.toNat)
  rw [ModIntMath.u32_ofInt_toNat _ hlo (by have := UInt32.toNat_lt m; omega)]
  refine ⟨rfl, ?_⟩
  exact (Int.toNat_lt hlo).mpr hhi

section Signed
local instance : Mod Int := ⟨Int.tmod⟩
variable [TypeTraits "T" Int]
  [TemplateConstraint ((TypeTraits.isSigned (tag := "T") (α := Int) ||
    TypeTraits.isCvInt128 (tag := "T") (α := Int)) = true)]

theorem signed_normalize (a : cp.DynamicModInt) (x : Int) (start : Nat)
    (hm : 0 < state.DynamicModInt_m.toNat) :
    let m := state.DynamicModInt_m.toNat
    ∃ r : cp.DynamicModInt,
      (cp.DynamicModInt.init_T x state).run start = some ((r, state), start + 1) ∧
      (cp.DynamicModInt.set__T a x state).run start = some ((r, state), start + 1) ∧
      r.x.toNat = (Int.emod x m).toNat ∧ r.x.toNat < m := by
  cases state
  obtain ⟨hv, hb⟩ := signed_value _ x hm
  exact ⟨⟨UInt32.ofInt (ModIntMath.signedNormalize x _)⟩, rfl, rfl, hv, hv ▸ hb⟩
end Signed

open ModIntMath in
theorem increment_correct (a : cp.DynamicModInt) (dummy : Int) (start : Nat)
    (ha : a.x.toNat < state.DynamicModInt_m.toNat) :
    let m := state.DynamicModInt_m.toNat
    ∃ r : cp.DynamicModInt,
      (cp.DynamicModInt.op_inc_0 a state).run start = some ((r, r, state), start + 1) ∧
      (cp.DynamicModInt.op_inc_int a dummy state).run start = some ((a, r, state), start + 2) ∧
      r.x.toNat = (a.x.toNat + 1) % m ∧ r.x.toNat < m := by
  cases state
  have hv := incrementWord32_toNat _ _ ha
  exact ⟨⟨incrementWord32 _ a.x⟩, rfl, rfl, hv, hv ▸ Nat.mod_lt _ (by omega)⟩

open ModIntMath in
theorem decrement_correct (a : cp.DynamicModInt) (dummy : Int) (start : Nat)
    (ha : a.x.toNat < state.DynamicModInt_m.toNat) :
    let m := state.DynamicModInt_m.toNat
    ∃ r : cp.DynamicModInt,
      (cp.DynamicModInt.op_dec_0 a state).run start = some ((r, r, state), start + 1) ∧
      (cp.DynamicModInt.op_dec_int a dummy state).run start = some ((a, r, state), start + 2) ∧
      r.x.toNat = (a.x.toNat + m - 1) % m ∧ r.x.toNat < m := by
  cases state
  have hv := decrementWord32_toNat _ _ ha
  exact ⟨⟨decrementWord32 _ a.x⟩, rfl, rfl, hv, hv ▸ Nat.mod_lt _ (by omega)⟩

open ModIntMath in
theorem negate_correct (a : cp.DynamicModInt) (start : Nat)
    (ha : a.x.toNat < state.DynamicModInt_m.toNat) :
    let m := state.DynamicModInt_m.toNat
    ∃ r : cp.DynamicModInt,
      (cp.DynamicModInt.op_sub a state).run start = some ((r, state), start + 2) ∧
      r.x.toNat = (m - a.x.toNat) % m ∧ r.x.toNat < m := by
  cases state
  have hv := negateWord32_toNat _ _ ha
  exact ⟨⟨negateWord32 _ a.x⟩, rfl, hv, hv ▸ Nat.mod_lt _ (by omega)⟩

open ModIntMath in
theorem add_correct (a b : cp.DynamicModInt) (start : Nat)
    (ha : a.x.toNat < state.DynamicModInt_m.toNat) (hb : b.x.toNat < state.DynamicModInt_m.toNat) :
    let m := state.DynamicModInt_m.toNat
    ∃ r : cp.DynamicModInt,
      (cp.DynamicModInt.op_add_assign a b state).run start = some ((r, r, state), start + 1) ∧
      (cp.op_add_DynamicModInt_DynamicModInt a b state).run start = some ((r, state), start + 2) ∧
      r.x.toNat = (a.x.toNat + b.x.toNat) % m ∧ r.x.toNat < m := by
  cases state
  have hv := addWord32_toNat _ _ _ ha hb
  exact ⟨⟨addWord32 _ a.x b.x⟩, rfl, rfl, hv, hv ▸ Nat.mod_lt _ (by omega)⟩

open ModIntMath in
theorem sub_correct (a b : cp.DynamicModInt) (start : Nat)
    (ha : a.x.toNat < state.DynamicModInt_m.toNat) (hb : b.x.toNat < state.DynamicModInt_m.toNat) :
    let m := state.DynamicModInt_m.toNat
    ∃ r : cp.DynamicModInt,
      (cp.DynamicModInt.op_sub_assign a b state).run start = some ((r, r, state), start + 1) ∧
      (cp.op_sub_DynamicModInt_DynamicModInt a b state).run start = some ((r, state), start + 2) ∧
      r.x.toNat = (a.x.toNat + m - b.x.toNat) % m ∧ r.x.toNat < m := by
  cases state
  have hv := subWord32_toNat _ _ _ ha hb
  exact ⟨⟨subWord32 _ a.x b.x⟩, rfl, rfl, hv, hv ▸ Nat.mod_lt _ (by omega)⟩

open ModIntMath in
theorem mul_correct (a b : cp.DynamicModInt) (start : Nat) (hm : 0 < state.DynamicModInt_m.toNat) :
    let m := state.DynamicModInt_m.toNat
    ∃ r : cp.DynamicModInt,
      (cp.DynamicModInt.op_mul_assign a b state).run start = some ((r, r, state), start + 1) ∧
      (cp.op_mul_DynamicModInt_DynamicModInt a b state).run start = some ((r, state), start + 2) ∧
      r.x.toNat = a.x.toNat * b.x.toNat % m ∧ r.x.toNat < m := by
  cases state
  have hv := mulWord32_toNat _ a.x b.x hm
  exact ⟨⟨mulWord32 _ a.x b.x⟩, rfl, rfl, hv, hv ▸ Nat.mod_lt _ hm⟩

section Streams
variable [Streams]

section Input
local instance : Mod Int := ⟨Int.tmod⟩
variable [SourceStreamRead "long" Int]

theorem extract_eq (input : IStream) (a : cp.DynamicModInt) :
    cp.op_shr_istream_DynamicModInt input a state = (do
      tick
      let (raw, after) ← SourceStreamRead.read (source := "long") input (0 : Int)
      tick
      let r : cp.DynamicModInt := ⟨UInt32.ofInt (ModIntMath.signedNormalize raw state.DynamicModInt_m.toNat)⟩
      pure (after, after, r, state)) := by
  cases state
  rfl

theorem extract_correct (input after : IStream) (a : cp.DynamicModInt) (raw : Int)
    (start finish : Nat) (hm : 0 < state.DynamicModInt_m.toNat)
    (hr : (SourceStreamRead.read (source := "long") input (0 : Int)).run (start + 1) =
      some ((raw, after), finish)) :
    let m := state.DynamicModInt_m.toNat
    ∃ r : cp.DynamicModInt,
      (cp.op_shr_istream_DynamicModInt input a state).run start =
        some ((after, after, r, state), finish + 1) ∧
      r.x.toNat = (Int.emod raw m).toNat ∧ r.x.toNat < m := by
  obtain ⟨hv, hb⟩ := signed_value state.DynamicModInt_m raw hm
  refine ⟨⟨UInt32.ofInt (ModIntMath.signedNormalize raw _)⟩, ?_, hv, hv ▸ hb⟩
  rw [extract_eq]
  change Option.bind ((SourceStreamRead.read (source := "long") input (0 : Int)).run (start + 1))
    (fun p => some ((p.1.2, p.1.2,
      (⟨UInt32.ofInt (ModIntMath.signedNormalize p.1.1 _)⟩ : cp.DynamicModInt), state), p.2 + 1)) = _
  rw [hr]
  rfl

theorem extract_nonreturn (input : IStream) (a : cp.DynamicModInt) (start : Nat)
    (hr : (SourceStreamRead.read (source := "long") input (0 : Int)).run (start + 1) = none) :
    (cp.op_shr_istream_DynamicModInt input a state).run start = none := by
  rw [extract_eq]
  change Option.bind ((SourceStreamRead.read (source := "long") input (0 : Int)).run (start + 1)) _ = _
  rw [hr]
  rfl
end Input

section Output
variable [SourceStreamWrite "unsigned_int" UInt32]

theorem insert_eq (output : OStream) (a : cp.DynamicModInt) :
    cp.op_shl_ostream_DynamicModInt output a = (do
      tick
      let after ← SourceStreamWrite.write (source := "unsigned_int") output a.x
      pure (after, after)) := by
  rfl

theorem insert_run (output after : OStream) (a : cp.DynamicModInt) (start finish : Nat)
    (hr : (SourceStreamWrite.write (source := "unsigned_int") output a.x).run (start + 1) =
      some (after, finish)) :
    (cp.op_shl_ostream_DynamicModInt output a).run start = some ((after, after), finish) := by
  rw [insert_eq]
  change Option.bind ((SourceStreamWrite.write (source := "unsigned_int") output a.x).run (start + 1))
    (fun p => some ((p.1, p.1), p.2)) = _
  rw [hr]
  rfl

theorem insert_nonreturn (output : OStream) (a : cp.DynamicModInt) (start : Nat)
    (hr : (SourceStreamWrite.write (source := "unsigned_int") output a.x).run (start + 1) = none) :
    (cp.op_shl_ostream_DynamicModInt output a).run start = none := by
  rw [insert_eq]
  change Option.bind ((SourceStreamWrite.write (source := "unsigned_int") output a.x).run (start + 1)) _ = _
  rw [hr]
  rfl
end Output
end Streams

end Proofs.Cpp.DynamicModint
