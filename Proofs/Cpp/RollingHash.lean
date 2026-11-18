import Proofs.Cpp.Mod61
import Proofs.Cpp.Gen.RollingHash

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Mod61Math Proofs.Cpp.Mod61

namespace Proofs.Cpp.RollingHash

theorem mul61_bounded_spec (a b : UInt64) (ha : a.toNat < 2 ^ 61) (hb : b.toNat < 2 ^ 61) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.mul61 a b ⦃⇓ r c => ⌜r.toNat % M61 = (a.toNat * b.toNat) % M61 ∧ r.toNat < 4 * M61 ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.mul61]
  simp +zetaDelta only at *
  have hau : (a >>> 31).toNat = a.toNat / 2 ^ 31 := shr_toNat a 31 (by omega)
  have had : (a &&& ((1 : UInt64) <<< 31 - 1)).toNat = a.toNat % 2 ^ 31 := and_mask_toNat a 31 (by omega)
  have hbu : (b >>> 31).toNat = b.toNat / 2 ^ 31 := shr_toNat b 31 (by omega)
  have hbd : (b &&& ((1 : UInt64) <<< 31 - 1)).toNat = b.toNat % 2 ^ 31 := and_mask_toNat b 31 (by omega)
  set au := a >>> 31
  set ad := a &&& ((1 : UInt64) <<< 31 - 1)
  set bu := b >>> 31
  set bd := b &&& ((1 : UInt64) <<< 31 - 1)
  have p1 : au.toNat * bu.toNat ≤ (2 ^ 30 - 1) * (2 ^ 30 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have p2 : ad.toNat * bu.toNat ≤ (2 ^ 31 - 1) * (2 ^ 30 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have p3 : au.toNat * bd.toNat ≤ (2 ^ 30 - 1) * (2 ^ 31 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have p4 : ad.toNat * bd.toNat ≤ (2 ^ 31 - 1) * (2 ^ 31 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hmid : (ad * bu + au * bd).toNat = ad.toNat * bu.toNat + au.toNat * bd.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_mul]; simp; omega
  set mid := ad * bu + au * bd
  have hmu : (mid >>> 30).toNat = mid.toNat / 2 ^ 30 := shr_toNat mid 30 (by omega)
  have hmd : (mid &&& ((1 : UInt64) <<< 30 - 1)).toNat = mid.toNat % 2 ^ 30 := and_mask_toNat mid 30 (by omega)
  set midu := mid >>> 30
  set midd := mid &&& ((1 : UInt64) <<< 30 - 1)
  have hsh : (midd <<< 31).toNat = midd.toNat * 2 ^ 31 := by
    rw [UInt64.toNat_shiftLeft]; simp; rw [Nat.shiftLeft_eq]; omega
  obtain ⟨hlt, hcong⟩ := mul61_math a.toNat b.toNat au.toNat ad.toNat bu.toNat bd.toNat mid.toNat midu.toNat midd.toNat
    ha hb hau had hbu hbd hmid hmu hmd
  have hres : (au * bu * (2 : UInt64) + midu + midd <<< (31 : UInt64) + ad * bd).toNat =
      au.toNat * bu.toNat * 2 + midu.toNat + midd.toNat * 2 ^ 31 + ad.toNat * bd.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_mul, UInt64.toNat_mul, hsh]
    simp; omega
  have hshift : midd.toNat * 2^31 ≤ (2^30 - 1) * 2^31 := by
    exact Nat.mul_le_mul_right _ (by have := Nat.mod_lt mid.toNat (by decide : 0 < 2^30); omega)
  constructor
  · rw [hres]
    exact hcong
  · refine ⟨?_, by omega⟩
    rw [hres]
    unfold M61
    have hmidu : midu.toNat < 2^32 := by omega
    omega

end Proofs.Cpp.RollingHash

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Mod61Math Proofs.Cpp.Mod61

namespace Proofs.Cpp.RollingHash

theorem word_of_nonnegative (x : Int) (hx0 : 0 ≤ x) (hx64 : x < 2 ^ 64) :
    (UInt64.ofInt x).toNat = x.toNat := by
  simp only [UInt64.ofInt, UInt64.toNat_ofNat']
  rw [Int.emod_eq_of_lt hx0 hx64, Nat.mod_eq_of_lt (by omega)]

theorem reduce_symbol_run {T : Type} [Conv T Int] (value : T)
    (hlo : -(2^31 : Int) ≤ (Conv.conv value : Int))
    (hhi : (Conv.conv value : Int) < 2^32) (start : Nat) :
    ∃ r, (cp.reduce_symbol value).run start = some (r, start + 1) ∧
      r.toNat = (Int.emod (Conv.conv value) M61).toNat ∧ r.toNat < M61 := by
  let x : Int := Conv.conv value
  have hcast : toSigned 64 cp.rh_in.M61.toNat = (M61 : Int) := by decide
  by_cases hx : x < 0
  · have hnorm0 : 0 ≤ x + M61 := by
      unfold M61
      omega
    have hnormhi : x + M61 < (M61 : Int) := by omega
    have hwide : x + M61 < (2 ^ 64 : Int) := by
      unfold M61
      omega
    refine ⟨UInt64.ofInt (x + M61), ?_, ?_, ?_⟩
    · change some ((if decide (x < 0) then UInt64.ofInt (x + toSigned 64 cp.rh_in.M61.toNat)
        else UInt64.ofInt x), start + 1) = _
      simp only [hx, decide_true, ↓reduceIte, hcast]
    · rw [word_of_nonnegative _ hnorm0 hwide]
      change (x + M61).toNat = (x % M61).toNat
      have he : (x + M61) % (M61 : Int) = x % M61 := by
        rw [Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod]
      rw [← he, Int.emod_eq_of_lt hnorm0 hnormhi]
    · rw [word_of_nonnegative _ hnorm0 hwide]
      exact (Int.toNat_lt hnorm0).mpr hnormhi
  · have hx0 : 0 ≤ x := by omega
    have hxm : x < (M61 : Int) := by
      unfold M61
      omega
    have hwide : x < (2 ^ 64 : Int) := by omega
    refine ⟨UInt64.ofInt x, ?_, ?_, ?_⟩
    · change some ((if decide (x < 0) then UInt64.ofInt (x + toSigned 64 cp.rh_in.M61.toNat)
        else UInt64.ofInt x), start + 1) = _
      simp only [hx, decide_false, Bool.false_eq_true, ↓reduceIte]
    · change (UInt64.ofInt x).toNat = (x % M61).toNat
      rw [word_of_nonnegative _ hx0 hwide, Int.emod_eq_of_lt hx0 hxm]
    · rw [word_of_nonnegative _ hx0 hwide]
      exact (Int.toNat_lt hx0).mpr hxm

theorem append_hash_run {T : Type} [Conv T Int] (a b : UInt64) (digit : T)
    (ha : a.toNat < M61) (hb : b.toNat < M61)
    (hlo : -(2^31 : Int) ≤ (Conv.conv digit : Int))
    (hhi : (Conv.conv digit : Int) < 2^32) (start : Nat) :
    ∃ r, (cp.append_hash a b digit).run start = some (r, start + 4) ∧
      r.toNat = (a.toNat * b.toNat + (Int.emod (Conv.conv digit) M61).toNat) % M61 ∧
      r.toNat < M61 := by
  have ha' : a.toNat < 2^61 := by unfold M61 at ha; omega
  have hb' : b.toNat < 2^61 := by unfold M61 at hb; omega
  obtain ⟨product, t₁, hp, hpmod, hpbound, ht₁⟩ :=
    run_of_triple (mul61_bounded_spec a b ha' hb' (start + 1))
  subst t₁
  obtain ⟨symbol, hs, hsv, hsbound⟩ := reduce_symbol_run digit hlo hhi (start + 1 + 1)
  let sum := product + symbol
  obtain ⟨r, t₂, hr, hv, ht₂⟩ := run_of_triple (mod61_spec sum (start + 1 + 1 + 1))
  subst t₂
  have hsum : sum.toNat = product.toNat + symbol.toNat := by
    rw [show sum = product + symbol from rfl, UInt64.toNat_add, Nat.mod_eq_of_lt]
    unfold M61 at hpbound hsbound
    omega
  have hres : r.toNat = (a.toNat * b.toNat + (Int.emod (Conv.conv digit) M61).toNat) % M61 := by
    rw [hv, hsum, hsv, ← Nat.mod_add_mod, hpmod, Nat.mod_add_mod]
  refine ⟨r, ?_, hres, hres ▸ Nat.mod_lt _ (by decide)⟩
  change Option.bind ((cp.mul61 a b).run (start + 1)) (fun p =>
    Option.bind ((cp.reduce_symbol digit).run p.2) (fun d =>
      (cp.mod61 (p.1 + d.1)).run d.2)) = _
  rw [hp, Option.bind_some, hs, Option.bind_some]
  exact hr

end Proofs.Cpp.RollingHash

namespace Proofs.Cpp.RollingHash

def evaluate (base initial : Nat) (input : List Nat) : Nat :=
  input.foldl (fun acc symbol => acc * base + symbol) initial

def fingerprint (modulus base : Nat) (input : List Nat) : Nat :=
  evaluate base 0 input % modulus

theorem evaluate_add (base initial extra : Nat) (input : List Nat) :
    evaluate base (extra + initial) input =
      extra * base ^ input.length + evaluate base initial input := by
  induction input generalizing initial extra with
  | nil => simp [evaluate]
  | cons symbol remaining ih =>
    simp only [evaluate, List.foldl_cons, List.length_cons] at *
    rw [show (extra + initial) * base + symbol =
      extra * base + (initial * base + symbol) by ring, ih]
    rw [pow_succ', Nat.mul_assoc]

theorem fingerprint_append (modulus base : Nat) (left right : List Nat) :
    fingerprint modulus base (left ++ right) =
      (fingerprint modulus base left * base ^ right.length + fingerprint modulus base right) %
        modulus := by
  unfold fingerprint
  have h := evaluate_add base 0 (evaluate base 0 left) right
  simp only [Nat.add_zero] at h
  rw [show evaluate base 0 (left ++ right) = evaluate base (evaluate base 0 left) right by
    simp only [evaluate, List.foldl_append], h]
  symm
  calc
    _ = (((evaluate base 0 left % modulus * base ^ right.length) % modulus) +
        evaluate base 0 right % modulus) % modulus := (Nat.mod_add_mod _ _ _).symm
    _ = _ := by rw [Nat.mod_mul_mod, Nat.mod_add_mod, Nat.add_mod_mod]

theorem fingerprint_split (modulus base : Nat) (left right : List Nat) (hm : 0 < modulus) :
    let prefixResidue := fingerprint modulus base left * base ^ right.length % modulus
    (fingerprint modulus base (left ++ right) + modulus - prefixResidue) % modulus =
      fingerprint modulus base right := by
  simp only [fingerprint_append]
  rw [← Nat.mod_add_mod (fingerprint modulus base left * base ^ right.length)
    modulus (fingerprint modulus base right)]
  let q := fingerprint modulus base left * base ^ right.length % modulus
  let r := fingerprint modulus base right
  change ((q + r) % modulus + modulus - q) % modulus = r
  have hq : q < modulus := Nat.mod_lt _ hm
  have hr : r < modulus := Nat.mod_lt _ hm
  by_cases h : q + r < modulus
  · rw [Nat.mod_eq_of_lt h, show q + r + modulus - q = r + modulus by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hr]
  · rw [Nat.mod_eq_sub_mod (by omega : modulus ≤ q + r),
      Nat.mod_eq_of_lt (by omega : q + r - modulus < modulus),
      show q + r - modulus + modulus - q = r by omega, Nat.mod_eq_of_lt hr]

theorem fingerprint_interval (modulus base : Nat) (input : List Nat) (l r : Nat)
    (hl : l ≤ r) (hr : r ≤ input.length) (hm : 0 < modulus) :
    let prefixResidue := fingerprint modulus base (input.take l) * base ^ (r - l) % modulus
    (fingerprint modulus base (input.take r) + modulus - prefixResidue) % modulus =
      fingerprint modulus base ((input.take r).drop l) := by
  have hsplit := List.take_append_drop l (input.take r)
  rw [List.take_take, Nat.min_eq_left hl] at hsplit
  have hlen : ((input.take r).drop l).length = r - l := by
    rw [List.length_drop, List.length_take, Nat.min_eq_left hr]
  have hs := fingerprint_split modulus base (input.take l) ((input.take r).drop l) hm
  simpa only [hsplit, hlen] using hs

end Proofs.Cpp.RollingHash

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Mod61Math

namespace Proofs.Cpp.RollingHash

def symbolResidue {T : Type} [Conv T Int] (digit : T) : Nat :=
  (Int.emod (Conv.conv digit) M61).toNat

@[spec] theorem append_hash_wp {T : Type} [Conv T Int] (a b : UInt64) (digit : T)
    (Q : PostCond UInt64 PS) :
    ⦃fun s => ⌜a.toNat < M61 ∧ b.toNat < M61 ∧
      -(2^31 : Int) ≤ (Conv.conv digit : Int) ∧ (Conv.conv digit : Int) < 2^32 ∧
      ∀ r, r.toNat = (a.toNat * b.toNat + symbolResidue digit) % M61 →
        (Q.1 r (s + 4)).down⌝⦄
      cp.append_hash a b digit ⦃Q⦄ := by
  apply Triple.iff.mpr
  intro start h
  obtain ⟨ha, hb, hlo, hhi, hq⟩ := h
  obtain ⟨r, hr, hv, _⟩ := append_hash_run a b digit ha hb hlo hhi start
  simp [wp, hr]
  exact hq r hv

theorem fingerprint_snoc (m b : Nat) (prefixDigits : List Nat) (digit : Nat) :
    fingerprint m b (prefixDigits ++ [digit]) =
      (fingerprint m b prefixDigits * b + digit) % m := by
  have h : fingerprint m b [digit] = digit % m := by simp [fingerprint, evaluate]
  rw [fingerprint_append, h, List.length_singleton, pow_one, Nat.add_mod_mod]

def prefixHash {T : Type} [Conv T Int] (b : Nat) (t : Array T) (n : Nat) : Nat :=
  fingerprint M61 b ((t.toList.map symbolResidue).take n)

theorem prefixHash_succ {T : Type} [Inhabited T] [Conv T Int]
    (b : Nat) (t : Array T) (i : Nat) (h : i < t.size) :
    prefixHash b t (i + 1) = (prefixHash b t i * b + symbolResidue t[i]!) % M61 := by
  unfold prefixHash
  have hi : i < (t.toList.map symbolResidue).length := by simpa using h
  rw [List.take_succ_eq_append_getElem hi, fingerprint_snoc]
  simp [getElem!_pos, h]

theorem simple_hash_all_spec {T : Type} [Inhabited T] [Conv T Int]
    (self : cp.SimpleRollingHash) (t : Array T) (start : Nat)
    (hin : ∀ i, i < t.size → -(2^31 : Int) ≤ (Conv.conv t[i]! : Int) ∧ (Conv.conv t[i]! : Int) < 2^32) :
    ⦃fun c => ⌜c = start⌝⦄ cp.SimpleRollingHash.hash_all self t
    ⦃⇓ r c => ⌜r.toNat = prefixHash cp.SIMPLE_BASE.toNat t t.size ∧ c = start + 1 + 5 * t.size⌝⦄ := by
  mvcgen [cp.SimpleRollingHash.hash_all]
  case inv1 =>
    exact ⇓⟨xs, hash⟩ c => ⌜hash.toNat = prefixHash cp.SIMPLE_BASE.toNat t xs.prefix.length ∧
      c = start + 1 + 5 * xs.prefix.length⌝
  all_goals simp +zetaDelta [size] at *
  · have hc := range_cursor ‹range _ _ = _ ++ _ :: _›
    have hl := range_prefix_length ‹range _ _ = _ ++ _ :: _›
    subst hc
    rename_i pre suffix acc clock hstate hlist
    obtain ⟨hhash, hclock⟩ := ‹_ ∧ _›
    simp only [zero_add, get_natCast]
    have hlt : pre.length < t.size := by simpa +zetaDelta [size] using hl
    obtain ⟨hlo, hhi⟩ := hin _ hlt
    have hm : 0 < M61 := by decide
    refine ⟨?_, by decide, hlo, hhi, ?_⟩
    · rw [hhash]
      exact Nat.mod_lt _ hm
    · intro r hr
      refine ⟨?_, by omega⟩
      rw [prefixHash_succ _ _ _ hlt, ← hhash]
      exact hr
  · exact ⟨by simp [prefixHash, fingerprint, evaluate], by omega⟩
  · assumption

end Proofs.Cpp.RollingHash

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Mod61Math Proofs.Cpp.Mod61

namespace Proofs.Cpp.RollingHash

theorem hash_interval_run (left right power : UInt64) (start : Nat)
    (hl : left.toNat < M61) (hr : right.toNat < M61) (hp : power.toNat < M61) :
    ∃ result, (cp.hash_interval left right power).run start = some (result, start + 3) ∧
      result.toNat = (right.toNat + M61 - (left.toNat * power.toNat) % M61) % M61 := by
  have hword : cp.rh_in.M61.toNat = M61 := by decide
  have hm : 0 < M61 := by decide
  have hleft64 : left.toNat < 2 ^ 61 := Nat.lt_trans hl (by decide)
  have hpower64 : power.toNat < 2 ^ 61 := Nat.lt_trans hp (by decide)
  obtain ⟨raw, t₁, hmul, hresidue, _, ht₁⟩ :=
    run_of_triple (mul61_bounded_spec left power hleft64 hpower64 (start + 1))
  subst t₁
  obtain ⟨product, t₂, hred, hproduct, ht₂⟩ :=
    run_of_triple (mod61_spec raw (start + 1 + 1))
  subst t₂
  have hbounded : product.toNat < M61 := hproduct ▸ Nat.mod_lt _ hm
  have hsum : (right + cp.rh_in.M61).toNat = right.toNat + M61 := by
    rw [UInt64.toNat_add, hword, Nat.mod_eq_of_lt]
    unfold M61 at hr ⊢
    omega
  have hle : product ≤ right + cp.rh_in.M61 := UInt64.le_iff_toNat_le.mpr (by rw [hsum]; omega)
  refine ⟨(right + cp.rh_in.M61 - product) % cp.rh_in.M61, ?_, ?_⟩
  · have hmul' : (cp.rh_in.mul left power).run (start + 1) = some (raw, start + 1 + 1) := hmul
    have hred' : (cp.rh_in.mod raw).run (start + 1 + 1) = some (product, start + 1 + 1 + 1) := hred
    change Option.bind ((cp.rh_in.mul left power).run (start + 1)) (fun p =>
      Option.bind ((cp.rh_in.mod p.1).run p.2) (fun q =>
        some ((right + cp.rh_in.M61 - q.1) % cp.rh_in.M61, q.2))) = _
    rw [hmul', Option.bind_some, hred', Option.bind_some]
  · rw [UInt64.toNat_mod, UInt64.toNat_sub_of_le _ _ hle, hsum, hword, hproduct, hresidue]

theorem simple_interval_run {T : Type} [Conv T Int] (self : cp.SimpleRollingHash) (input : Array T)
    (l r start : Nat) (hl : l ≤ r) (hr : r ≤ input.size)
    (hh : ∀ i, i ≤ input.size →
      self.hash_sum_[i]!.toNat = prefixHash cp.SIMPLE_BASE.toNat input i)
    (hp : ∀ i, i ≤ input.size → self.pows[i]!.toNat = cp.SIMPLE_BASE.toNat ^ i % M61) :
    ∃ result,
      (cp.SimpleRollingHash.hash_int_int self (l : Int) (r : Int)).run start =
        some (result, start + 4) ∧
      result.toNat = fingerprint M61 cp.SIMPLE_BASE.toNat
        (((input.toList.map symbolResidue).take r).drop l) := by
  have hm : 0 < M61 := by decide
  have hl' := hh l (Nat.le_trans hl hr)
  have hr' := hh r hr
  have hp' := hp (r - l) (Nat.le_trans (Nat.sub_le _ _) hr)
  have hlBound : self.hash_sum_[l]!.toNat < M61 := hl' ▸ Nat.mod_lt _ hm
  have hrBound : self.hash_sum_[r]!.toNat < M61 := hr' ▸ Nat.mod_lt _ hm
  have hpBound : self.pows[r - l]!.toNat < M61 := hp' ▸ Nat.mod_lt _ hm
  obtain ⟨result, hrun, hword⟩ := hash_interval_run self.hash_sum_[l]! self.hash_sum_[r]!
    self.pows[r - l]! (start + 1) hlBound hrBound hpBound
  refine ⟨result, ?_, hword.trans ?_⟩
  · have hsub : (r : Int) - l = ((r - l : Nat) : Int) := (Int.ofNat_sub hl).symm
    simp only [cp.SimpleRollingHash.hash_int_int, StateT.run_bind, hsub,
      get_natCast, show tick.run start = some ((), start + 1) from rfl]
    exact hrun
  · rw [hl', hr', hp', Nat.mul_mod_mod]
    exact fingerprint_interval M61 cp.SIMPLE_BASE.toNat (input.toList.map symbolResidue) l r hl
      (by simpa using hr) hm

end Proofs.Cpp.RollingHash

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Mod61Math Proofs.Cpp.Mod61

namespace Proofs.Cpp.RollingHash

def Fingerprints {T : Type} [Conv T Int] (b offset verified : Nat) (input : Array T)
    (fingerprints : Array UInt64) : Prop :=
  ∀ i, i ≤ verified → fingerprints[offset + i]!.toNat = prefixHash b input i

def Powers (b offset verified : Nat) (powers : Array UInt64) : Prop :=
  ∀ i, i ≤ verified → powers[offset + i]!.toNat = b ^ i % M61

theorem row_set_extends (expected : Nat → Nat) (offset i : Nat) (words : Array UInt64)
    (word : UInt64) (hsize : offset + (i + 1) < words.size)
    (hprefix : ∀ j, j ≤ i → words[offset + j]!.toNat = expected j)
    (hnext : word.toNat = expected (i + 1)) :
    ∀ j, j ≤ i + 1 → (set words ((offset + (i + 1) : Nat) : Int) word)[offset + j]!.toNat =
      expected j := by
  intro j hj
  rw [getElemBang_set _ _ _ _ (by omega)]
  simp only [Int.toNat_natCast]
  by_cases h : j = i + 1
  · subst j
    simpa using hnext
  · simpa [h] using hprefix j (by omega)

theorem fingerprint_row_step {T : Type} [Conv T Int] [Inhabited T]
    (b offset i : Nat) (input : Array T) (words : Array UInt64) (word : UInt64)
    (hi : i < input.size) (hsize : offset + (i + 1) < words.size)
    (old : Fingerprints b offset i input words)
    (hword : word.toNat = (words[offset + i]!.toNat * b + symbolResidue input[i]!) % M61) :
    Fingerprints b offset (i + 1) input (set words ((offset + (i + 1) : Nat) : Int) word) := by
  apply row_set_extends (prefixHash b input) offset i words word hsize old
  rw [hword, old _ (Nat.le_refl _), prefixHash_succ _ _ _ hi]

theorem power_row_step (b offset i : Nat) (words : Array UInt64) (word : UInt64)
    (hsize : offset + (i + 1) < words.size) (old : Powers b offset i words)
    (hword : word.toNat = (words[offset + i]!.toNat * b) % M61) :
    Powers b offset (i + 1) (set words ((offset + (i + 1) : Nat) : Int) word) := by
  apply row_set_extends (fun i => b ^ i % M61) offset i words word hsize old
  rw [hword, old _ (Nat.le_refl _), Nat.mod_mul_mod, pow_succ]

end Proofs.Cpp.RollingHash

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Mod61Math Proofs.Cpp.Mod61

namespace Proofs.Cpp.RollingHash

@[spec] theorem mul_hash_wp (a b : UInt64) (Q : PostCond UInt64 PS) :
    ⦃fun s => ⌜a.toNat < M61 ∧ b.toNat < M61 ∧
      ∀ r, r.toNat % M61 = (a.toNat * b.toNat) % M61 → (Q.1 r (s + 1)).down⌝⦄
      cp.rh_in.mul a b ⦃Q⦄ := by
  apply Triple.iff.mpr
  intro start h
  obtain ⟨ha, hb, next⟩ := h
  have bound : M61 < 2 ^ 61 := by decide
  obtain ⟨r, c, hrun, hr, hc⟩ := run_of_triple
    (mul61_spec a b (ha.trans bound) (hb.trans bound) start)
  have hrun' : (cp.rh_in.mul a b).run start = some (r, c) := hrun
  simp [wp, hrun', hc]
  exact next r hr

@[spec] theorem mod_hash_wp (a : UInt64) (Q : PostCond UInt64 PS) :
    ⦃fun s => ⌜∀ r, r.toNat = a.toNat % M61 → (Q.1 r (s + 1)).down⌝⦄ cp.rh_in.mod a ⦃Q⦄ := by
  apply Triple.iff.mpr
  intro start next
  obtain ⟨r, c, hrun, hr, hc⟩ := run_of_triple (mod61_spec a start)
  have hrun' : (cp.rh_in.mod a).run start = some (r, c) := hrun
  simp [wp, hrun', hc]
  exact next r hr

theorem simple_build_spec {T : Type} [Inhabited T] [Conv T Int]
    (t : Array T) (start : Nat)
    (hin : ∀ i, i < t.size → -(2^31 : Int) ≤ (Conv.conv t[i]! : Int) ∧ (Conv.conv t[i]! : Int) < 2^32) :
    ⦃fun c => ⌜c = start⌝⦄ cp.SimpleRollingHash.build ⟨([] : List UInt64).toArray, ([] : List UInt64).toArray, t.size⟩ t
    ⦃⇓ result c => ⌜result.n_ = t.size ∧ result.hash_sum_.size = t.size + 1 ∧
      result.pows.size = t.size + 1 ∧
      Fingerprints cp.SIMPLE_BASE.toNat 0 t.size t result.hash_sum_ ∧
      Powers cp.SIMPLE_BASE.toNat 0 t.size result.pows ∧ c = start + 3 + 9 * t.size⌝⦄ := by
  mvcgen [cp.SimpleRollingHash.build]
  case inv1 =>
    exact ⇓⟨xs, hashes, powers⟩ c => ⌜hashes.size = t.size + 1 ∧ powers.size = t.size + 1 ∧
      Fingerprints cp.SIMPLE_BASE.toNat 0 xs.prefix.length t hashes ∧
      Powers cp.SIMPLE_BASE.toNat 0 xs.prefix.length powers ∧
      c = start + 1 + 2 * (t.size + 1) + 7 * xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  · have hc := range_cursor ‹range _ _ = _ ++ _ :: _›
    have hbound := range_prefix_length ‹range _ _ = _ ++ _ :: _›
    subst hc
    rename_i pre suffix arrays hashes powers clock hstate hlist
    obtain ⟨hs, hp, hf, hpow, hclock⟩ := ‹_ ∧ _›
    have hlt : pre.length < t.size := by simpa +zetaDelta using hbound
    have hnext : (pre.length : Int) + 1 = ((pre.length + 1 : Nat) : Int) := by omega
    simp only [zero_add, get_natCast, hnext]
    have hm : 0 < M61 := by decide
    have hb : cp.SIMPLE_BASE.toNat < M61 := by decide
    have hhash : arrays.1[pre.length]!.toNat < M61 := by
      rw [show arrays.1[pre.length]!.toNat = prefixHash cp.SIMPLE_BASE.toNat t pre.length from
        by simpa using hf pre.length (Nat.le_refl _)]
      exact Nat.mod_lt _ hm
    have hpower : arrays.2[pre.length]!.toNat < M61 := by
      rw [show arrays.2[pre.length]!.toNat = cp.SIMPLE_BASE.toNat ^ pre.length % M61 from
        by simpa using hpow pre.length (Nat.le_refl _)]
      exact Nat.mod_lt _ hm
    obtain ⟨hlo, hhi⟩ := hin _ hlt
    refine ⟨hhash, hb, hlo, hhi, ?_⟩
    intro r hr
    apply (Triple.iff.mp (mul_hash_wp _ _ _)) _
    refine ⟨hpower, hb, ?_⟩
    intro raw hraw
    apply (Triple.iff.mp (mod_hash_wp _ _)) _
    intro value hvalue
    refine ⟨hs, hp, ?_, ?_, by omega⟩
    · have hsize : 0 + (pre.length + 1) < arrays.1.size := by
        rw [Nat.zero_add, hs]
        exact Nat.add_lt_add_right hlt 1
      have step := fingerprint_row_step cp.SIMPLE_BASE.toNat 0 pre.length t arrays.1 r hlt hsize hf
        (by simpa only [Nat.zero_add] using hr)
      simpa only [Nat.zero_add] using step
    · have hsize : 0 + (pre.length + 1) < arrays.2.size := by
        rw [Nat.zero_add, hp]
        exact Nat.add_lt_add_right hlt 1
      have step := power_row_step cp.SIMPLE_BASE.toNat 0 pre.length arrays.2 value hsize hpow
        (by simpa only [Nat.zero_add] using hvalue.trans hraw)
      simpa only [Nat.zero_add] using step
  · have hzero : resize (([] : List UInt64).toArray : Array UInt64) (↑t.size + 1) 0 =
        Array.replicate (t.size + 1) 0 := by simp [resize]
    rw [hzero]
    refine ⟨by simp, ?_, ?_, by omega⟩
    · intro i hi
      have hi0 : i = 0 := by omega
      subst i
      simp [prefixHash, fingerprint, evaluate]
    · intro i hi
      have hi0 : i = 0 := by omega
      subst i
      rw [getElemBang_set _ _ _ _ (by simp)]
      simp [M61]
  · obtain ⟨hs, hp, hf, hpow, hc⟩ := ‹_ ∧ _›
    exact ⟨hs, hp, hf, hpow, by omega⟩

end Proofs.Cpp.RollingHash

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Mod61Math

namespace Proofs.Cpp.RollingHash

def rollingBases : Array UInt64 :=
  ([131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211] : List UInt64).toArray

theorem base_run (i start : Nat) (hi : i < 16) :
    (cp.base_at (i : Int)).run start = some (rollingBases[i]!, start + 1) := by
  have hindex : (i : Int) < cp.rh_in.SZ_BASE := by
    change (i : Int) < 16
    exact_mod_cast hi
  simp [cp.base_at, Int.natCast_nonneg, hindex, check, tick, get_natCast, cp.rh_in.base, rollingBases]


theorem base_lt (i : Nat) (hi : i < 16) : rollingBases[i]!.toNat < M61 := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def RowRest (first last : Nat) (before after : Array UInt64) : Prop :=
  ∀ p, p < first ∨ last < p → after[p]! = before[p]!

theorem row_rest_set (first last position : Nat) (source current : Array UInt64) (word : UInt64)
    (hp : position < current.size) (hf : first ≤ position) (hl : position ≤ last)
    (rest : RowRest first last source current) :
    RowRest first last source (set current (position : Int) word) := by
  intro p hp'
  rw [getElemBang_set _ _ _ _ (by simpa using hp), Int.toNat_natCast, ite_eq_right (by intro h; omega)]
  exact rest _ hp'

def fillRow {T : Type} [Inhabited T] [Conv T Int]
    (self : cp.MultiRollingHash) (t : Array T) (row : Int) (b : UInt64) : M cp.MultiRollingHash := do
  let mut hashes := self.hash_sum_
  let mut powers := set self.pows row (1 : UInt64)
  for i in range 0 self.n_ do
    tick
    let r ← cp.append_hash (get hashes (row + i)) b (get t i)
    hashes := set hashes (row + i + 1) r
    let raw ← cp.rh_in.mul (get powers (row + i)) b
    let p ← cp.rh_in.mod raw
    powers := set powers (row + i + 1) p
  return ⟨hashes, powers, self.n_, self.strength_⟩

theorem rolling_build_eq {T : Type} [Inhabited T] [Conv T Int]
    (self : cp.MultiRollingHash) (t : Array T) (i : Int) :
    cp.MultiRollingHash.build self t i = (do
      tick
      let b ← cp.base_at i
      fillRow self t (i * (self.n_ + 1)) b) := by
  simp only [cp.MultiRollingHash.build, fillRow, Int.add_zero, bind_assoc]

theorem fill_row_spec {T : Type} [Inhabited T] [Conv T Int]
    (self : cp.MultiRollingHash) (t : Array T) (row start : Nat) (base : UInt64)
    (hbase : base.toNat < M61)
    (hn : self.n_ = t.size)
    (hin : ∀ i, i < t.size → -(2^31 : Int) ≤ (Conv.conv t[i]! : Int) ∧ (Conv.conv t[i]! : Int) < 2^32)
    (hfSize : row + t.size < self.hash_sum_.size)
    (hpSize : row + t.size < self.pows.size)
    (hzero : self.hash_sum_[row]!.toNat = 0) :
    ⦃fun c => ⌜c = start⌝⦄ fillRow self t row base
    ⦃⇓ r c => ⌜r.n_ = self.n_ ∧ r.strength_ = self.strength_ ∧
      r.hash_sum_.size = self.hash_sum_.size ∧ r.pows.size = self.pows.size ∧
      Fingerprints base.toNat row t.size t r.hash_sum_ ∧ Powers base.toNat row t.size r.pows ∧
      RowRest row (row + t.size) self.hash_sum_ r.hash_sum_ ∧
      RowRest row (row + t.size) self.pows r.pows ∧ c = start + 7 * t.size⌝⦄ := by
  mvcgen [fillRow]
  case inv1 =>
    exact ⇓⟨xs, hashes, powers⟩ c => ⌜hashes.size = self.hash_sum_.size ∧ powers.size = self.pows.size ∧
      Fingerprints base.toNat row xs.prefix.length t hashes ∧
      Powers base.toNat row xs.prefix.length powers ∧
      RowRest row (row + t.size) self.hash_sum_ hashes ∧
      RowRest row (row + t.size) self.pows powers ∧
      c = start + 7 * xs.prefix.length⌝
  all_goals simp +zetaDelta [hn]
  · have hc := range_cursor ‹range _ _ = _ ++ _ :: _›
    have hbound := range_prefix_length ‹range _ _ = _ ++ _ :: _›
    subst hc
    rename_i pre suffix arrays hashes powers clock hlist hstate
    simp +zetaDelta at hstate
    obtain ⟨hs, hp, hf, hpow, hfr, hpr, hclock⟩ := hstate
    have hlt : pre.length < t.size := by simpa [hn] using hbound
    have hread : (row : Int) + (pre.length : Int) = ((row + pre.length : Nat) : Int) := by omega
    have hwrite : (row : Int) + (pre.length : Int) + 1 = ((row + (pre.length + 1) : Nat) : Int) := by omega
    simp only [zero_add, hwrite, hread, get_natCast]
    have hm : 0 < M61 := by decide
    have hhash : arrays.1[row + pre.length]!.toNat < M61 := hf _ (Nat.le_refl _) ▸ Nat.mod_lt _ hm
    have hpower : arrays.2[row + pre.length]!.toNat < M61 := hpow _ (Nat.le_refl _) ▸ Nat.mod_lt _ hm
    obtain ⟨hlo, hhi⟩ := hin _ hlt
    refine ⟨hhash, hbase, hlo, hhi, ?_⟩
    intro r hr
    apply (Triple.iff.mp (mul_hash_wp _ _ _)) _
    refine ⟨hpower, hbase, ?_⟩
    intro raw hraw
    apply (Triple.iff.mp (mod_hash_wp _ _)) _
    intro value hvalue
    have hend : row + (pre.length + 1) ≤ row + t.size := Nat.add_le_add_left hlt row
    have hhs : row + (pre.length + 1) < arrays.1.size := hs ▸ Nat.lt_of_le_of_lt hend hfSize
    have hps : row + (pre.length + 1) < arrays.2.size := hp ▸ Nat.lt_of_le_of_lt hend hpSize
    have hstart : row ≤ row + (pre.length + 1) := Nat.le_add_right _ _
    exact ⟨hs, hp, fingerprint_row_step _ _ _ _ _ _ hlt hhs hf hr,
      power_row_step _ _ _ _ _ hps hpow (hvalue.trans hraw),
      row_rest_set _ _ _ _ _ _ hhs hstart hend hfr,
      row_rest_set _ _ _ _ _ _ hps hstart hend hpr, by omega⟩
  · have hp : row < self.pows.size := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hpSize
    refine ⟨?_, ?_, fun _ _ => rfl, row_rest_set _ _ _ _ _ _ hp (Nat.le_refl row) (Nat.le_add_right _ _) (fun _ _ => rfl), ‹_ = start›⟩
    · intro i hi
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
      subst i
      simpa [prefixHash, fingerprint, evaluate] using hzero
    · intro i hi
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
      subst i
      rw [Nat.add_zero, getElemBang_set _ _ _ _ (by simpa using hp)]
      simp [M61]
  · rename_i clock hstate
    simpa +zetaDelta [hn] using hstate

theorem rolling_build_row_run {T : Type} [Inhabited T] [Conv T Int]
    (self : cp.MultiRollingHash) (t : Array T) (base start : Nat) (hbase : base < 16)
    (hn : self.n_ = t.size)
    (hin : ∀ i, i < t.size → -(2^31 : Int) ≤ (Conv.conv t[i]! : Int) ∧ (Conv.conv t[i]! : Int) < 2^32)
    (hfSize : base * (t.size + 1) + t.size < self.hash_sum_.size)
    (hpSize : base * (t.size + 1) + t.size < self.pows.size)
    (hzero : self.hash_sum_[base * (t.size + 1)]!.toNat = 0) :
    let row := base * (t.size + 1)
    let b := rollingBases[base]!.toNat
    ∃ r, (cp.MultiRollingHash.build self t (base : Int)).run start = some (r, start + 2 + 7 * t.size) ∧
      r.n_ = self.n_ ∧ r.strength_ = self.strength_ ∧
      r.hash_sum_.size = self.hash_sum_.size ∧ r.pows.size = self.pows.size ∧
      Fingerprints b row t.size t r.hash_sum_ ∧ Powers b row t.size r.pows ∧
      RowRest row (row + t.size) self.hash_sum_ r.hash_sum_ ∧
      RowRest row (row + t.size) self.pows r.pows := by
  let row := base * (t.size + 1)
  have hrow : (base : Int) * (self.n_ + 1) = (row : Int) := by
    rw [hn]
    simp [row, Nat.cast_mul, Nat.cast_add]
  obtain ⟨r, clock, hrun, hsz, hstrength, hf, hp, htable, hpow, hfr, hpr, hclock⟩ :=
    run_of_triple (fill_row_spec self t row (start + 2) rollingBases[base]! (base_lt _ hbase)
      hn hin hfSize hpSize hzero)
  subst clock
  refine ⟨r, ?_, hsz, hstrength, hf, hp, htable, hpow, hfr, hpr⟩
  rw [rolling_build_eq]
  change Option.bind ((cp.base_at (base : Int)).run (start + 1)) (fun p =>
    (fillRow self t ((base : Int) * (self.n_ + 1)) p.1).run p.2) = _
  rw [base_run _ _ hbase, Option.bind_some, hrow]
  exact hrun

end Proofs.Cpp.RollingHash

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Mod61Math

namespace Proofs.Cpp.RollingHash

theorem row_end_before {n i j : Nat} (h : i < j) :
    i * (n + 1) + n < j * (n + 1) := by
  calc
    i * (n + 1) + n < (i + 1) * (n + 1) := by rw [Nat.add_mul, Nat.one_mul]; omega
    _ ≤ j * (n + 1) := Nat.mul_le_mul_right _ h

def CorrectRows {T : Type} [Conv T Int] (t : Array T) (done : Nat)
    (hashes powers : Array UInt64) : Prop :=
  ∀ i, i < done →
    Fingerprints rollingBases[i]!.toNat (i * (t.size + 1)) t.size t hashes ∧
    Powers rollingBases[i]!.toNat (i * (t.size + 1)) t.size powers

def UnstartedRows (n done total : Nat) (hashes : Array UInt64) : Prop :=
  ∀ i, done ≤ i → i < total → hashes[i * (n + 1)]!.toNat = 0

theorem extend_correct_rows {T : Type} [Conv T Int] (t : Array T) (done total : Nat)
    (hashes powers nextHashes nextPowers : Array UInt64)
    (old : CorrectRows t done hashes powers)
    (zero : UnstartedRows t.size done total hashes)
    (newHash : Fingerprints rollingBases[done]!.toNat (done * (t.size + 1)) t.size t nextHashes)
    (newPows : Powers rollingBases[done]!.toNat (done * (t.size + 1)) t.size nextPowers)
    (stableHash : RowRest (done * (t.size + 1)) (done * (t.size + 1) + t.size) hashes nextHashes)
    (stablePows : RowRest (done * (t.size + 1)) (done * (t.size + 1) + t.size) powers nextPowers) :
    CorrectRows t (done + 1) nextHashes nextPowers ∧
    UnstartedRows t.size (done + 1) total nextHashes := by
  constructor
  · intro i hi
    by_cases he : i = done
    · subst i
      exact ⟨newHash, newPows⟩
    · have hlt : i < done := by omega
      obtain ⟨hh, hp⟩ := old i hlt
      have hBefore := row_end_before (n := t.size) hlt
      constructor
      · intro k hk
        rw [stableHash _ (Or.inl (Nat.lt_of_le_of_lt (Nat.add_le_add_left hk _) hBefore))]
        exact hh k hk
      · intro k hk
        rw [stablePows _ (Or.inl (Nat.lt_of_le_of_lt (Nat.add_le_add_left hk _) hBefore))]
        exact hp k hk
  · intro i hi hit
    rw [stableHash _ (Or.inr (row_end_before hi))]
    exact zero i (by omega) hit

theorem rolling_build_wp {T : Type} [Inhabited T] [Conv T Int] (self : cp.MultiRollingHash)
    (t : Array T) (i : Nat) (Q : PostCond cp.MultiRollingHash PS) :
    let row := i * (t.size + 1)
    let b := rollingBases[i]!.toNat
    ⦃fun start => ⌜i < 16 ∧ self.n_ = t.size ∧
      (∀ j, j < t.size → -(2^31 : Int) ≤ (Conv.conv t[j]! : Int) ∧ (Conv.conv t[j]! : Int) < 2^32) ∧
      row + t.size < self.hash_sum_.size ∧ row + t.size < self.pows.size ∧ self.hash_sum_[row]!.toNat = 0 ∧
      (∀ r, r.n_ = self.n_ → r.strength_ = self.strength_ →
        r.hash_sum_.size = self.hash_sum_.size → r.pows.size = self.pows.size →
        Fingerprints b row t.size t r.hash_sum_ → Powers b row t.size r.pows →
        RowRest row (row + t.size) self.hash_sum_ r.hash_sum_ →
        RowRest row (row + t.size) self.pows r.pows → (Q.1 r (start + 2 + 7 * t.size)).down)⌝⦄
      cp.MultiRollingHash.build self t (i : Int) ⦃Q⦄ := by
  dsimp only
  apply Triple.iff.mpr
  intro start h
  obtain ⟨hi, hn, hin, hh, hp, hz, next⟩ := h
  obtain ⟨r, hrun, hn', hs', hh', hp', ht, hw, hrt, hrw⟩ :=
    rolling_build_row_run self t i start hi hn hin hh hp hz
  simp [wp, hrun]
  exact next r hn' hs' hh' hp' ht hw hrt hrw

theorem rolling_init_vec_spec {T : Type} [Inhabited T] [Conv T Int]
    (t : Array T) (strength start : Nat) (hStrength : strength ≤ 16)
    (hin : ∀ i, i < t.size → -(2^31 : Int) ≤ (Conv.conv t[i]! : Int) ∧ (Conv.conv t[i]! : Int) < 2^32) :
    let sizeOfTables := strength * (t.size + 1)
    ⦃fun c => ⌜c = start⌝⦄ cp.MultiRollingHash.init_vec_int t (strength : Int)
    ⦃⇓ r c => ⌜r.n_ = t.size ∧ r.strength_ = strength ∧
      r.hash_sum_.size = sizeOfTables ∧ r.pows.size = sizeOfTables ∧
      CorrectRows t strength r.hash_sum_ r.pows ∧
      c = start + 1 + 2 * sizeOfTables + strength * (3 + 7 * t.size)⌝⦄ := by
  have hs : (strength : Int) ≤ cp.rh_in.SZ_BASE := by
    change (strength : Int) ≤ 16
    exact_mod_cast hStrength
  unfold cp.MultiRollingHash.init_vec_int
  simp only [hs, decide_true, check, ite_true, pure_bind,
    not_lt.mpr (Int.natCast_nonneg strength), decide_false, Bool.false_eq_true, ite_false, size]
  let width := strength * (t.size + 1)
  have hwidth : (strength : Int) * ((t.size : Int) + 1) = (width : Int) := by
    simp [width, Nat.cast_mul, Nat.cast_add]
  rw [hwidth]
  mvcgen
  case inv1 =>
    exact ⇓⟨xs, hashes, powers, n, rows⟩ c => ⌜n = t.size ∧ rows = strength ∧
      hashes.size = width ∧ powers.size = width ∧
      CorrectRows t xs.prefix.length hashes powers ∧ UnstartedRows t.size xs.prefix.length strength hashes ∧
      c = start + 1 + 2 * width + xs.prefix.length * (3 + 7 * t.size)⌝
  all_goals simp +zetaDelta at *
  · have hcursor := range_cursor ‹range _ _ = _ ++ _ :: _›
    have hlen := range_prefix_length ‹range _ _ = _ ++ _ :: _›
    subst hcursor
    rename_i pre suffix tables clock hstate hlist
    obtain ⟨hn, hrows, hh, hp, hcorrect, hzero, hclock⟩ := ‹_ ∧ _›
    have hlt : pre.length < strength := by simpa using hlen
    have hb : pre.length < 16 := Nat.lt_of_lt_of_le hlt hStrength
    have hbnd := row_end_before (n := t.size) hlt
    simp only [zero_add]
    apply (Triple.iff.mp (rolling_build_wp _ _ _ _)) _
    refine ⟨hb, hn, hin, hh ▸ hbnd, hp ▸ hbnd, hzero _ (Nat.le_refl _) hlt, ?_⟩
    intro r hnewn hnewrows hnewh hnewp hrowHash hrowPow hstableHash hstablePow
    obtain ⟨hcorrect', hzero'⟩ := extend_correct_rows _ _ _ _ _ _ _
      hcorrect hzero hrowHash hrowPow hstableHash hstablePow
    refine ⟨hnewn.trans hn, hnewrows.trans hrows, hnewh.trans hh, hnewp.trans hp, hcorrect', hzero', ?_⟩
    rw [Nat.add_mul, Nat.one_mul]
    omega
  · have hwidth' : (strength : Int) * ((t.size : Int) + 1) = (width : Int) := by
      simp [width, Nat.cast_mul, Nat.cast_add]
    have hreplicate : resize (([] : List UInt64).toArray : Array UInt64) ((strength : Int) * ((t.size : Int) + 1)) 0 =
        Array.replicate width 0 := by
      rw [hwidth']
      cases width <;> simp [resize]
    have hclockWidth : ((strength : Int) * ((t.size : Int) + 1)).toNat = width := by
      rw [hwidth', Int.toNat_natCast]
    simp only [hreplicate, hclockWidth, Array.size_replicate, width, true_and]
    refine ⟨?_, ?_, by omega⟩
    · intro i hi
      omega
    · intro i _ hi
      have hi' : i * (t.size + 1) < width :=
        Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (row_end_before (n := t.size) hi)
      change (Array.replicate width (0 : UInt64))[i * (t.size + 1)]!.toNat = 0
      have hb : i * (t.size + 1) < (Array.replicate width (0 : UInt64)).size := by
        rw [Array.size_replicate]
        exact hi'
      rw [getElem!_pos (Array.replicate width (0 : UInt64)) (i * (t.size + 1)) hb]
      simp
  · obtain ⟨hn, hrows, hh, hp, hcorrect, _, hclock⟩ := ‹_ ∧ _›
    exact ⟨hn, hrows, hh, hp, hcorrect, hclock⟩

end Proofs.Cpp.RollingHash

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Mod61Math

namespace Proofs.Cpp.RollingHash

def sliceHash {T : Type} [Conv T Int] (b : Nat) (input : Array T) (l r : Nat) : Nat :=
  fingerprint M61 b (((input.toList.map symbolResidue).take r).drop l)

theorem rolling_slice_run {T : Type} [Conv T Int] (self : cp.MultiRollingHash) (t : Array T)
    (strength base l r start : Nat) (hn : self.n_ = t.size) (hr : r ≤ t.size) (hl : l ≤ r)
    (hbase : base < strength) (htables : CorrectRows t strength self.hash_sum_ self.pows) :
    ∃ result, (cp.MultiRollingHash.hash_int_int_int self l r base).run start = some (result, start + 4) ∧
      result.toNat = sliceHash rollingBases[base]!.toNat t l r := by
  let row := base * (t.size + 1)
  let b := rollingBases[base]!.toNat
  have hm : 0 < M61 := by decide
  obtain ⟨hh, hp⟩ := htables base hbase
  have hl' : self.hash_sum_[row + l]!.toNat = prefixHash b t l := hh l (hl.trans hr)
  have hr' : self.hash_sum_[row + r]!.toNat = prefixHash b t r := hh r hr
  have hp' : self.pows[row + (r - l)]!.toNat = b ^ (r - l) % M61 := hp _ (Nat.sub_le r l |>.trans hr)
  obtain ⟨result, hrun, hword⟩ :=
    hash_interval_run self.hash_sum_[row + l]! self.hash_sum_[row + r]! self.pows[row + (r - l)]! (start + 1)
      (hl' ▸ Nat.mod_lt _ hm) (hr' ▸ Nat.mod_lt _ hm) (hp' ▸ Nat.mod_lt _ hm)
  refine ⟨result, ?_, hword.trans ?_⟩
  · have hrow : (base : Int) * (self.n_ + 1) = (row : Int) := by
      rw [hn]
      simp [row, Nat.cast_mul, Nat.cast_add]
    have indexL : (row : Int) + (l : Int) = ((row + l : Nat) : Int) := by omega
    have indexR : (row : Int) + (r : Int) = ((row + r : Nat) : Int) := by omega
    have indexP : ((row + r : Nat) : Int) - (l : Int) = ((row + (r - l) : Nat) : Int) := by omega
    simp only [cp.MultiRollingHash.hash_int_int_int, StateT.run_bind, hrow, indexP, indexL, indexR,
      get_natCast, show tick.run start = some ((), start + 1) from rfl]
    exact hrun
  · rw [hl', hr', hp', Nat.mul_mod_mod]
    exact fingerprint_interval M61 b (t.toList.map symbolResidue) l r hl (by simpa using hr) hm

end Proofs.Cpp.RollingHash

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Mod61Math

namespace Proofs.Cpp.RollingHash

theorem rolling_slice_wp {T : Type} [Conv T Int] (self : cp.MultiRollingHash) (t : Array T)
    (strength base l r : Nat) (Q : PostCond UInt64 PS) :
    ⦃fun c => ⌜self.n_ = t.size ∧ r ≤ t.size ∧ l ≤ r ∧ base < strength ∧
      CorrectRows t strength self.hash_sum_ self.pows ∧
      (∀ value, value.toNat = sliceHash rollingBases[base]!.toNat t l r →
        (Q.1 value (c + 4)).down)⌝⦄
    cp.MultiRollingHash.hash_int_int_int self l r base ⦃Q⦄ := by
  apply Triple.iff.mpr
  intro start h
  obtain ⟨hn, hr, hl, hb, ht, next⟩ := h
  obtain ⟨v, hrun, hv⟩ := rolling_slice_run self t strength base l r start hn hr hl hb ht
  simp [wp, hrun]
  exact next v hv

def SliceHashes {T : Type} [Conv T Int] (t : Array T) (l r k : Nat) (hashes : Array UInt64) : Prop :=
  ∀ i, i < k → hashes[i]!.toNat = sliceHash rollingBases[i]!.toNat t l r

theorem rolling_hash_vec_spec {T : Type} [Conv T Int] (self : cp.MultiRollingHash) (t : Array T)
    (strength l r start : Nat) (hn : self.n_ = t.size) (hs : self.strength_ = strength)
    (hr : r ≤ t.size) (hl : l ≤ r) (ht : CorrectRows t strength self.hash_sum_ self.pows) :
    ⦃fun c => ⌜c = start⌝⦄ cp.MultiRollingHash.hash_int_int self l r
    ⦃⇓ result c => ⌜result.size = strength ∧ SliceHashes t l r strength result ∧
      c = start + 1 + 7 * strength⌝⦄ := by
  have hl' : (l : Int) ≤ r := by exact_mod_cast hl
  have hr' : (r : Int) ≤ self.n_ := by rw [hn]; exact_mod_cast hr
  unfold cp.MultiRollingHash.hash_int_int
  simp only [Int.natCast_nonneg, hl', hr', hs, decide_true, check, ite_true, pure_bind, Int.toNat_natCast]
  mvcgen
  case inv1 =>
    exact ⇓⟨xs, result⟩ c => ⌜result.size = strength ∧ SliceHashes t l r xs.prefix.length result ∧
      c = start + 1 + strength + 5 * xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  · have hcursor := range_cursor ‹range _ _ = _ ++ _ :: _›
    have hlen := range_prefix_length ‹range _ _ = _ ++ _ :: _›
    subst hcursor
    rename_i pre suffix table clock hstate hlist
    obtain ⟨hsize, hprefix, hclock⟩ := ‹_ ∧ _›
    have hi : pre.length < strength := by simpa using hlen
    simp only [zero_add]
    apply (Triple.iff.mp (rolling_slice_wp self t strength pre.length l r _)) _
    refine ⟨?_, hr, hl, hi, ht, ?_⟩
    · assumption
    · intro result hres
      refine ⟨hsize, ?_, by omega⟩
      intro i hilt
      have hpos : (pre.length : Int).toNat < table.size := by
        simpa only [Int.toNat_natCast, hsize] using hi
      rw [getElemBang_set _ _ _ _ hpos, Int.toNat_natCast]
      by_cases hi' : i = pre.length
      · subst i
        simpa using hres
      · simpa [hi'] using hprefix i (by omega)
  · refine ⟨by simp [replicate], ?_, by omega⟩
    intro i hi
    omega
  · obtain ⟨hsize, hprefix, hclock⟩ := ‹_ ∧ _›
    exact ⟨hsize, hprefix, by omega⟩

end Proofs.Cpp.RollingHash

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Mod61Math

namespace Proofs.Cpp.RollingHash

def sequenceHash {T : Type} [Inhabited T] [Conv T Int] (base : UInt64) (t : Array T) : M UInt64 := do
  let mut acc : UInt64 := 0
  for i in range 0 (size t) do
    tick
    acc ← cp.append_hash acc base (get t i)
  return acc

theorem sequence_hash_spec {T : Type} [Inhabited T] [Conv T Int]
    (base : UInt64) (t : Array T) (start : Nat) (hb : base.toNat < M61)
    (hin : ∀ i, i < t.size → -(2^31 : Int) ≤ (Conv.conv t[i]! : Int) ∧ (Conv.conv t[i]! : Int) < 2^32) :
    ⦃fun c => ⌜c = start⌝⦄ sequenceHash base t
    ⦃⇓ r c => ⌜r.toNat = prefixHash base.toNat t t.size ∧ c = start + 5 * t.size⌝⦄ := by
  mvcgen [sequenceHash]
  case inv1 =>
    exact ⇓⟨xs, hash⟩ c => ⌜hash.toNat = prefixHash base.toNat t xs.prefix.length ∧
      c = start + 5 * xs.prefix.length⌝
  all_goals simp +zetaDelta [size] at *
  · have hc := range_cursor ‹range _ _ = _ ++ _ :: _›
    have hl := range_prefix_length ‹range _ _ = _ ++ _ :: _›
    subst hc
    rename_i pre suffix acc clock hstate hlist
    obtain ⟨hhash, hclock⟩ := ‹_ ∧ _›
    simp only [zero_add, get_natCast]
    have hlt : pre.length < t.size := by simpa +zetaDelta [size] using hl
    obtain ⟨hlo, hhi⟩ := hin _ hlt
    have hm : 0 < M61 := by decide
    refine ⟨?_, hb, hlo, hhi, ?_⟩
    · rw [hhash]
      exact Nat.mod_lt _ hm
    · intro r hr
      refine ⟨?_, by omega⟩
      rw [prefixHash_succ _ _ _ hlt, ← hhash]
      exact hr
  · exact ⟨by simp [prefixHash, fingerprint, evaluate], by omega⟩
  · assumption

theorem rolling_hash_all_at_run {T : Type} [Inhabited T] [Conv T Int]
    (self : cp.MultiRollingHash) (t : Array T) (base start : Nat) (hb : base < 16)
    (hin : ∀ i, i < t.size → -(2^31 : Int) ≤ (Conv.conv t[i]! : Int) ∧ (Conv.conv t[i]! : Int) < 2^32) :
    ∃ result, (cp.MultiRollingHash.hash_all_vec_int self t base).run start = some (result, start + 2 + 5 * t.size) ∧
      result.toNat = prefixHash rollingBases[base]!.toNat t t.size := by
  obtain ⟨result, clock, hrun, hv, hc⟩ := run_of_triple
    (sequence_hash_spec rollingBases[base]! t (start + 2) (base_lt _ hb) hin)
  subst clock
  refine ⟨result, ?_, hv⟩
  have sourceEq : cp.MultiRollingHash.hash_all_vec_int self t base = (do
      tick
      let b ← cp.base_at base
      sequenceHash b t) := rfl
  rw [sourceEq]
  change Option.bind ((cp.base_at (base : Int)).run (start + 1)) (fun p =>
    (sequenceHash p.1 t).run p.2) = _
  rw [base_run _ _ hb, Option.bind_some]
  exact hrun

theorem rolling_hash_all_at_wp {T : Type} [Inhabited T] [Conv T Int]
    (self : cp.MultiRollingHash) (t : Array T) (base : Nat) (Q : PostCond UInt64 PS) :
    ⦃fun start => ⌜base < 16 ∧
      (∀ i, i < t.size → -(2^31 : Int) ≤ (Conv.conv t[i]! : Int) ∧ (Conv.conv t[i]! : Int) < 2^32) ∧
      (∀ result, result.toNat = prefixHash rollingBases[base]!.toNat t t.size →
        (Q.1 result (start + 2 + 5 * t.size)).down)⌝⦄ cp.MultiRollingHash.hash_all_vec_int self t base ⦃Q⦄ := by
  apply Triple.iff.mpr
  intro start h
  obtain ⟨hb, hin, next⟩ := h
  obtain ⟨result, hrun, hv⟩ := rolling_hash_all_at_run self t base start hb hin
  simp [wp, hrun]
  exact next result hv

def SequenceHashes {T : Type} [Conv T Int] (t : Array T) (done : Nat) (hashes : Array UInt64) : Prop :=
  ∀ i, i < done → hashes[i]!.toNat = prefixHash rollingBases[i]!.toNat t t.size

theorem rolling_hash_all_vec_spec {T : Type} [Inhabited T] [Conv T Int] (self : cp.MultiRollingHash)
    (t : Array T) (strength start : Nat) (hs : self.strength_ = strength) (hb : strength ≤ 16)
    (hin : ∀ i, i < t.size → -(2^31 : Int) ≤ (Conv.conv t[i]! : Int) ∧ (Conv.conv t[i]! : Int) < 2^32) :
    ⦃fun c => ⌜c = start⌝⦄ cp.MultiRollingHash.hash_all_vec self t
    ⦃⇓ result c => ⌜result.size = strength ∧ SequenceHashes t strength result ∧
      c = start + 1 + 2 * strength + strength * (3 + 5 * t.size)⌝⦄ := by
  unfold cp.MultiRollingHash.hash_all_vec
  simp only [hs, Int.toNat_natCast]
  mvcgen
  case inv1 =>
    exact ⇓⟨xs, hashes⟩ c => ⌜hashes.size = strength ∧ SequenceHashes t xs.prefix.length hashes ∧
      c = start + 1 + strength + xs.prefix.length * (3 + 5 * t.size)⌝
  all_goals simp +zetaDelta at *
  · have hc := range_cursor ‹range _ _ = _ ++ _ :: _›
    have hlen := range_prefix_length ‹range _ _ = _ ++ _ :: _›
    subst hc
    rename_i pre suffix table clock hstate hlist
    obtain ⟨hsize, hprefix, hclock⟩ := ‹_ ∧ _›
    have hi : pre.length < strength := by simpa using hlen
    simp only [zero_add]
    apply (Triple.iff.mp (rolling_hash_all_at_wp _ t pre.length _)) _
    refine ⟨hi.trans_le hb, hin, ?_⟩
    intro result hres
    refine ⟨hsize, ?_, ?_⟩
    · intro j hj
      have hpos : (pre.length : Int).toNat < table.size := by simpa only [Int.toNat_natCast, hsize] using hi
      rw [getElemBang_set _ _ _ _ hpos, Int.toNat_natCast]
      by_cases he : j = pre.length
      · subst j
        simpa using hres
      · simpa [he] using hprefix j (by omega)
    · rw [Nat.add_mul, Nat.one_mul]
      omega
  · refine ⟨by simp [replicate], ?_, by omega⟩
    intro i hi
    omega
  · obtain ⟨hsize, hprefix, hclock⟩ := ‹_ ∧ _›
    exact ⟨hsize, hprefix, by omega⟩

end Proofs.Cpp.RollingHash

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Mod61Math

namespace Proofs.Cpp.RollingHash

def MatchesHashes {T : Type} [Conv T Int] (t : Array T) (l r strength : Nat) (h : Array UInt64) : Prop :=
  ∀ i, i < strength → h[i]!.toNat = sliceHash rollingBases[i]!.toNat t l r

theorem rolling_compare_spec {T : Type} [Conv T Int] (self : cp.MultiRollingHash)
    (t : Array T) (query : Array UInt64) (strength l r start : Nat)
    (hn : self.n_ = t.size) (hs : self.strength_ = strength)
    (hr : r ≤ t.size) (hl : l ≤ r) (ht : CorrectRows t strength self.hash_sum_ self.pows) :
    ⦃fun c => ⌜c = start⌝⦄ cp.MultiRollingHash.match__int_int_vec self l r query
    ⦃⇓ result c => ⌜(result = true ↔ MatchesHashes t l r strength query) ∧
      c ≤ start + 1 + 5 * strength⌝⦄ := by
  unfold cp.MultiRollingHash.match__int_int_vec
  simp only [hs]
  mvcgen
  case inv1 =>
    exact ⇓⟨xs, answer, _⟩ c => ⌜c ≤ start + 1 + 5 * xs.prefix.length ∧
      ((answer = none ∧ MatchesHashes t l r xs.prefix.length query) ∨
        (xs.prefix.length = strength ∧ answer = some false ∧ ¬ MatchesHashes t l r strength query))⌝
  all_goals simp +zetaDelta at *
  · have hcursor := range_cursor ‹range _ _ = _ ++ _ :: _›
    have hlen := range_prefix_length ‹range _ _ = _ ++ _ :: _›
    subst hcursor
    rename_i pre suffix acc clock hstate hlist
    obtain ⟨hclock, hprefix | hdone⟩ := ‹_ ∧ _›
    · obtain ⟨_, hprefix⟩ := hprefix
      have hlt : pre.length < strength := by simpa using hlen
      simp only [zero_add]
      apply (Triple.iff.mp (rolling_slice_wp _ t strength pre.length l r _)) _
      refine ⟨?_, hr, hl, hlt, ht, ?_⟩
      · assumption
      · intro v hv
        simp only [get_natCast]
        by_cases he : v = query[pre.length]!
        · have hnext : MatchesHashes t l r (pre.length + 1) query := by
            intro i hi
            by_cases hi' : i = pre.length
            · subst i
              exact (congrArg UInt64.toNat he).symm.trans hv
            · exact hprefix i (by omega)
          simpa [he] using And.intro
            (show clock + 1 + 4 ≤ start + 1 + 5 * (pre.length + 1) by omega) hnext
        · have hmiss : ¬ MatchesHashes t l r strength query := by
            intro all
            exact he (UInt64.toNat_inj.mp (hv.trans (all _ hlt).symm))
          simpa [he] using And.intro
            (show clock + 1 + 4 ≤ start + 1 + 5 * strength by omega) hmiss
    · have hlt : pre.length < strength := by simpa using hlen
      omega
  · refine ⟨by omega, ?_⟩
    intro i hi
    omega
  · rename_i answer hanswer clock hstate
    obtain ⟨hclock, hresult⟩ := hstate
    refine ⟨?_, hclock⟩
    have h : answer = false ∧ ¬ MatchesHashes t l r strength query := by
      simpa [hanswer] using hresult
    simp [h.1, h.2]
  · rename_i hanswer clock hstate
    obtain ⟨hclock, hresult⟩ := hstate
    exact ⟨by simpa [hanswer] using hresult, hclock⟩

def FingerprintsMatch {S T : Type} [Conv S Int] [Conv T Int]
    (input : Array S) (query : Array T) (l r strength : Nat) : Prop :=
  ∀ i, i < strength → prefixHash rollingBases[i]!.toNat query query.size =
    sliceHash rollingBases[i]!.toNat input l r

theorem compare_matches_fingerprints {S T : Type} [Conv S Int] [Conv T Int]
    (input : Array S) (query : Array T) (l r strength : Nat) (h : Array UInt64)
    (hquery : SequenceHashes query strength h) :
    MatchesHashes input l r strength h ↔ FingerprintsMatch input query l r strength := by
  constructor <;> intro hm i hi
  · exact (hquery i hi).symm.trans (hm i hi)
  · exact (hquery i hi).trans (hm i hi)

end Proofs.Cpp.RollingHash

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.RollingHash

def boundaryMatch {T : Type} [Inhabited T] [Conv T Int] (self : cp.MultiRollingHash)
    (query : Array T) (suffix : Bool) : M Bool := do
  tick
  let n := size query
  if decide (n > self.n_) then return false
  let h ← cp.MultiRollingHash.hash_all_vec self query
  if suffix then cp.MultiRollingHash.match__int_int_vec self (self.n_ - n) self.n_ h
  else cp.MultiRollingHash.match__int_int_vec self 0 n h

theorem starts_with_eq {T : Type} [Inhabited T] [Conv T Int] (self : cp.MultiRollingHash) (query : Array T) :
    cp.MultiRollingHash.starts_with_vector self query = boundaryMatch self query false := by
  cases self
  rfl

theorem ends_with_eq {T : Type} [Inhabited T] [Conv T Int] (self : cp.MultiRollingHash) (query : Array T) :
    cp.MultiRollingHash.ends_with_vector self query = boundaryMatch self query true := by
  cases self
  rfl

theorem boundary_match_run {S T : Type} [Conv S Int] [Inhabited T] [Conv T Int] (self : cp.MultiRollingHash)
    (input : Array S) (query : Array T) (suffix : Bool) (strength start : Nat)
    (hn : self.n_ = input.size) (hs : self.strength_ = strength) (hb : strength ≤ 16)
    (ht : CorrectRows input strength self.hash_sum_ self.pows)
    (hin : ∀ i, i < query.size → -(2^31 : Int) ≤ (Conv.conv query[i]! : Int) ∧ (Conv.conv query[i]! : Int) < 2^32) :
    let r := if suffix then input.size else query.size
    let l := r - query.size
    ∃ answer clock, (boundaryMatch self query suffix).run start = some (answer, clock) ∧
      (answer = true ↔ query.size ≤ input.size ∧ FingerprintsMatch input query l r strength) ∧
      clock ≤ start + 3 + strength * (10 + 5 * query.size) := by
  by_cases hlen : query.size ≤ input.size
  · let r := if suffix then input.size else query.size
    let l := r - query.size
    have hr : r ≤ input.size := by cases suffix <;> simp [r, hlen]
    have hl : l ≤ r := Nat.sub_le _ _
    obtain ⟨h, afterHash, hhash, _, hquery, hcHash⟩ :=
      run_of_triple (rolling_hash_all_vec_spec self query strength (start + 1) hs hb hin)
    obtain ⟨answer, clock, hcompare, hv, hc⟩ :=
      run_of_triple (rolling_compare_spec self input h strength l r afterHash hn hs hr hl ht)
    refine ⟨answer, clock, ?_, ?_, ?_⟩
    · have hsize : ¬size query > self.n_ := by rw [hn, size]; exact Int.not_lt.mpr (by exact_mod_cast hlen)
      simp only [boundaryMatch, hsize, decide_false, Bool.false_eq_true, ite_false]
      change Option.bind ((cp.MultiRollingHash.hash_all_vec self query).run (start + 1)) (fun p =>
        (if suffix then cp.MultiRollingHash.match__int_int_vec self (self.n_ - size query) self.n_ p.1
         else cp.MultiRollingHash.match__int_int_vec self 0 (size query) p.1).run p.2) = _
      rw [hhash, Option.bind_some]
      cases suffix
      · simpa [l, r, size] using hcompare
      · simp only [ite_true, hn, size]
        rw [← Int.ofNat_sub hlen]
        simpa [l, r] using hcompare
    · exact hv.trans ((compare_matches_fingerprints input query l r strength h hquery).trans
        (and_iff_right hlen).symm)
    · calc
        clock ≤ afterHash + 1 + 5 * strength := hc
        _ = start + 3 + strength * (10 + 5 * query.size) := by
          rw [hcHash, show 10 + 5 * query.size = (3 + 5 * query.size) + 7 by omega,
            Nat.mul_add strength (3 + 5 * query.size) 7]
          omega
  · have hsize : size query > self.n_ := by
      rw [hn, size]
      exact_mod_cast Nat.lt_of_not_ge hlen
    refine ⟨false, start + 1, ?_, by simp [hlen], Nat.le_trans (by omega) (Nat.le_add_right _ _)⟩
    simp only [boundaryMatch, hsize, decide_true, ite_true]
    rfl

end Proofs.Cpp.RollingHash
open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.RollingHash

theorem signed_size (input : Array Int) (h : input.size < 2 ^ 31) :
    toSigned 32 (UInt64.ofInt (size input)).toNat = input.size := by
  rw [size, UInt64.ofInt, Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]
  have h64 : input.size < UInt64.size := by
    change input.size < 2 ^ 64
    omega
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt h64]
  rw [toSigned, Nat.mod_eq_of_lt (by omega : input.size < 2 ^ 32)]
  simp only [show input.size < 2 ^ (32 - 1) from h, ↓reduceIte]

theorem signed_size64 (input : Array Int) (h : input.size < 2 ^ 31) :
    toSigned 64 (UInt64.ofInt (size input)).toNat = input.size := by
  rw [size, UInt64.ofInt, Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]
  have h64 : input.size < UInt64.size := by
    change input.size < 2 ^ 64
    omega
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt h64]
  rw [toSigned, Nat.mod_eq_of_lt (by omega : input.size < 2 ^ 64)]
  simp only [show input.size < 2 ^ (64 - 1) by omega, ↓reduceIte]

def CopyPrefix (input output : Array Int) (copied : Nat) : Prop :=
  ∀ i, i < copied → output[i]! = input[i]!

theorem copy_step (input output : Array Int) (i : Nat) (hi : i < output.size)
    (hs : CopyPrefix input output i) :
    CopyPrefix input (set output (i : Int) input[i]!) (i + 1) := by
  intro j hj
  rw [getElemBang_set _ _ _ _ (by simpa using hi)]
  simp only [Int.toNat_natCast]
  by_cases he : j = i
  · subst j
    simp
  · simpa [he] using hs j (by omega)

theorem to_vec_char_spec (input : Array Int) (start : Nat) (h : input.size < 2 ^ 31) :
    ⦃fun c => ⌜c = start⌝⦄ cp.rh_in.to_vec_char input
    ⦃⇓ result c => ⌜result = input ∧ c = start + 1 + 3 * input.size⌝⦄ := by
  unfold cp.rh_in.to_vec_char
  rw [signed_size input h, signed_size64 input h]
  mvcgen
  case inv1 =>
    exact ⇓⟨xs, output⟩ c => ⌜output.size = input.size ∧ CopyPrefix input output xs.prefix.length ∧
      c = start + 1 + input.size + xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  · have hc := range_cursor ‹range _ _ = _ ++ _ :: _›
    have hl := range_prefix_length ‹range _ _ = _ ++ _ :: _›
    subst hc
    obtain ⟨hs, hp, ht⟩ := ‹_ ∧ _ ∧ _›
    simp only [zero_add, get_natCast]
    refine ⟨by simpa using hs, copy_step _ _ _ (by omega) hp, by omega⟩
  · refine ⟨by simp [replicate], ?_, by omega⟩
    intro i hi
    omega
  · obtain ⟨hs, hp, ht⟩ := ‹_ ∧ _ ∧ _›
    refine ⟨?_, by omega⟩
    apply Array.ext hs
    intro i h₁ h₂
    simpa [getElem!_pos, h₁, h₂] using hp i h₂

end Proofs.Cpp.RollingHash

open Std.Do Proofs.Cpp

namespace Proofs.Cpp.RollingHash

def FirstMatch {α : Type} (accepts : α → Prop) (candidates : List α) (result : Option α) : Prop :=
  match result with
  | none => ∀ a, a ∈ candidates → ¬ accepts a
  | some a => ∃ before after, candidates = before ++ a :: after ∧
      accepts a ∧ ∀ x, x ∈ before → ¬ accepts x

def searchCandidates {α β : Type} (test : α → M Bool) (positions : List α)
    (encode : α → β) (missing : β) : M β := do
  for p in positions do
    tick
    if ← test p then return encode p
  return missing

theorem search_candidates_spec {α β : Type} (accepts : α → Prop) (test : α → M Bool)
    (positions : List α) (encode : α → β) (missing : β) (start cost : Nat)
    (step : ∀ seen p suffix, positions = seen ++ p :: suffix →
      FirstMatch accepts seen none → ∀ entry : Nat,
      ⦃fun c => ⌜c = entry⌝⦄ test p
      ⦃⇓ b c => ⌜(b = true ↔ accepts p) ∧ c ≤ entry + cost⌝⦄) :
    ⦃fun c => ⌜c = start⌝⦄ searchCandidates test positions encode missing
    ⦃⇓ value c => ⌜(∃ result, FirstMatch accepts positions result ∧
      value = result.elim missing encode) ∧ c ≤ start + (cost + 1) * positions.length⌝⦄ := by
  mvcgen [searchCandidates]
  case inv1 =>
    exact ⇓⟨xs, answer, _⟩ c => ⌜c ≤ start + (cost + 1) * xs.prefix.length ∧
      ((answer = none ∧ FirstMatch accepts xs.prefix none) ∨
        (xs.prefix.length = positions.length ∧ ∃ p, answer = some (encode p) ∧
          FirstMatch accepts positions (some p)))⌝
  all_goals simp +zetaDelta at *
  case vc1.step =>
    rename_i seen current suffix hpositions carried clock hinvariant
    have hlen : seen.length + 1 ≤ positions.length := by
      rw [hpositions, List.length_append, List.length_cons]
      omega
    have hprefix : FirstMatch accepts seen none := by
      rcases hinvariant.2 with h | h
      · exact h.2
      · omega
    obtain ⟨matched, nextClock, hrun, hresult, hbound⟩ :=
      run_of_triple (step seen current suffix hpositions hprefix (clock + 1))
    have hnext : nextClock ≤ start + (cost + 1) * (seen.length + 1) := by
      rw [Nat.mul_succ]
      have := hinvariant.1
      omega
    cases matched with
    | false =>
      simp [wp, hrun]
      refine ⟨hnext, Or.inl ⟨rfl, ?_⟩⟩
      unfold FirstMatch at hprefix ⊢
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hprefix x hx
      · have heq := List.mem_singleton.mp hx
        subst x
        exact fun h => Bool.false_ne_true (hresult.mpr h)
    | true =>
      simp [wp, hrun]
      exact ⟨hnext.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hlen) _),
        Or.inr ⟨current, rfl, seen, suffix, hpositions, hresult.mp rfl, hprefix⟩⟩
  case vc2.pre =>
    simp_all [FirstMatch]
  case vc3.post.success.h_1 =>
    rename_i carried result hanswer clock hinvariant
    rcases hinvariant with ⟨hclock, h | ⟨p, hp, hfirst⟩⟩
    · simp [hanswer] at h
    · exact ⟨⟨some p, hfirst, Option.some.inj (hanswer.symm.trans hp)⟩, hclock⟩
  case vc4.post.success.h_2 =>
    rename_i carried hanswer clock hinvariant
    rcases hinvariant with ⟨hclock, h | ⟨p, hp, _⟩⟩
    · exact ⟨⟨none, h.2, rfl⟩, hclock⟩
    · simp [hanswer] at hp

end Proofs.Cpp.RollingHash

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.RollingHash

theorem rolling_compare_query_spec {S T : Type} [Conv S Int] [Conv T Int]
    (self : cp.MultiRollingHash) (input : Array S) (query : Array T) (hashes : Array UInt64)
    (strength left start : Nat) (hn : self.n_ = input.size)
    (hs : self.strength_ = strength) (hrange : left + query.size ≤ input.size)
    (hrows : CorrectRows input strength self.hash_sum_ self.pows)
    (hquery : SequenceHashes query strength hashes) :
    ⦃fun c => ⌜c = start⌝⦄
      cp.MultiRollingHash.match__int_int_vec self left ((left + query.size : Nat) : Int) hashes
    ⦃⇓ result c => ⌜(result = true ↔ FingerprintsMatch input query left
      (left + query.size) strength) ∧ c ≤ start + (1 + 5 * strength)⌝⦄ := by
  apply Triple.iff.mpr
  intro c hc
  have hc' : c = start := by simpa using hc
  subst c
  obtain ⟨result, clock, hrun, hresult, htime⟩ := run_of_triple
    (rolling_compare_spec self input hashes strength left (left + query.size) start
      hn hs hrange (Nat.le_add_right _ _) hrows)
  rw [Int.natCast_add] at hrun
  simp [wp, hrun]
  exact ⟨hresult.trans (compare_matches_fingerprints input query left
    (left + query.size) strength hashes hquery), by omega⟩

theorem rolling_match_too_long_run {T : Type} [Inhabited T] [Conv T Int]
    (self : cp.MultiRollingHash) (query : Array T) (start : Nat)
    (h : self.n_ < (query.size : Int)) :
    (cp.MultiRollingHash.match_vector self query).run start = some (cp.RH_NPOS, start + 1) := by
  simp [cp.MultiRollingHash.match_vector, size, tick, h]

theorem rolling_match_custom_too_long_run {T : Type} [Inhabited T] [Conv T Int]
    (self : cp.MultiRollingHash) (query : Array T) (indices : Array Int) (start : Nat)
    (h : self.n_ < (query.size : Int)) :
    (cp.MultiRollingHash.match_custom_vector self query indices).run start =
      some (cp.RH_NPOS, start + 1) := by
  simp [cp.MultiRollingHash.match_custom_vector, size, tick, h]

end Proofs.Cpp.RollingHash

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.RollingHash

theorem rolling_match_vector_run {S T : Type} [Conv S Int] [Inhabited T] [Conv T Int]
    (self : cp.MultiRollingHash) (input : Array S) (query : Array T) (strength start : Nat)
    (hn : self.n_ = input.size) (hs : self.strength_ = strength)
    (hrows : CorrectRows input strength self.hash_sum_ self.pows)
    (hfit : query.size ≤ input.size) (hb : strength ≤ 16)
    (hin : ∀ i, i < query.size →
      -(2^31 : Int) ≤ (Conv.conv query[i]! : Int) ∧ (Conv.conv query[i]! : Int) < 2^32) :
    let positions := range 0 ((input.size : Int) - query.size + 1)
    ∃ answer clock first, (cp.MultiRollingHash.match_vector self query).run start = some (answer, clock) ∧
      FirstMatch (fun i => FingerprintsMatch input query i.toNat (i.toNat + query.size) strength)
        positions first ∧ answer = first.elim cp.RH_NPOS UInt64.ofInt ∧
      clock ≤ start + 2 + 2 * strength + strength * (3 + 5 * query.size) +
        (2 + 5 * strength) * positions.length := by
  let positions := range 0 ((input.size : Int) - query.size + 1)
  let checkAt := fun i : Int => cp.MultiRollingHash.match__int_int_vec self i (i + query.size)
  have elapsed := rolling_hash_all_vec_spec self query strength (start + 1) hs hb hin
  obtain ⟨hashes, afterHash, hhash, _, hseq, htime⟩ := run_of_triple elapsed
  have hcheck : ∀ seen i suffix, positions = seen ++ i :: suffix →
      FirstMatch (fun j => FingerprintsMatch input query j.toNat (j.toNat + query.size) strength)
        seen none → ∀ entry : Nat,
      ⦃fun c => ⌜c = entry⌝⦄ checkAt i hashes
      ⦃⇓ result c => ⌜(result = true ↔ FingerprintsMatch input query i.toNat
          (i.toNat + query.size) strength) ∧ c ≤ entry + (1 + 5 * strength)⌝⦄ := by
    intro seen i suffix hpositions _ entry
    have hi' : i ∈ positions := by simp [hpositions]
    simp [positions, range, List.mem_map] at hi'
    obtain ⟨j, hj, rfl⟩ := hi'
    have hj' : j + query.size ≤ input.size := by omega
    simpa [checkAt] using
      rolling_compare_query_spec self input query hashes strength j entry hn hs hj' hrows hseq
  obtain ⟨answer, clock, hsearch, ⟨first, hfirst, hencode⟩, hbound⟩ :=
    run_of_triple (search_candidates_spec _ (fun i => checkAt i hashes) positions
      UInt64.ofInt cp.RH_NPOS afterHash (1 + 5 * strength) hcheck)
  have heq : cp.MultiRollingHash.match_vector self query = (do
    tick
    let hashes ← cp.MultiRollingHash.hash_all_vec self query
    searchCandidates (fun i => checkAt i hashes) positions UInt64.ofInt cp.RH_NPOS) := by
    cases self
    dsimp at hn
    simp [cp.MultiRollingHash.match_vector, searchCandidates, checkAt, positions, size, hn, Nat.not_lt.mpr hfit]
  refine ⟨answer, clock, first, ?_, hfirst, hencode, ?_⟩
  · rw [heq]
    simp [StateT.run_bind, tick, hhash, hsearch]
  · have hcost : 1 + 5 * strength + 1 = 2 + 5 * strength := by omega
    rw [hcost] at hbound
    dsimp [positions] at hbound
    omega

end Proofs.Cpp.RollingHash

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.RollingHash

theorem rolling_match_custom_vector_run {S T : Type} [Conv S Int] [Inhabited T] [Conv T Int]
    (self : cp.MultiRollingHash) (input : Array S) (query : Array T) (indices : Array Int)
    (strength start : Nat)
    (hn : self.n_ = input.size) (hs : self.strength_ = strength)
    (hrows : CorrectRows input strength self.hash_sum_ self.pows)
    (hfit : query.size ≤ input.size) (hb : strength ≤ 16)
    (hin : ∀ i, i < query.size →
      -(2^31 : Int) ≤ (Conv.conv query[i]! : Int) ∧ (Conv.conv query[i]! : Int) < 2^32) :
    let positions := range 0 (size indices)
    let hit := fun i : Int =>
      let left := (get indices i).toNat
      FingerprintsMatch input query left (left + query.size) strength
    (∀ seen i suffix, positions = seen ++ i :: suffix → FirstMatch hit seen none →
      0 ≤ get indices i ∧ get indices i ≤ (input.size : Int) - query.size) →
    ∃ answer clock first,
      (cp.MultiRollingHash.match_custom_vector self query indices).run start = some (answer, clock) ∧
      FirstMatch hit positions first ∧
      answer = first.elim cp.RH_NPOS (fun i => UInt64.ofInt (get indices i)) ∧
      clock ≤ start + 2 + 2 * strength + strength * (3 + 5 * query.size) +
        (2 + 5 * strength) * indices.size := by
  dsimp only
  intro hvalid
  let positions := range 0 (size indices)
  let hit := fun i : Int =>
    let left := (get indices i).toNat
    FingerprintsMatch input query left (left + query.size) strength
  let checkAt := fun i hashes => do
    check (decide (0 ≤ get indices i))
    check (decide (get indices i ≤ self.n_ - query.size))
    cp.MultiRollingHash.match__int_int_vec self (get indices i) (get indices i + query.size) hashes
  obtain ⟨hashes, afterHash, hhash, _, hseq, htime⟩ := run_of_triple
    (rolling_hash_all_vec_spec self query strength (start + 1) hs hb hin)
  have hcheck : ∀ seen i suffix, positions = seen ++ i :: suffix →
      FirstMatch hit seen none → ∀ entry : Nat,
      ⦃fun c => ⌜c = entry⌝⦄ checkAt i hashes
      ⦃⇓ result c => ⌜(result = true ↔ hit i) ∧ c ≤ entry + (1 + 5 * strength)⌝⦄ := by
    intro seen i suffix hpositions hseen entry
    obtain ⟨hlo, hhi⟩ := hvalid seen i suffix hpositions hseen
    have hhi' : get indices i ≤ self.n_ - query.size := by rwa [hn]
    have hcast : ((get indices i).toNat : Int) = get indices i := Int.toNat_of_nonneg hlo
    have hright : (get indices i).toNat + query.size ≤ input.size := by omega
    simpa [checkAt, check, hlo, hhi', hit, hcast, pure_bind] using
      rolling_compare_query_spec self input query hashes strength
        (get indices i).toNat entry hn hs hright hrows hseq
  obtain ⟨answer, clock, hsearch, ⟨first, hfirst, hencode⟩, hbound⟩ :=
    run_of_triple (search_candidates_spec hit (fun i => checkAt i hashes) positions
      (fun i => UInt64.ofInt (get indices i)) cp.RH_NPOS afterHash (1 + 5 * strength) hcheck)
  have heq : cp.MultiRollingHash.match_custom_vector self query indices = (do
    tick
    let hashes ← cp.MultiRollingHash.hash_all_vec self query
    searchCandidates (fun i => checkAt i hashes) positions
      (fun i => UInt64.ofInt (get indices i)) cp.RH_NPOS) := by
    have hfit' : ¬ self.n_ < (query.size : Int) := by omega
    cases self
    simp [cp.MultiRollingHash.match_custom_vector, searchCandidates, checkAt, positions, size, hfit',
      bind_assoc] <;> rfl
  refine ⟨answer, clock, first, ?_, hfirst, hencode, ?_⟩
  · rw [heq]
    simp [StateT.run_bind, tick, hhash, hsearch]
  · have hcost : 1 + 5 * strength + 1 = 2 + 5 * strength := by omega
    rw [hcost] at hbound
    have hlength : positions.length = indices.size := by simp [positions, size]
    rw [hlength] at hbound
    omega

end Proofs.Cpp.RollingHash

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Mod61Math

namespace Proofs.Cpp.RollingHash

def SimpleFingerprintsMatch {S T : Type} [Conv S Int] [Conv T Int]
    (input : Array S) (query : Array T) (left : Nat) : Prop :=
  sliceHash cp.SIMPLE_BASE.toNat input left (left + query.size) =
    prefixHash cp.SIMPLE_BASE.toNat query query.size

theorem simple_compare_query_spec {S T : Type} [Conv S Int] [Conv T Int]
    (self : cp.SimpleRollingHash) (input : Array S) (query : Array T) (hash : UInt64)
    (left start : Nat) (hrange : left + query.size ≤ input.size)
    (hh : ∀ i, i ≤ input.size → self.hash_sum_[i]!.toNat =
      prefixHash cp.SIMPLE_BASE.toNat input i)
    (hp : ∀ i, i ≤ input.size → self.pows[i]!.toNat = cp.SIMPLE_BASE.toNat ^ i % M61)
    (hquery : hash.toNat = prefixHash cp.SIMPLE_BASE.toNat query query.size) :
    ⦃fun c => ⌜c = start⌝⦄
      (do
        let word ← cp.SimpleRollingHash.hash_int_int self left (left + (query.size : Int))
        return decide (word = hash) : M Bool)
    ⦃⇓ result c => ⌜(result = true ↔ SimpleFingerprintsMatch input query left) ∧
      c = start + 4⌝⦄ := by
  apply Triple.iff.mpr
  intro c hc
  have hc' : c = start := by simpa using hc
  subst c
  obtain ⟨result, hrun, hs⟩ := simple_interval_run self input left (left + query.size) start
    (Nat.le_add_right _ _) hrange hh hp
  rw [Int.natCast_add] at hrun
  change result.toNat = sliceHash cp.SIMPLE_BASE.toNat input left (left + query.size) at hs
  simp [wp, hrun, SimpleFingerprintsMatch, ← hs, ← hquery, UInt64.toNat_inj]
  change (decide (result = hash) = true ↔ result = hash) ∧ start + 4 = start + 4
  simp

end Proofs.Cpp.RollingHash

namespace Proofs.Cpp.RollingHash

theorem simple_match_vector_run {S T : Type} [Conv S Int] [Inhabited T] [Conv T Int]
    (self : cp.SimpleRollingHash) (input : Array S) (query : Array T) (start : Nat)
    (hn : self.n_ = input.size)
    (hh : ∀ i, i ≤ input.size → self.hash_sum_[i]!.toNat =
      prefixHash cp.SIMPLE_BASE.toNat input i)
    (hp : ∀ i, i ≤ input.size → self.pows[i]!.toNat = cp.SIMPLE_BASE.toNat ^ i % M61)
    (hfit : query.size ≤ input.size)
    (hin : ∀ i, i < query.size →
      -(2^31 : Int) ≤ (Conv.conv query[i]! : Int) ∧ (Conv.conv query[i]! : Int) < 2^32) :
    let positions := range 0 ((input.size : Int) - query.size + 1)
    ∃ answer clock first, (cp.SimpleRollingHash.match_vector self query).run start =
      some (answer, clock) ∧
      FirstMatch (fun i => SimpleFingerprintsMatch input query i.toNat) positions first ∧
      answer = first.elim cp.RH_NPOS UInt64.ofInt ∧
      clock ≤ start + 2 + 5 * query.size + 5 * positions.length := by
  let positions := range 0 ((input.size : Int) - query.size + 1)
  let checkAt := fun (i : Int) (hash : UInt64) => do
    let word ← cp.SimpleRollingHash.hash_int_int self i (i + query.size)
    return decide (word = hash)
  obtain ⟨hash, afterHash, hhash, hseq, htime⟩ := run_of_triple
    (simple_hash_all_spec self query (start + 1) hin)
  let hit := fun i : Int => SimpleFingerprintsMatch input query i.toNat
  have hcheck : ∀ seen i suffix, positions = seen ++ i :: suffix →
      FirstMatch hit seen none → ∀ entry : Nat,
      ⦃fun c => ⌜c = entry⌝⦄ checkAt i hash
      ⦃⇓ result c => ⌜(result = true ↔ hit i) ∧ c ≤ entry + 4⌝⦄ := by
    intro seen i suffix hpositions _ entry
    have hi : i ∈ positions := by simp [hpositions]
    simp [positions, range, List.mem_map] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    have hj' : j + query.size ≤ input.size := by omega
    apply Triple.iff.mpr
    intro c hc
    have hc' : c = entry := by simpa using hc
    subst c
    obtain ⟨b, clock, hrun, hhit, hclock⟩ := run_of_triple
      (simple_compare_query_spec self input query hash j entry hj' hh hp hseq)
    simp only [Int.toNat_natCast, hit]
    change (wp⟦checkAt (j : Int) hash⟧ _ entry).down
    change (checkAt (j : Int) hash).run entry = some (b, clock) at hrun
    simp [wp, hrun, hclock]
    exact ⟨hhit, Nat.le_refl _⟩
  obtain ⟨answer, clock, hsearch, ⟨first, hfirst, hencode⟩, hbound⟩ := run_of_triple
    (search_candidates_spec hit (fun i => checkAt i hash) positions
      UInt64.ofInt cp.RH_NPOS afterHash 4 hcheck)
  have heq : cp.SimpleRollingHash.match_vector self query = (do
    tick
    let hash ← cp.SimpleRollingHash.hash_all self query
    searchCandidates (fun i => checkAt i hash) positions UInt64.ofInt cp.RH_NPOS) := by
    cases self
    dsimp at hn
    simp [cp.SimpleRollingHash.match_vector, searchCandidates, checkAt, positions, size, hn,
      Nat.not_lt.mpr hfit] <;> rfl
  refine ⟨answer, clock, first, ?_, hfirst, hencode, ?_⟩
  · rw [heq]
    simp [StateT.run_bind, tick, hhash, hsearch]
  · dsimp [positions] at hbound
    omega

end Proofs.Cpp.RollingHash

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Mod61Math

namespace Proofs.Cpp.RollingHash

theorem simple_match_custom_vector_run {S T : Type} [Conv S Int] [Inhabited T] [Conv T Int]
    (self : cp.SimpleRollingHash) (input : Array S) (query : Array T) (indices : Array Int)
    (start : Nat) (hn : self.n_ = input.size)
    (hh : ∀ i, i ≤ input.size → self.hash_sum_[i]!.toNat =
      prefixHash cp.SIMPLE_BASE.toNat input i)
    (hp : ∀ i, i ≤ input.size → self.pows[i]!.toNat = cp.SIMPLE_BASE.toNat ^ i % M61)
    (hfit : query.size ≤ input.size)
    (hin : ∀ i, i < query.size →
      -(2^31 : Int) ≤ (Conv.conv query[i]! : Int) ∧ (Conv.conv query[i]! : Int) < 2^32) :
    let positions := range 0 (size indices)
    let hit := fun i => SimpleFingerprintsMatch input query (get indices i).toNat
    (∀ seen i suffix, positions = seen ++ i :: suffix → FirstMatch hit seen none →
      0 ≤ get indices i ∧ get indices i ≤ (input.size : Int) - query.size) →
    ∃ answer clock first,
      (cp.SimpleRollingHash.match_custom_vector self query indices).run start = some (answer, clock) ∧
      FirstMatch hit positions first ∧
      answer = first.elim cp.RH_NPOS (fun i => UInt64.ofInt (get indices i)) ∧
      clock ≤ start + 2 + 5 * query.size + 5 * indices.size := by
  dsimp only
  intro hvalid
  let positions := range 0 (size indices)
  let hit := fun i => SimpleFingerprintsMatch input query (get indices i).toNat
  let checkAt := fun i hash => do
    check (decide (0 ≤ get indices i))
    check (decide (get indices i ≤ self.n_ - query.size))
    let word ← cp.SimpleRollingHash.hash_int_int self (get indices i) (get indices i + query.size)
    return decide (word = hash)
  obtain ⟨hash, afterHash, hhash, hseq, htime⟩ := run_of_triple
    (simple_hash_all_spec self query (start + 1) hin)
  have hcheck : ∀ seen i suffix, positions = seen ++ i :: suffix →
      FirstMatch hit seen none → ∀ entry : Nat,
      ⦃fun c => ⌜c = entry⌝⦄ checkAt i hash
      ⦃⇓ result c => ⌜(result = true ↔ hit i) ∧ c ≤ entry + 4⌝⦄ := by
    intro seen i suffix hpositions hseen entry
    obtain ⟨hlo, hhi⟩ := hvalid seen i suffix hpositions hseen
    have hhi' : get indices i ≤ self.n_ - query.size := by rwa [hn]
    have hcast := Int.toNat_of_nonneg hlo
    have hright : (get indices i).toNat + query.size ≤ input.size := by omega
    obtain ⟨result, clock, hrun, hresult, hclock⟩ := run_of_triple
      (simple_compare_query_spec self input query hash (get indices i).toNat entry hright hh hp hseq)
    apply triple_of_run result clock
    · simpa [checkAt, check, hlo, hhi', hcast, pure_bind] using hrun
    · exact ⟨hresult, Nat.le_of_eq hclock⟩
  obtain ⟨answer, clock, hsearch, ⟨first, hfirst, hencode⟩, hbound⟩ :=
    run_of_triple (search_candidates_spec hit (fun i => checkAt i hash) positions
      (fun i => UInt64.ofInt (get indices i)) cp.RH_NPOS afterHash 4 hcheck)
  have heq : cp.SimpleRollingHash.match_custom_vector self query indices = (do
    tick
    let hash ← cp.SimpleRollingHash.hash_all self query
    searchCandidates (fun i => checkAt i hash) positions
      (fun i => UInt64.ofInt (get indices i)) cp.RH_NPOS) := by
    have hfit' : ¬ self.n_ < (query.size : Int) := by omega
    cases self
    simp [cp.SimpleRollingHash.match_custom_vector, searchCandidates, checkAt, positions, size, hfit',
      bind_assoc] <;> rfl
  refine ⟨answer, clock, first, ?_, hfirst, hencode, ?_⟩
  · rw [heq]
    simp [StateT.run_bind, tick, hhash, hsearch]
  · have hlength : positions.length = indices.size := by simp [positions, size]
    rw [hlength] at hbound
    omega

end Proofs.Cpp.RollingHash

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Mod61Math

namespace Proofs.Cpp.RollingHash

def simpleBoundaryMatch {T : Type} [Inhabited T] [Conv T Int] (self : cp.SimpleRollingHash)
    (query : Array T) (suffix : Bool) : M Bool := do
  tick
  let n := size query
  if decide (n > self.n_) then return false
  let h ← cp.SimpleRollingHash.hash_all self query
  let word ← if suffix then cp.SimpleRollingHash.hash_int_int self (self.n_ - n) self.n_
    else cp.SimpleRollingHash.hash_int_int self 0 n
  return decide (word = h)

theorem simple_starts_with_eq {T : Type} [Inhabited T] [Conv T Int]
    (self : cp.SimpleRollingHash) (query : Array T) :
    cp.SimpleRollingHash.starts_with_vector self query = simpleBoundaryMatch self query false := by
  cases self
  rfl

theorem simple_ends_with_eq {T : Type} [Inhabited T] [Conv T Int]
    (self : cp.SimpleRollingHash) (query : Array T) :
    cp.SimpleRollingHash.ends_with_vector self query = simpleBoundaryMatch self query true := by
  cases self
  rfl

theorem simple_boundary_match_run {S T : Type} [Conv S Int] [Inhabited T] [Conv T Int]
    (self : cp.SimpleRollingHash) (input : Array S) (query : Array T) (suffix : Bool)
    (start : Nat) (hn : self.n_ = input.size)
    (hh : ∀ i, i ≤ input.size → self.hash_sum_[i]!.toNat =
      prefixHash cp.SIMPLE_BASE.toNat input i)
    (hp : ∀ i, i ≤ input.size → self.pows[i]!.toNat = cp.SIMPLE_BASE.toNat ^ i % M61)
    (hin : ∀ i, i < query.size →
      -(2^31 : Int) ≤ (Conv.conv query[i]! : Int) ∧ (Conv.conv query[i]! : Int) < 2^32) :
    let l := if suffix then input.size - query.size else 0
    ∃ answer clock, (simpleBoundaryMatch self query suffix).run start = some (answer, clock) ∧
      (answer = true ↔ query.size ≤ input.size ∧ SimpleFingerprintsMatch input query l) ∧
      clock = if query.size ≤ input.size then start + 6 + 5 * query.size else start + 1 := by
  by_cases hfit : query.size ≤ input.size
  · let l := if suffix then input.size - query.size else 0
    have hright : l + query.size ≤ input.size := by
      cases suffix <;> simp [l] <;> omega
    obtain ⟨hash, afterHash, hhash, hseq, htime⟩ := run_of_triple
      (simple_hash_all_spec self query (start + 1) hin)
    obtain ⟨answer, clock, hcompare, hv, hc⟩ := run_of_triple
      (simple_compare_query_spec self input query hash l afterHash hright hh hp hseq)
    refine ⟨answer, clock, ?_, by simpa [hfit] using hv, by simp [hfit]; omega⟩
    have hfit' : ¬ self.n_ < size query := by rw [hn, size]; omega
    have htick : tick.run start = some ((), start + 1) := rfl
    simp only [simpleBoundaryMatch, hfit', decide_false, Bool.false_eq_true, ite_false,
      StateT.run_bind, htick]
    change Option.bind ((cp.SimpleRollingHash.hash_all self query).run (start + 1)) (fun p =>
      (do
        let word ← if suffix then cp.SimpleRollingHash.hash_int_int self (self.n_ - size query) self.n_
          else cp.SimpleRollingHash.hash_int_int self 0 (size query)
        return decide (word = p.1) : M Bool).run p.2) = _
    rw [hhash, Option.bind_some]
    cases suffix
    · simpa [l, size, StateT.run_bind] using hcompare
    · simp only [ite_true, hn, size]
      have hr : (l : Int) + query.size = input.size := by
        simp only [l, ite_true]
        omega
      simp only [hr] at hcompare
      rw [← Int.ofNat_sub hfit]
      simpa [l, StateT.run_bind] using hcompare
  · have hlong : self.n_ < size query := by rw [hn, size]; omega
    refine ⟨false, start + 1, ?_, by simp [hfit], by simp [hfit]⟩
    simp only [simpleBoundaryMatch, hlong, decide_true, ite_true]
    rfl

end Proofs.Cpp.RollingHash

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Mod61Math

namespace Proofs.Cpp.RollingHash

def SimpleTables {T : Type} [Conv T Int] (input : Array T) (self : cp.SimpleRollingHash) : Prop :=
  self.n_ = input.size ∧ self.hash_sum_.size = input.size + 1 ∧ self.pows.size = input.size + 1 ∧
  Fingerprints cp.SIMPLE_BASE.toNat 0 input.size input self.hash_sum_ ∧
  Powers cp.SIMPLE_BASE.toNat 0 input.size self.pows

theorem simple_init_vec_run {T : Type} [Inhabited T] [Conv T Int] (input : Array T) (start : Nat)
    (hin : ∀ i, i < input.size → -(2^31 : Int) ≤ (Conv.conv input[i]! : Int) ∧
      (Conv.conv input[i]! : Int) < 2^32) :
    ∃ self, (cp.SimpleRollingHash.init_vec input).run start = some (self, start + 4 + 9 * input.size) ∧
      SimpleTables input self := by
  obtain ⟨self, clock, hbuild, hn, hh, hp, hfp, hpow, hclock⟩ :=
    run_of_triple (simple_build_spec input (start + 1) hin)
  refine ⟨self, ?_, hn, hh, hp, hfp, hpow⟩
  have hclock' : clock = start + 4 + 9 * input.size := by omega
  simp [cp.SimpleRollingHash.init_vec, tick, size, hbuild, ← hclock']

theorem simple_init_string_run (input : Array Int) (start : Nat)
    (hlen : input.size < 2 ^ 31)
    (hin : ∀ i, i < input.size → -(2^31 : Int) ≤ input[i]! ∧ input[i]! < 2^32) :
    ∃ self, (cp.SimpleRollingHash.init_string input).run start =
      some (self, start + 5 + 12 * input.size) ∧ SimpleTables input self := by
  obtain ⟨copy, afterCopy, hcopy, heq, htcopy⟩ :=
    run_of_triple (to_vec_char_spec input (start + 1) hlen)
  subst copy
  obtain ⟨self, clock, hbuild, hn, hh, hp, hfp, hpow, hclock⟩ :=
    run_of_triple (simple_build_spec input afterCopy hin)
  refine ⟨self, ?_, hn, hh, hp, hfp, hpow⟩
  have hclock' : clock = start + 5 + 12 * input.size := by omega
  simp [cp.SimpleRollingHash.init_string, signed_size input hlen, tick, hcopy, hbuild, ← hclock']

end Proofs.Cpp.RollingHash

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.RollingHash

theorem rolling_init_string_spec
    (t : Array Int) (strength start : Nat) (hStrength : strength ≤ 16)
    (hlenInput : t.size < 2 ^ 31)
    (hin : ∀ i, i < t.size → -(2^31 : Int) ≤ t[i]! ∧ t[i]! < 2^32) :
    let sizeOfTables := strength * (t.size + 1)
    ⦃fun c => ⌜c = start⌝⦄ cp.MultiRollingHash.init_string_int t (strength : Int)
    ⦃⇓ r c => ⌜r.n_ = t.size ∧ r.strength_ = strength ∧
      r.hash_sum_.size = sizeOfTables ∧ r.pows.size = sizeOfTables ∧
      CorrectRows t strength r.hash_sum_ r.pows ∧
      c = start + 1 + 2 * sizeOfTables + strength * (4 + 10 * t.size)⌝⦄ := by
  have hs : (strength : Int) ≤ cp.rh_in.SZ_BASE := by
    change (strength : Int) ≤ 16
    exact_mod_cast hStrength
  unfold cp.MultiRollingHash.init_string_int
  rw [signed_size t hlenInput]
  simp only [hs, decide_true, check, ite_true, pure_bind,
    not_lt.mpr (Int.natCast_nonneg strength), decide_false, Bool.false_eq_true, ite_false, size]
  let width := strength * (t.size + 1)
  have hwidth : (strength : Int) * ((t.size : Int) + 1) = (width : Int) := by
    simp [width, Nat.cast_mul, Nat.cast_add]
  rw [hwidth]
  mvcgen
  case inv1 =>
    exact ⇓⟨xs, hashes, powers, n, rows⟩ c => ⌜n = t.size ∧ rows = strength ∧
      hashes.size = width ∧ powers.size = width ∧
      CorrectRows t xs.prefix.length hashes powers ∧ UnstartedRows t.size xs.prefix.length strength hashes ∧
      c = start + 1 + 2 * width + xs.prefix.length * (4 + 10 * t.size)⌝
  all_goals simp +zetaDelta at *
  · have hcursor := range_cursor ‹range _ _ = _ ++ _ :: _›
    have hlen := range_prefix_length ‹range _ _ = _ ++ _ :: _›
    subst hcursor
    rename_i pre suffix tables clock hstate hlist
    obtain ⟨hn, hrows, hh, hp, hcorrect, hzero, hclock⟩ := ‹_ ∧ _›
    have hlt : pre.length < strength := by simpa using hlen
    have hb : pre.length < 16 := Nat.lt_of_lt_of_le hlt hStrength
    have hbnd := row_end_before (n := t.size) hlt
    simp only [zero_add]
    apply (Triple.iff.mp (wp_of_triple (fun c => to_vec_char_spec t c hlenInput))) _
    intro copy afterCopy ⟨heq, hcopy⟩
    subst copy
    apply (Triple.iff.mp (rolling_build_wp _ _ _ _)) _
    refine ⟨hb, hn, hin, hh ▸ hbnd, hp ▸ hbnd, hzero _ (Nat.le_refl _) hlt, ?_⟩
    intro r hnewn hnewrows hnewh hnewp hrowHash hrowPow hstableHash hstablePow
    obtain ⟨hcorrect', hzero'⟩ := extend_correct_rows _ _ _ _ _ _ _
      hcorrect hzero hrowHash hrowPow hstableHash hstablePow
    refine ⟨hnewn.trans hn, hnewrows.trans hrows, hnewh.trans hh, hnewp.trans hp, hcorrect', hzero', ?_⟩
    rw [Nat.add_mul, Nat.one_mul]
    omega
  · have hwidth' : (strength : Int) * ((t.size : Int) + 1) = (width : Int) := by
      simp [width, Nat.cast_mul, Nat.cast_add]
    have hreplicate : resize (([] : List UInt64).toArray : Array UInt64) ((strength : Int) * ((t.size : Int) + 1)) 0 =
        Array.replicate width 0 := by
      rw [hwidth']
      cases width <;> simp [resize]
    have hclockWidth : ((strength : Int) * ((t.size : Int) + 1)).toNat = width := by
      rw [hwidth', Int.toNat_natCast]
    simp only [hreplicate, hclockWidth, Array.size_replicate, width, true_and]
    refine ⟨?_, ?_, by omega⟩
    · intro i hi
      omega
    · intro i _ hi
      have hi' : i * (t.size + 1) < width :=
        Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (row_end_before (n := t.size) hi)
      change (Array.replicate width (0 : UInt64))[i * (t.size + 1)]!.toNat = 0
      have hb : i * (t.size + 1) < (Array.replicate width (0 : UInt64)).size := by
        rw [Array.size_replicate]
        exact hi'
      rw [getElem!_pos (Array.replicate width (0 : UInt64)) (i * (t.size + 1)) hb]
      simp
  · obtain ⟨hn, hrows, hh, hp, hcorrect, _, hclock⟩ := ‹_ ∧ _›
    exact ⟨hn, hrows, hh, hp, hcorrect, hclock⟩


theorem rolling_init_vec_negative_run {T : Type} [Inhabited T] [Conv T Int]
    (t : Array T) (strength : Int) (start : Nat) (hneg : strength < 0) :
    (cp.MultiRollingHash.init_vec_int t strength).run start =
      some (⟨([] : List UInt64).toArray, ([] : List UInt64).toArray, t.size, strength⟩, start + 1) := by
  have hs : strength ≤ cp.rh_in.SZ_BASE := by change strength ≤ 16; omega
  simp [cp.MultiRollingHash.init_vec_int, hs, hneg, check, size, range, resize, tick, tickN]

theorem rolling_init_string_negative_run (t : Array Int) (strength : Int) (start : Nat)
    (hneg : strength < 0) (hlen : t.size < 2 ^ 31) :
    (cp.MultiRollingHash.init_string_int t strength).run start =
      some (⟨([] : List UInt64).toArray, ([] : List UInt64).toArray, t.size, strength⟩, start + 1) := by
  have hs : strength ≤ cp.rh_in.SZ_BASE := by change strength ≤ 16; omega
  simp [cp.MultiRollingHash.init_string_int, signed_size t hlen, hs, hneg, check, range, resize, tick, tickN]

end Proofs.Cpp.RollingHash

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.RollingHash

def stringQuery {R : Type} (query : Array Int) (f : Array Int → M R) : M R := do
  tick
  let symbols ← cp.rh_in.to_vec_char query
  f symbols

theorem string_query_run {R : Type} (query : Array Int) (f : Array Int → M R)
    (start : Nat) (hlen : query.size < 2 ^ 31) :
    (stringQuery query f).run start = (f query).run (start + 2 + 3 * query.size) := by
  obtain ⟨copy, clock, hrun, hcopy, hclock⟩ := run_of_triple (to_vec_char_spec query (start + 1) hlen)
  subst copy
  have hclock' : clock = start + 2 + 3 * query.size := by omega
  simp [stringQuery, tick, hrun, hclock']

theorem rolling_match_vec_eq {T : Type} [Inhabited T] [Conv T Int]
    (self : cp.MultiRollingHash) (query : Array T) :
    cp.MultiRollingHash.match__vec self query =
      (do
        tick
        cp.MultiRollingHash.match_vector self query) := by
  cases self
  rfl

theorem rolling_match_string_eq
    (self : cp.MultiRollingHash) (query : Array Int) :
    cp.MultiRollingHash.match__string self query =
      stringQuery query (fun symbols => cp.MultiRollingHash.match_vector self symbols) := by
  cases self
  rfl

theorem rolling_match_custom_vec_eq {T : Type} [Inhabited T] [Conv T Int]
    (self : cp.MultiRollingHash) (query : Array T) (indices : Array Int) :
    cp.MultiRollingHash.match_custom_vec_vec self query indices =
      (do
        tick
        cp.MultiRollingHash.match_custom_vector self query indices) := by
  cases self
  rfl

theorem rolling_match_custom_string_eq
    (self : cp.MultiRollingHash) (query : Array Int) (indices : Array Int) :
    cp.MultiRollingHash.match_custom_string_vec self query indices =
      stringQuery query (fun symbols => cp.MultiRollingHash.match_custom_vector self symbols indices) := by
  cases self
  rfl

theorem rolling_starts_with_vec_eq {T : Type} [Inhabited T] [Conv T Int]
    (self : cp.MultiRollingHash) (query : Array T) :
    cp.MultiRollingHash.starts_with_vec self query =
      (do
        tick
        cp.MultiRollingHash.starts_with_vector self query) := by
  cases self
  rfl

theorem rolling_starts_with_string_eq
    (self : cp.MultiRollingHash) (query : Array Int) :
    cp.MultiRollingHash.starts_with_string self query =
      stringQuery query (fun symbols => cp.MultiRollingHash.starts_with_vector self symbols) := by
  cases self
  rfl

theorem rolling_ends_with_vec_eq {T : Type} [Inhabited T] [Conv T Int]
    (self : cp.MultiRollingHash) (query : Array T) :
    cp.MultiRollingHash.ends_with_vec self query =
      (do
        tick
        cp.MultiRollingHash.ends_with_vector self query) := by
  cases self
  rfl

theorem rolling_ends_with_string_eq
    (self : cp.MultiRollingHash) (query : Array Int) :
    cp.MultiRollingHash.ends_with_string self query =
      stringQuery query (fun symbols => cp.MultiRollingHash.ends_with_vector self symbols) := by
  cases self
  rfl

theorem simple_match_vec_eq {T : Type} [Inhabited T] [Conv T Int]
    (self : cp.SimpleRollingHash) (query : Array T) :
    cp.SimpleRollingHash.match__vec self query =
      (do
        tick
        cp.SimpleRollingHash.match_vector self query) := by
  cases self
  rfl

theorem simple_match_string_eq
    (self : cp.SimpleRollingHash) (query : Array Int) :
    cp.SimpleRollingHash.match__string self query =
      stringQuery query (fun symbols => cp.SimpleRollingHash.match_vector self symbols) := by
  cases self
  rfl

theorem simple_match_custom_vec_eq {T : Type} [Inhabited T] [Conv T Int]
    (self : cp.SimpleRollingHash) (query : Array T) (indices : Array Int) :
    cp.SimpleRollingHash.match_custom_vec_vec self query indices =
      (do
        tick
        cp.SimpleRollingHash.match_custom_vector self query indices) := by
  cases self
  rfl

theorem simple_match_custom_string_eq
    (self : cp.SimpleRollingHash) (query : Array Int) (indices : Array Int) :
    cp.SimpleRollingHash.match_custom_string_vec self query indices =
      stringQuery query (fun symbols => cp.SimpleRollingHash.match_custom_vector self symbols indices) := by
  cases self
  rfl

theorem simple_starts_with_vec_eq {T : Type} [Inhabited T] [Conv T Int]
    (self : cp.SimpleRollingHash) (query : Array T) :
    cp.SimpleRollingHash.starts_with_vec self query =
      (do
        tick
        cp.SimpleRollingHash.starts_with_vector self query) := by
  cases self
  rfl

theorem simple_starts_with_string_eq
    (self : cp.SimpleRollingHash) (query : Array Int) :
    cp.SimpleRollingHash.starts_with_string self query =
      stringQuery query (fun symbols => cp.SimpleRollingHash.starts_with_vector self symbols) := by
  cases self
  rfl

theorem simple_ends_with_vec_eq {T : Type} [Inhabited T] [Conv T Int]
    (self : cp.SimpleRollingHash) (query : Array T) :
    cp.SimpleRollingHash.ends_with_vec self query =
      (do
        tick
        cp.SimpleRollingHash.ends_with_vector self query) := by
  cases self
  rfl

theorem simple_ends_with_string_eq
    (self : cp.SimpleRollingHash) (query : Array Int) :
    cp.SimpleRollingHash.ends_with_string self query =
      stringQuery query (fun symbols => cp.SimpleRollingHash.ends_with_vector self symbols) := by
  cases self
  rfl

theorem simple_match_too_long_run {T : Type} [Inhabited T] [Conv T Int]
    (self : cp.SimpleRollingHash) (query : Array T) (start : Nat)
    (h : self.n_ < (query.size : Int)) :
    (cp.SimpleRollingHash.match_vector self query).run start = some (cp.RH_NPOS, start + 1) := by
  simp [cp.SimpleRollingHash.match_vector, size, tick, h]

theorem simple_match_custom_too_long_run {T : Type} [Inhabited T] [Conv T Int]
    (self : cp.SimpleRollingHash) (query : Array T) (indices : Array Int) (start : Nat)
    (h : self.n_ < (query.size : Int)) :
    (cp.SimpleRollingHash.match_custom_vector self query indices).run start =
      some (cp.RH_NPOS, start + 1) := by
  simp [cp.SimpleRollingHash.match_custom_vector, size, tick, h]

end Proofs.Cpp.RollingHash

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Mod61Math

namespace Proofs.Cpp.RollingHash

theorem rolling_prefix_hash_run {T : Type} [Conv T Int] (self : cp.MultiRollingHash)
    (input : Array T) (strength r start : Nat) (hn : self.n_ = input.size)
    (hs : self.strength_ = strength) (hr : r ≤ input.size)
    (ht : CorrectRows input strength self.hash_sum_ self.pows) :
    ∃ result, (cp.MultiRollingHash.hash_int self r).run start =
      some (result, start + 2 + 7 * strength) ∧
      result.size = strength ∧ SliceHashes input 0 r strength result := by
  obtain ⟨result, clock, heval, hsize, hslices, htime⟩ := run_of_triple
    (rolling_hash_vec_spec self input strength 0 r (start + 1) hn hs hr (Nat.zero_le _) ht)
  refine ⟨result, ?_, hsize, hslices⟩
  have hclock : clock = start + 2 + 7 * strength := by omega
  cases self
  simp [cp.MultiRollingHash.hash_int, tick]
  simpa only [hclock, Int.natCast_zero] using heval

theorem simple_prefix_hash_run {T : Type} [Conv T Int] (self : cp.SimpleRollingHash)
    (input : Array T) (r start : Nat) (hr : r ≤ input.size)
    (hh : ∀ i, i ≤ input.size → self.hash_sum_[i]!.toNat =
      prefixHash cp.SIMPLE_BASE.toNat input i)
    (hp : ∀ i, i ≤ input.size → self.pows[i]!.toNat = cp.SIMPLE_BASE.toNat ^ i % M61) :
    ∃ result, (cp.SimpleRollingHash.hash_int self r).run start = some (result, start + 5) ∧
      result.toNat = prefixHash cp.SIMPLE_BASE.toNat input r := by
  obtain ⟨result, heval, hvalue⟩ :=
    simple_interval_run self input 0 r (start + 1) (Nat.zero_le _) hr hh hp
  refine ⟨result, ?_, ?_⟩
  · cases self
    simp [cp.SimpleRollingHash.hash_int, tick]
    exact heval
  · simpa [prefixHash] using hvalue

theorem index_ne_npos (i : Int) (hlo : 0 ≤ i) (hhi : i < 2 ^ 31) :
    UInt64.ofInt i ≠ cp.RH_NPOS := by
  intro h
  have hbits := congrArg UInt64.toNat h
  rw [cp.RH_NPOS, UInt64.ofInt, Int.emod_eq_of_lt hlo (by omega), UInt64.toNat_ofNat'] at hbits
  rw [Nat.mod_eq_of_lt (by omega)] at hbits
  have : i.toNat = 18446744073709551615 := hbits
  omega

end Proofs.Cpp.RollingHash

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Mod61Math

namespace Proofs.Cpp.RollingHash

theorem legacy_init_run {T : Type} [Inhabited T] [Conv T Int]
    (input : Array T) (start : Nat)
    (hin : ∀ i, i < input.size → -(2^31 : Int) ≤ (Conv.conv input[i]! : Int) ∧
      (Conv.conv input[i]! : Int) < 2^32) :
    ∃ self, (cp.RollingHash.init input).run start =
      some (self, start + 5 + 9 * input.size) ∧ SimpleTables input self.impl_ := by
  obtain ⟨impl, hrun, ht⟩ := simple_init_vec_run input (start + 1) hin
  refine ⟨⟨impl⟩, ?_, ht⟩
  simp [cp.RollingHash.init, tick, hrun]

theorem legacy_interval_run {T : Type} [Conv T Int]
    (self : cp.RollingHash T) (input : Array T) (left right start : Nat)
    (hleft : left ≤ right) (hright : right ≤ input.size) (ht : SimpleTables input self.impl_) :
    ∃ answer, (cp.RollingHash.hash_int_int self left right).run start =
      some (answer, start + 5) ∧ answer.toNat = sliceHash cp.SIMPLE_BASE.toNat input left right := by
  obtain ⟨_, _, _, hh, hp⟩ := ht
  have hh' : ∀ i, i ≤ input.size → self.impl_.hash_sum_[i]!.toNat =
      prefixHash cp.SIMPLE_BASE.toNat input i := by simpa [Fingerprints] using hh
  have hp' : ∀ i, i ≤ input.size →
      self.impl_.pows[i]!.toNat = cp.SIMPLE_BASE.toNat ^ i % M61 := by simpa [Powers] using hp
  obtain ⟨result, hrun, hresult⟩ := simple_interval_run self.impl_ input left right (start + 1)
    hleft hright hh' hp'
  refine ⟨result, ?_, hresult⟩
  simp [cp.RollingHash.hash_int_int, tick, hrun]

theorem legacy_prefix_run {T : Type} [Conv T Int]
    (self : cp.RollingHash T) (input : Array T) (right start : Nat)
    (hright : right ≤ input.size) (ht : SimpleTables input self.impl_) :
    ∃ answer, (cp.RollingHash.hash_int self right).run start =
      some (answer, start + 6) ∧ answer.toNat = prefixHash cp.SIMPLE_BASE.toNat input right := by
  obtain ⟨_, _, _, hh, hp⟩ := ht
  have hh' : ∀ i, i ≤ input.size → self.impl_.hash_sum_[i]!.toNat =
      prefixHash cp.SIMPLE_BASE.toNat input i := by simpa [Fingerprints] using hh
  have hp' : ∀ i, i ≤ input.size →
      self.impl_.pows[i]!.toNat = cp.SIMPLE_BASE.toNat ^ i % M61 := by simpa [Powers] using hp
  obtain ⟨result, hrun, hresult⟩ := simple_prefix_hash_run self.impl_ input right (start + 1) hright hh' hp'
  refine ⟨result, ?_, hresult⟩
  simp [cp.RollingHash.hash_int, tick, hrun]

end Proofs.Cpp.RollingHash
