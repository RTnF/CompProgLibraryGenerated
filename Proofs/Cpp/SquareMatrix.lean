import Proofs.Cpp.Gen.SquareMatrix
import Proofs.Cpp.Lib.Basic
import Proofs.MatPowMath

/-! # `square_matrix` (library/number/square_matrix.hpp)

Row-major `n × n` matrices. The elementwise operations, the zero and identity matrices, the comparison and the product
are proved for any element type `T` (the loops write a prefix of the flat index: `EW`); the product is
`MM a b n i j n`, the sum of `a[i n + t] b[t n + j]` accumulated in loop order. `mat_pow` is proved for
`unsigned long long` (`UInt64`): its loop keeps `R · Y^e = A^E` for the matrices modulo `2^64` of `Proofs.MatPowMath`
(`mulF`, `PW`, `pow_round`), using `mat_mul` through its deterministic result `mulRes` (`mat_mul_wp`). -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.SquareMatrix

/-- Writing slot `k` extends the prefix where `a` holds `f`. -/
theorem pre_step {α : Type} [Inhabited α] (a a0 : Array α) (f : Nat → α) (k : Nat) (hk : k < a.size)
    (hd : ∀ i, i < k → a[i]! = f i) (hr : ∀ i, k ≤ i → a[i]! = a0[i]!) :
    (∀ i, i < k + 1 → (set a (k : Int) (f k))[i]! = f i) ∧ (∀ i, k + 1 ≤ i → (set a (k : Int) (f k))[i]! = a0[i]!) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rw [getElemBang_set _ _ _ _ (by simpa using hk)]
    by_cases h : i = k
    · simp [h]
    · simp only [Int.toNat_natCast, h, ite_false]; exact hd i (by omega)
  · rw [getElemBang_set _ _ _ _ (by simpa using hk)]
    simp only [Int.toNat_natCast, show i ≠ k by omega, ite_false]; exact hr i (by omega)

/-- An elementwise loop `a[i] = g i (a[i])` for `i < m` (the shape of `mat_add_assign`, `mat_sub_assign`, `mat_zero`,
`mat_negate`). -/
abbrev EW {α : Type} [Inhabited α] (a a0 : Array α) (f : Nat → α) (k : Nat) : Prop :=
  a.size = a0.size ∧ (∀ i, i < k → a[i]! = f i) ∧ ∀ i, k ≤ i → a[i]! = a0[i]!

theorem ew_step {α : Type} [Inhabited α] (d a : Array α) (f : Nat → α) (L : Nat) (hL : L < a.size)
    (h : EW d a f L) (x : α) (hx : x = f L) : EW (set d (L : Int) x) a f (L + 1) := by
  obtain ⟨hs, hd, hr⟩ := h
  subst hx
  have P := pre_step d a f L (by omega) hd hr
  exact ⟨by simp [hs], P.1, P.2⟩

theorem ew_cur {α : Type} [Inhabited α] (d a : Array α) (f : Nat → α) (L : Nat) (h : EW d a f L) :
    get d (L : Int) = a[L]! := by
  rw [get_eq, Int.toNat_natCast]; exact h.2.2 L (Nat.le_refl L)

theorem cur_eq {M : Int} {pref suff : List Int} {c : Int} (h : range 0 M = pref ++ c :: suff) :
    c = (pref.length : Int) ∧ (pref.length : Int) < M := by
  have e := range_cursor h
  have l := range_prefix_length h
  simp at e l; exact ⟨e, l⟩

theorem ew_vc {α : Type} [Inhabited α] (d a : Array α) (f : Nat → α) (N : Nat) (ha : N * N ≤ a.size)
    (pref suff : List Int) (hr : range 0 ((N : Int) * N) = pref ++ (pref.length : Int) :: suff)
    (h : EW d a f pref.length) (x : α) (hx : x = f pref.length) : EW (set d (pref.length : Int) x) a f (pref.length + 1) := by
  have hl := range_prefix_length hr
  rw [Int.sub_zero, ← Nat.cast_mul, Int.toNat_natCast] at hl
  exact ew_step d a f _ (by omega) h x hx

theorem nn_toNat (N : Nat) : ((N : Int) * N).toNat = N * N := by rw [← Nat.cast_mul, Int.toNat_natCast]

theorem mat_add_assign_spec {T : Type} [Inhabited T] [Add T] (a b : Array T) (N : Nat) (ha : N * N ≤ a.size)
    (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.mat_add_assign a b N
    ⦃⇓ r c => ⌜EW r a (fun i => a[i]! + b[i]!) (N * N) ∧ c = t0 + 1 + N * N⌝⦄ := by
  mvcgen [cp.mat_add_assign]
  case inv1 => exact ⇓⟨xs, d⟩ c => ⌜EW d a (fun i => a[i]! + b[i]!) xs.prefix.length ∧ c = t0 + 1 + xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  · obtain ⟨hE, hc⟩ := ‹EW _ _ _ _ ∧ _›
    obtain ⟨rfl, -⟩ := cur_eq ‹range 0 _ = _ ++ _ :: _›
    refine ⟨ew_vc _ _ _ N ha _ _ ‹_› hE _ ?_, by omega⟩
    rw [ew_cur _ _ _ _ hE, get_eq, Int.toNat_natCast]
  · exact ⟨⟨rfl, fun i hi => absurd hi (by omega), fun i _ => rfl⟩, ‹_›⟩
  · obtain ⟨hE, hc⟩ := ‹EW _ _ _ _ ∧ _›
    rw [range_length, Int.sub_zero, nn_toNat] at hE hc
    exact ⟨hE, hc⟩

theorem mat_sub_assign_spec {T : Type} [Inhabited T] [Sub T] (a b : Array T) (N : Nat) (ha : N * N ≤ a.size)
    (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.mat_sub_assign a b N
    ⦃⇓ r c => ⌜EW r a (fun i => a[i]! - b[i]!) (N * N) ∧ c = t0 + 1 + N * N⌝⦄ := by
  mvcgen [cp.mat_sub_assign]
  case inv1 => exact ⇓⟨xs, d⟩ c => ⌜EW d a (fun i => a[i]! - b[i]!) xs.prefix.length ∧ c = t0 + 1 + xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  · obtain ⟨hE, hc⟩ := ‹EW _ _ _ _ ∧ _›
    obtain ⟨rfl, -⟩ := cur_eq ‹range 0 _ = _ ++ _ :: _›
    refine ⟨ew_vc _ _ _ N ha _ _ ‹_› hE _ ?_, by omega⟩
    rw [ew_cur _ _ _ _ hE, get_eq, Int.toNat_natCast]
  · exact ⟨⟨rfl, fun i hi => absurd hi (by omega), fun i _ => rfl⟩, ‹_›⟩
  · obtain ⟨hE, hc⟩ := ‹EW _ _ _ _ ∧ _›
    rw [range_length, Int.sub_zero, nn_toNat] at hE hc
    exact ⟨hE, hc⟩

theorem mat_zero_spec {T : Type} [Inhabited T] [Zero T] (a : Array T) (N : Nat) (ha : N * N ≤ a.size)
    (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.mat_zero a N
    ⦃⇓ r c => ⌜EW r a (fun _ => (0 : T)) (N * N) ∧ c = t0 + 1 + N * N⌝⦄ := by
  mvcgen [cp.mat_zero]
  case inv1 => exact ⇓⟨xs, d⟩ c => ⌜EW d a (fun _ => (0 : T)) xs.prefix.length ∧ c = t0 + 1 + xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  · obtain ⟨hE, hc⟩ := ‹EW _ _ _ _ ∧ _›
    obtain ⟨rfl, -⟩ := cur_eq ‹range 0 _ = _ ++ _ :: _›
    refine ⟨ew_vc _ _ _ N ha _ _ ‹_› hE _ ?_, by omega⟩
    rfl
  · exact ⟨⟨rfl, fun i hi => absurd hi (by omega), fun i _ => rfl⟩, ‹_›⟩
  · obtain ⟨hE, hc⟩ := ‹EW _ _ _ _ ∧ _›
    rw [range_length, Int.sub_zero, nn_toNat] at hE hc
    exact ⟨hE, hc⟩

theorem mat_negate_spec {T : Type} [Inhabited T] [Zero T] [Sub T] (a : Array T) (N : Nat) (ha : N * N ≤ a.size)
    (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.mat_negate a N
    ⦃⇓ r c => ⌜EW r a (fun i => (0 : T) - a[i]!) (N * N) ∧ c = t0 + 1 + N * N⌝⦄ := by
  mvcgen [cp.mat_negate]
  case inv1 => exact ⇓⟨xs, d⟩ c => ⌜EW d a (fun i => (0 : T) - a[i]!) xs.prefix.length ∧ c = t0 + 1 + xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  · obtain ⟨hE, hc⟩ := ‹EW _ _ _ _ ∧ _›
    obtain ⟨rfl, -⟩ := cur_eq ‹range 0 _ = _ ++ _ :: _›
    refine ⟨ew_vc _ _ _ N ha _ _ ‹_› hE _ ?_, by omega⟩
    rw [ew_cur _ _ _ _ hE]
  · exact ⟨⟨rfl, fun i hi => absurd hi (by omega), fun i _ => rfl⟩, ‹_›⟩
  · obtain ⟨hE, hc⟩ := ‹EW _ _ _ _ ∧ _›
    rw [range_length, Int.sub_zero, nn_toNat] at hE hc
    exact ⟨hE, hc⟩

theorem idx (N p q : Nat) : ((p : Int) * (N : Int) + (q : Int)).toNat = p * N + q := by
  rw [← Nat.cast_mul, ← Nat.cast_add, Int.toNat_natCast]

theorem div_mod_idx (N p q : Nat) (hq : q < N) : (p * N + q) / N = p ∧ (p * N + q) % N = q := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hq]; omega
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq]

theorem idx_lt (N p q : Nat) (hp : p < N) (hq : q < N) : p * N + q < N * N := by
  have : (p + 1) * N ≤ N * N := Nat.mul_le_mul_right N hp
  rw [Nat.add_mul, Nat.one_mul] at this; omega

/-- The identity matrix, as a function of the flat index. -/
def Idf {T : Type} [Zero T] [One T] (N : Nat) (idx : Nat) : T := if idx / N = idx % N then 1 else 0

theorem ew_step2 {α : Type} [Inhabited α] (d a : Array α) (f : Nat → α) (L : Nat) (hL : L < a.size)
    (h : EW d a f L) (x y : α) (hy : y = f L) : EW (set (set d (L : Int) x) (L : Int) y) a f (L + 1) := by
  obtain ⟨hs, hd, hr⟩ := h
  have g : ∀ k : Nat, (set (set d (L : Int) x) (L : Int) y)[k]! = (set d (L : Int) y)[k]! := by
    intro k
    rw [getElemBang_set _ _ _ _ (by simp; omega), getElemBang_set _ _ _ _ (by simp; omega),
      getElemBang_set _ _ _ _ (by simp; omega)]
    split <;> rfl
  have E := ew_step d a f L hL ⟨hs, hd, hr⟩ y hy
  exact ⟨by simp [hs], fun i hi => by rw [g]; exact E.2.1 i hi, fun i hi => by rw [g]; exact E.2.2 i hi⟩

theorem id_vc {T : Type} [Inhabited T] [Zero T] [One T] (d a : Array T) (N : Nat) (ha : N * N ≤ a.size)
    (pi si pj sj : List Int) (ci cj : Int) (hi : range 0 (N : Int) = pi ++ ci :: si)
    (hj : range 0 (N : Int) = pj ++ cj :: sj) (h : EW d a (Idf N) (pi.length * N + pj.length)) :
    (ci = cj → EW (set (set d (ci * N + cj) 0) (ci * N + cj) 1) a (Idf N) (pi.length * N + (pj.length + 1))) ∧
    (¬ci = cj → EW (set d (ci * N + cj) 0) a (Idf N) (pi.length * N + (pj.length + 1))) := by
  obtain ⟨rfl, hI⟩ := cur_eq hi
  obtain ⟨rfl, hJ⟩ := cur_eq hj
  have hI' : pi.length < N := by exact_mod_cast hI
  have hJ' : pj.length < N := by exact_mod_cast hJ
  have hL := idx_lt N _ _ hI' hJ'
  have e : (pi.length : Int) * N + pj.length = ((pi.length * N + pj.length : Nat) : Int) := by push_cast; ring
  obtain ⟨hdv, hmd⟩ := div_mod_idx N pi.length pj.length hJ'
  rw [e]
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · exact ew_step2 d a _ _ (by omega) h _ _ (by simp only [Idf, hdv, hmd]; rw [if_pos (by exact_mod_cast hij)])
  · exact ew_step d a _ _ (by omega) h _ (by simp only [Idf, hdv, hmd]; rw [if_neg (fun h => hij (by exact_mod_cast h))])

theorem mat_identity_spec {T : Type} [Inhabited T] [Zero T] [One T] (a : Array T) (N : Nat) (ha : N * N ≤ a.size)
    (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.mat_identity a N
    ⦃⇓ r c => ⌜EW r a (Idf N) (N * N) ∧ c = t0 + 1 + N * (1 + N)⌝⦄ := by
  mvcgen [cp.mat_identity]
  case inv1 => exact ⇓⟨xs, d⟩ c => ⌜EW d a (Idf N) (xs.prefix.length * N) ∧ c = t0 + 1 + xs.prefix.length * (1 + N)⌝
  case inv2 =>
    rename_i pi _ _ _ _ _ _
    exact ⇓⟨xs, d⟩ c => ⌜EW d a (Idf N) (pi.length * N + xs.prefix.length) ∧
      c = t0 + 1 + pi.length * (1 + N) + 1 + xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  · obtain ⟨hE, hc⟩ := ‹EW _ _ _ _ ∧ _›
    exact ⟨(id_vc _ _ N ha _ _ _ _ _ _ (by assumption) (by assumption) hE).1 ‹_›, by omega⟩
  · obtain ⟨hE, hc⟩ := ‹EW _ _ _ _ ∧ _›
    exact ⟨(id_vc _ _ N ha _ _ _ _ _ _ (by assumption) (by assumption) hE).2 ‹_›, by omega⟩
  · obtain ⟨hE, hc⟩ := ‹EW _ _ _ _ ∧ _›
    exact ⟨by simpa using hE, by omega⟩
  · obtain ⟨hE, hc⟩ := ‹EW _ _ _ _ ∧ _›
    refine ⟨by rw [Nat.add_mul, Nat.one_mul]; exact hE, by rw [Nat.add_mul, Nat.one_mul]; omega⟩
  · exact ⟨⟨rfl, fun i hi => absurd hi (by omega), fun i _ => rfl⟩, ‹_›⟩
  · obtain ⟨hE, hc⟩ := ‹EW _ _ _ _ ∧ _›
    exact ⟨hE, hc⟩

theorem mat_equal_spec {T : Type} [Inhabited T] [DecidableEq T] (a b : Array T) (N : Nat) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.mat_equal a b N
    ⦃⇓ r c => ⌜(r = true ↔ ∀ i, i < N * N → a[i]! = b[i]!) ∧ c = t0 + 1 + N * N⌝⦄ := by
  mvcgen [cp.mat_equal]
  case inv1 => exact ⇓⟨xs, f⟩ c => ⌜(f = true ↔ ∀ i, i < xs.prefix.length → a[i]! = b[i]!) ∧
    c = t0 + 1 + xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  · obtain ⟨-, hc⟩ := ‹(_ ↔ _) ∧ _›
    obtain ⟨rfl, -⟩ := cur_eq ‹range 0 _ = _ ++ _ :: _›
    refine ⟨⟨_, Nat.lt_succ_self _, ?_⟩, by omega⟩
    have hn := ‹¬get a _ = get b _›
    simp only [get_eq, Int.toNat_natCast] at hn
    exact hn
  · obtain ⟨hf, hc⟩ := ‹(_ ↔ _) ∧ _›
    obtain ⟨rfl, -⟩ := cur_eq ‹range 0 _ = _ ++ _ :: _›
    have he := ‹get a _ = get b _›
    simp only [get_eq, Int.toNat_natCast] at he
    refine ⟨?_, by omega⟩
    rw [hf]
    constructor
    · intro h i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h' | h'
      · exact h i h'
      · subst h'; exact he
    · intro h i hi; exact h i (by omega)
  · exact ‹_ = t0›
  · obtain ⟨hf, hc⟩ := ‹(_ ↔ _) ∧ _›
    rw [range_length, Int.sub_zero, nn_toNat] at hf hc
    exact ⟨hf, hc⟩

/-- The entry `(i, j)` of the product: `a[i n + 0] b[0 n + j] + ... ` accumulated from `0` in the order of the loop. -/
def MM {T : Type} [Inhabited T] [Zero T] [Add T] [Mul T] (a b : Array T) (N i j k : Nat) : T :=
  (List.range k).foldl (fun s t => s + a[i * N + t]! * b[t * N + j]!) 0

def MMf {T : Type} [Inhabited T] [Zero T] [Add T] [Mul T] (a b : Array T) (N : Nat) (idx : Nat) : T :=
  MM a b N (idx / N) (idx % N) N

theorem MM_succ {T : Type} [Inhabited T] [Zero T] [Add T] [Mul T] (a b : Array T) (N i j k : Nat) :
    MM a b N i j (k + 1) = MM a b N i j k + a[i * N + k]! * b[k * N + j]! := by
  simp [MM, List.range_succ]

theorem mm_vc {T : Type} [Inhabited T] [Zero T] [Add T] [Mul T] (a b : Array T) (N : Nat)
    (pi si pj sj pk sk : List Int) (ci cj ck : Int) (hi : range 0 (N : Int) = pi ++ ci :: si)
    (hj : range 0 (N : Int) = pj ++ cj :: sj) (hk : range 0 (N : Int) = pk ++ ck :: sk) (x : T)
    (h : x = MM a b N pi.length pj.length pk.length) :
    x + get a (ci * N + ck) * get b (ck * N + cj) = MM a b N pi.length pj.length (pk.length + 1) := by
  obtain ⟨rfl, -⟩ := cur_eq hi
  obtain ⟨rfl, -⟩ := cur_eq hj
  obtain ⟨rfl, -⟩ := cur_eq hk
  rw [MM_succ, h, get_eq, get_eq, idx, idx]

theorem mw_vc {T : Type} [Inhabited T] [Zero T] [Add T] [Mul T] (a b c c0 : Array T) (N : Nat)
    (hc : N * N ≤ c0.size) (pi si pj sj : List Int) (ci cj : Int) (hi : range 0 (N : Int) = pi ++ ci :: si)
    (hj : range 0 (N : Int) = pj ++ cj :: sj) (h : EW c c0 (MMf a b N) (pi.length * N + pj.length)) :
    EW (set c (ci * N + cj) (MM a b N pi.length pj.length N)) c0 (MMf a b N) (pi.length * N + (pj.length + 1)) := by
  obtain ⟨rfl, hI⟩ := cur_eq hi
  obtain ⟨rfl, hJ⟩ := cur_eq hj
  have hI' : pi.length < N := by exact_mod_cast hI
  have hJ' : pj.length < N := by exact_mod_cast hJ
  have hL := idx_lt N _ _ hI' hJ'
  have e : (pi.length : Int) * N + pj.length = ((pi.length * N + pj.length : Nat) : Int) := by push_cast; ring
  obtain ⟨hdv, hmd⟩ := div_mod_idx N pi.length pj.length hJ'
  rw [e]
  exact ew_step c c0 _ _ (by omega) h _ (by simp only [MMf, hdv, hmd])

theorem mat_mul_spec {T : Type} [Inhabited T] [Zero T] [Add T] [Mul T] (a b c : Array T) (N : Nat)
    (hc : N * N ≤ c.size) (t0 : Nat) :
    ⦃fun t => ⌜t = t0⌝⦄ cp.mat_mul a b c N
    ⦃⇓ r t => ⌜EW r c (MMf a b N) (N * N) ∧ t = t0 + 1 + N * (1 + N * (1 + N))⌝⦄ := by
  mvcgen [cp.mat_mul]
  case inv1 => exact ⇓⟨xs, d⟩ t => ⌜EW d c (MMf a b N) (xs.prefix.length * N) ∧
    t = t0 + 1 + xs.prefix.length * (1 + N * (1 + N))⌝
  case inv2 =>
    rename_i pi _ _ _ _ _ _
    exact ⇓⟨xs, d⟩ t => ⌜EW d c (MMf a b N) (pi.length * N + xs.prefix.length) ∧
      t = t0 + 1 + pi.length * (1 + N * (1 + N)) + 1 + xs.prefix.length * (1 + N)⌝
  case inv3 =>
    rename_i pi _ _ _ _ _ _ pj _ _ _ _ sj _
    exact ⇓⟨xs, x⟩ t => ⌜x = MM a b N pi.length pj.length xs.prefix.length ∧ t = sj + 1 + xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  · obtain ⟨hx, ht⟩ := ‹_ = MM _ _ _ _ _ _ ∧ _›
    exact ⟨mm_vc a b N _ _ _ _ _ _ _ _ _ (by assumption) (by assumption) (by assumption) _ hx, by omega⟩
  · rfl
  · obtain ⟨hx, ht⟩ := ‹_ = MM _ _ _ _ _ _ ∧ _›
    obtain ⟨hE, hc0⟩ := ‹EW _ _ _ (_ * N + _) ∧ _›
    rw [hx]
    refine ⟨mw_vc a b _ c N hc _ _ _ _ _ _ (by assumption) (by assumption) hE, ?_⟩
    rw [Nat.add_mul, Nat.one_mul]; omega
  · obtain ⟨hE, hc0⟩ := ‹EW _ _ _ _ ∧ _›
    exact ⟨by simpa using hE, by omega⟩
  · obtain ⟨hE, hc0⟩ := ‹EW _ _ _ _ ∧ _›
    refine ⟨by rw [Nat.add_mul, Nat.one_mul]; exact hE, ?_⟩
    rw [Nat.add_mul, Nat.one_mul]; omega
  · exact ⟨⟨rfl, fun i hi => absurd hi (by omega), fun i _ => rfl⟩, ‹_›⟩
  · exact ‹_ ∧ _›

/-- The result of `mat_mul`: the product in the first `N * N` entries, `c` after them. -/
def mulRes {T : Type} [Inhabited T] [Zero T] [Add T] [Mul T] (a b c : Array T) (N : Nat) : Array T :=
  Array.ofFn (n := c.size) (fun i => if i.val < N * N then MMf a b N i.val else c[i.val]!)

theorem EW_eq {α : Type} [Inhabited α] (r c : Array α) (f : Nat → α) (M : Nat) (h : EW r c f M) :
    r = Array.ofFn (n := c.size) (fun i => if i.val < M then f i.val else c[i.val]!) := by
  obtain ⟨hs, hd, hr⟩ := h
  apply Array.ext
  · simp [hs]
  · intro i h1 h2
    simp only [Array.getElem_ofFn]
    have e : r[i] = r[i]! := (getElem!_pos r i h1).symm
    rw [e]
    split
    · exact hd i ‹_›
    · exact hr i (by omega)

@[spec] theorem mat_mul_wp {T : Type} [Inhabited T] [Zero T] [Add T] [Mul T] (a b c : Array T) (N : Nat)
    (hc : N * N ≤ c.size) {Q : PostCond (Array T) PS} :
    ⦃fun t => Q.1 (mulRes a b c N) (t + 1 + N * (1 + N * (1 + N)))⦄ cp.mat_mul a b c N ⦃Q⦄ := by
  have W := wp_of_triple (Q := Q) (fun t0 => mat_mul_spec a b c N hc t0)
  apply Triple.iff.mpr
  intro s hs
  have := (Triple.iff.mp W) s
  apply this
  intro r t' ⟨hE, ht'⟩
  rw [EW_eq r c _ _ hE, ht']
  exact hs

open Proofs.MatPowMath in
/-- The `n × n` matrix of a flat `UInt64` vector, as natural numbers. -/
def toM (x : Array UInt64) (N : Nat) : Nat → Nat → Nat := fun i j => (x[i * N + j]!).toNat

section Pow
open Proofs.MatPowMath

theorem EqOn_trans {N : Nat} {A B C : Nat → Nat → Nat} (h1 : EqOn N A B) (h2 : EqOn N B C) : EqOn N A C :=
  fun i j hi hj => (h1 i j hi hj).trans (h2 i j hi hj)

theorem EqOn_symm {N : Nat} {A B : Nat → Nat → Nat} (h : EqOn N A B) : EqOn N B A :=
  fun i j hi hj => (h i j hi hj).symm

theorem EqOn_refl (N : Nat) (A : Nat → Nat → Nat) : EqOn N A A := fun _ _ _ _ => rfl

theorem toM_bd (x : Array UInt64) (N : Nat) : Bd N (toM x N) := fun i j _ _ => by
  simp only [toM]; exact UInt64.toNat_lt _

theorem MM_toNat (x y : Array UInt64) (N i j k : Nat) :
    (MM x y N i j k).toNat = MatPowMath.Sum k (fun t => toM x N i t * toM y N t j) % M64 := by
  induction k with
  | zero => simp [MM, MatPowMath.Sum]
  | succ k ih =>
    rw [MM_succ, Sum_succ, UInt64.toNat_add, UInt64.toNat_mul, ih]
    simp only [toM, M64]
    rw [show (2 : Nat) ^ 64 = 18446744073709551616 by norm_num, Nat.add_mod_mod, Nat.mod_add_mod]

/-- `mulRes` holds the product `mulF` in its first `N × N` entries. -/
theorem toM_mulRes (x y c : Array UInt64) (N : Nat) (hc : N * N ≤ c.size) :
    EqOn N (toM (mulRes x y c N) N) (mulF N (toM x N) (toM y N)) := by
  intro i j hi hj
  have hL := idx_lt N i j hi hj
  obtain ⟨hdv, hmd⟩ := div_mod_idx N i j hj
  simp only [toM, mulRes]
  rw [getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn, if_pos hL]
  simp only [MMf, hdv, hmd]
  rw [MM_toNat]; rfl

/-- A copied vector holds the same matrix. -/
theorem toM_copy (p d s : Array UInt64) (N : Nat) (h : EW p d (fun i => s[i]!) (N * N)) :
    EqOn N (toM p N) (toM s N) := by
  intro i j hi hj
  simp only [toM]; rw [h.2.1 _ (idx_lt N i j hi hj)]

theorem PW_sq (N : Nat) (Y : Nat → Nat → Nat) : ∀ k, EqOn N (PW N (mulF N Y Y) k) (PW N Y (2 * k)) := by
  intro k
  induction k with
  | zero => exact EqOn_refl N _
  | succ k ih =>
    show EqOn N (mulF N (PW N (mulF N Y Y) k) (mulF N Y Y)) (PW N Y (2 * k + 2))
    have e : PW N Y (2 * k + 2) = mulF N (mulF N (PW N Y (2 * k)) Y) Y := rfl
    rw [e, mulF_assoc]
    exact mulF_congr N _ _ _ _ ih (EqOn_refl N _)

theorem PW_congr (N : Nat) (Y Y' : Nat → Nat → Nat) (h : EqOn N Y' Y) : ∀ k, EqOn N (PW N Y' k) (PW N Y k) := by
  intro k
  induction k with
  | zero => exact EqOn_refl N _
  | succ k ih => exact mulF_congr N _ _ _ _ ih h

/-- One round of the binary powering keeps `R * Y^e`. -/
theorem pow_round (N : Nat) (R Y T : Nat → Nat → Nat) (hYb : Bd N Y) (e : Nat)
    (h : EqOn N (mulF N R (PW N Y e)) T)
    (R' Y' : Nat → Nat → Nat) (hY : EqOn N Y' (mulF N Y Y))
    (hR : (e % 2 = 1 → EqOn N R' (mulF N R Y)) ∧ (e % 2 ≠ 1 → EqOn N R' R)) :
    EqOn N (mulF N R' (PW N Y' (e / 2))) T := by
  set k := e / 2
  have hPY : EqOn N (PW N Y' k) (PW N Y (2 * k)) := by
    have : ∀ k, EqOn N (PW N Y' k) (PW N (mulF N Y Y) k) := by
      intro k
      induction k with
      | zero => exact EqOn_refl N _
      | succ k ih => exact mulF_congr N _ _ _ _ ih hY
    exact EqOn_trans (this _) (PW_sq N Y _)
  by_cases ho : e % 2 = 1
  · have he : e = 2 * k + 1 := by omega
    have h1 : EqOn N (PW N Y e) (mulF N Y (PW N Y (2 * k))) := by
      have hadd := PW_add N Y 1 (2 * k)
      rw [show 1 + 2 * k = e by omega] at hadd
      refine EqOn_trans hadd (mulF_congr N _ _ _ _ ?_ (EqOn_refl N _))
      exact mulF_one_left N Y hYb
    refine EqOn_trans (mulF_congr N _ _ _ _ (hR.1 ho) hPY) ?_
    rw [mulF_assoc]
    exact EqOn_trans (mulF_congr N _ _ _ _ (EqOn_refl N R) (EqOn_symm h1)) h
  · have he : e = 2 * k := by omega
    refine EqOn_trans (mulF_congr N _ _ _ _ (hR.2 ho) hPY) ?_
    rw [← he]; exact h

end Pow

/-- The ticks of one `mat_mul`. -/
abbrev Kmm (N : Nat) : Nat := 1 + N * (1 + N * (1 + N))

/-- The identity written so far by the diagonal loop: rows `< i`. -/
def Dg (N i idx : Nat) : UInt64 := if idx / N = idx % N ∧ idx / N < i then 1 else 0

theorem mulRes_size {T : Type} [Inhabited T] [Zero T] [Add T] [Mul T] (a b c : Array T) (N : Nat) :
    (mulRes a b c N).size = c.size := by simp [mulRes]

theorem diag_step (b r : Array UInt64) (N : Nat) (hr : N * N ≤ r.size) (pref suff : List Int) (c : Int)
    (hrg : range 0 (N : Int) = pref ++ c :: suff)
    (h : b.size = r.size ∧ (∀ idx, idx < N * N → b[idx]! = Dg N pref.length idx)) :
    (set b (c * N + c) 1).size = r.size ∧ ∀ idx, idx < N * N → (set b (c * N + c) 1)[idx]! = Dg N (pref.length + 1) idx := by
  obtain ⟨rfl, hl⟩ := cur_eq hrg
  have hL : pref.length < N := by exact_mod_cast hl
  obtain ⟨hs, he⟩ := h
  have e : (pref.length : Int) * N + pref.length = ((pref.length * N + pref.length : Nat) : Int) := by push_cast; ring
  have hlt := idx_lt N _ _ hL hL
  rw [e]
  refine ⟨by simp [hs], fun idx hidx => ?_⟩
  rw [getElemBang_set _ _ _ _ (by simp; omega), Int.toNat_natCast]
  have hdm := Nat.div_add_mod idx N
  by_cases hk : idx = pref.length * N + pref.length
  · subst hk
    obtain ⟨h1, h2⟩ := div_mod_idx N pref.length pref.length hL
    simp [Dg, h1, h2]
  · rw [if_neg hk, he idx hidx]
    simp only [Dg]
    have hmod : idx % N < N := Nat.mod_lt _ (by omega)
    by_cases hq : idx / N = idx % N ∧ idx / N = pref.length
    · exfalso; apply hk
      have h2 : idx % N = pref.length := by omega
      rw [← hdm, Nat.mul_comm, hq.2, h2]
    · congr 1
      apply propext
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩

theorem toM_diag (r0 r : Array UInt64) (N : Nat) (hr : N * N ≤ r0.size)
    (h : r.size = r0.size ∧ ∀ idx, idx < N * N → r[idx]! = Dg N N idx) : Proofs.MatPowMath.EqOn N (toM r N) Proofs.MatPowMath.Idm := by
  intro i j hi hj
  obtain ⟨h1, h2⟩ := div_mod_idx N i j hj
  simp only [toM, Proofs.MatPowMath.Idm]
  rw [h.2 _ (idx_lt N i j hi hj)]
  simp only [Dg, h1, h2]
  by_cases hij : i = j
  · subst hij; simp [hi]
  · simp [hij]

theorem bw_half (e : UInt64) (h : ¬e = 0) : bitWidth (e.toNat / 2) + 1 = bitWidth e.toNat := by
  have : 0 < e.toNat := by
    rcases Nat.eq_zero_or_pos e.toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) h
    · exact h0
  exact bitWidth_div_two _ this

theorem half_lt (e : UInt64) (h : ¬e = 0) : e.toNat / 2 < e.toNat := by
  have : 0 < e.toNat := by
    rcases Nat.eq_zero_or_pos e.toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) h
    · exact h0
  omega

open Proofs.MatPowMath in
theorem mat_pow_spec (a r y t : Array UInt64) (N : Nat) (e : UInt64) (ha : N * N ≤ a.size) (hr : N * N ≤ r.size)
    (hy : N * N ≤ y.size) (ht : N * N ≤ t.size) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.mat_pow a r y t N e
    ⦃⇓ res c => ⌜res.1.size = r.size ∧ Proofs.MatPowMath.EqOn N (toM res.1 N) (Proofs.MatPowMath.PW N (toM a N) e.toNat) ∧
      c ≤ t0 + 1 + N * N + N * N + N + (1 + 2 * (Kmm N + N * N)) * bitWidth e.toNat + 1⌝⦄ := by
  mvcgen [cp.mat_pow]
  case inv1 => exact ⇓⟨xs, p⟩ c => ⌜EW p y (fun i => a[i]!) xs.prefix.length ∧ c = t0 + 1 + xs.prefix.length⌝
  case inv2 => exact ⇓⟨xs, p⟩ c => ⌜EW p r (fun _ => 0) xs.prefix.length ∧ c = t0 + 1 + N * N + xs.prefix.length⌝
  case inv3 => exact ⇓⟨xs, p⟩ c => ⌜p.size = r.size ∧ (∀ idx, idx < N * N → p[idx]! = Dg N xs.prefix.length idx) ∧
    c = t0 + 1 + N * N + N * N + xs.prefix.length⌝
  case vc7.inv =>
    exact ⟨fun ⟨r', y', t', e'⟩ c => ⌜r'.size = r.size ∧ y'.size = y.size ∧ N * N ≤ t'.size ∧
        Proofs.MatPowMath.EqOn N (Proofs.MatPowMath.mulF N (toM r' N) (Proofs.MatPowMath.PW N (toM y' N) e'.toNat))
          (Proofs.MatPowMath.PW N (toM a N) e.toNat) ∧
        c + (1 + 2 * (Kmm N + N * N)) * bitWidth e'.toNat ≤
          t0 + 1 + N * N + N * N + N + (1 + 2 * (Kmm N + N * N)) * bitWidth e.toNat⌝,
      fun ⟨r', _, _, _⟩ c => ⌜r'.size = r.size ∧ Proofs.MatPowMath.EqOn N (toM r' N) (Proofs.MatPowMath.PW N (toM a N) e.toNat) ∧
        c ≤ t0 + 1 + N * N + N * N + N + (1 + 2 * (Kmm N + N * N)) * bitWidth e.toNat + 1⌝,
      fun ⟨_, _, _, e'⟩ => e'.toNat⟩
  case inv4 =>
    rename_i ob _ _ _ _ _ _ so _ _ _ _ _
    exact ⇓⟨xs, p⟩ c => ⌜EW p ob.1 (fun i => (mulRes ob.1 ob.2.1 ob.2.2.1 N)[i]!) xs.prefix.length ∧
      c = so + 1 + Kmm N + xs.prefix.length⌝
  case inv5 =>
    rename_i ob _ _ _ _ _ _ _ _ _ _ _ _ _ s5 _ _
    exact ⇓⟨xs, p⟩ c => ⌜EW p ob.2.1 (fun i => (mulRes ob.2.1 ob.2.1 (mulRes ob.1 ob.2.1 ob.2.2.1 N) N)[i]!)
      xs.prefix.length ∧ c = s5 + Kmm N + xs.prefix.length⌝
  case inv6 =>
    rename_i ob _ _ _ _ _ _ so _ _ _ _ _
    exact ⇓⟨xs, p⟩ c => ⌜EW p ob.2.1 (fun i => (mulRes ob.2.1 ob.2.1 ob.2.2.1 N)[i]!) xs.prefix.length ∧
      c = so + 1 + Kmm N + xs.prefix.length⌝
  all_goals simp +zetaDelta [fuel] at *
  -- the copy and zero loops
  all_goals (try (
                  obtain ⟨hE, hc⟩ := ‹EW _ _ _ _ ∧ _›
                  obtain ⟨rfl, -⟩ := cur_eq ‹range 0 ((N : Int) * N) = _ ++ _ :: _›
                  try (obtain ⟨hs1, hs2, hs3, -, -⟩ := ‹_ = r.size ∧ _ = y.size ∧ _›)
                  refine ⟨ew_vc _ _ _ N (by first | exact hy | exact hr | exact (hs2 ▸ hy) | exact (hs1 ▸ hr)) _ _ ‹_› hE _ (by first | rfl | simp only [get_eq, Int.toNat_natCast]), by omega⟩))
  -- the loops start with nothing written
  all_goals (try (refine ⟨⟨rfl, fun i hi => absurd hi (by omega), fun i _ => rfl⟩, by first | omega | (simp only [Kmm]; omega)⟩))
  -- sizes for the calls of mat_mul
  all_goals (try (obtain ⟨-, -, hs3, -, -⟩ := ‹_ = r.size ∧ _ = y.size ∧ _›
                  first
                  | exact hs3
                  | (rw [mulRes_size]; exact hs3)
                  | (rw [mulRes_size, mulRes_size]; exact hs3)))
  · obtain ⟨-, hc⟩ := ‹EW _ y _ _ ∧ _›
    rw [range_length, Int.sub_zero, nn_toNat] at hc
    exact ⟨⟨rfl, fun i hi => absurd hi (by omega), fun i _ => rfl⟩, hc⟩
  · obtain ⟨hs, he, hc⟩ := ‹_ = r.size ∧ (∀ idx, idx < N * N → _ = Dg N _ idx) ∧ _›
    have D := diag_step _ r N hr _ _ _ ‹range 0 _ = _ ++ _ :: _› ⟨hs, he⟩
    exact ⟨by simpa using D.1, D.2, by omega⟩
  · obtain ⟨hE, hc⟩ := ‹EW _ r _ _ ∧ _›
    rw [range_length, Int.sub_zero, nn_toNat] at hE hc
    refine ⟨hE.1, fun idx hidx => ?_, by omega⟩
    rw [hE.2.1 idx hidx]; simp [Dg]
  -- the loop of the powering: end and start
  case vc8.step.isTrue =>
    obtain ⟨hs1, -, -, hq, hc⟩ := ‹_ = r.size ∧ _ = y.size ∧ _›
    have he := ‹_ = (0 : UInt64)›
    rw [he] at hq hc
    simp only [UInt64.toNat_zero, bitWidth_zero, Nat.mul_zero, Nat.add_zero] at hq hc
    refine ⟨hs1, EqOn_trans (EqOn_symm (mulF_one_right N _ (toM_bd _ N))) hq, by omega⟩
  case vc23.post.success.post.success.post.success.pre =>
    obtain ⟨hs, hd, hc⟩ := ‹_ = r.size ∧ (∀ idx, idx < N * N → _ = Dg N N idx) ∧ _›
    obtain ⟨hE, -⟩ := ‹EW _ y _ _ ∧ _›
    rw [range_length, Int.sub_zero, nn_toNat] at hE
    have hR := toM_diag r _ N hr ⟨hs, hd⟩
    have hY := toM_copy _ y a N hE
    refine ⟨⟨hs, hE.1, ht, ?_, by omega⟩, UInt64.toNat_lt _⟩
    refine EqOn_trans (mulF_congr N _ _ _ _ hR (PW_congr N _ _ hY _)) ?_
    exact mulF_one_left N _ (PW_bd N _ _)
  -- one round of the powering
  case vc15.step.isFalse.isTrue.post.success.post.success =>
    obtain ⟨hs1, hs2, hs3, hq, hc⟩ := ‹_ = r.size ∧ _ = y.size ∧ _›
    obtain ⟨hE1, hc1⟩ := ‹EW _ _ (fun i => (mulRes _ _ _ N)[i]!) _ ∧ _ = _ + 1 + _ + _›
    obtain ⟨hE2, hc2⟩ := ‹EW _ _ (fun i => (mulRes _ _ (mulRes _ _ _ N) N)[i]!) _ ∧ _›
    rw [range_length, Int.sub_zero, nn_toNat] at hE1 hc1 hE2 hc2
    have hne := ‹¬_ = (0 : UInt64)›
    have hodd : (‹Array UInt64 × Array UInt64 × Array UInt64 × UInt64›).2.2.2.toNat % 2 = 1 := by
      have := ‹_ % 2 = (1 : UInt64)›; rw [← UInt64.toNat_inj] at this; simpa using this
    have hR := EqOn_trans (toM_copy _ _ _ N hE1) (toM_mulRes _ _ _ N hs3)
    have hY := EqOn_trans (toM_copy _ _ _ N hE2) (toM_mulRes _ _ _ N (by rw [mulRes_size]; exact hs3))
    have hbw := bw_half _ hne
    refine ⟨⟨by rw [hE1.1]; exact hs1, by rw [hE2.1]; exact hs2, by rw [mulRes_size, mulRes_size]; exact hs3,
      pow_round N _ _ _ (toM_bd _ N) _ hq _ _ hY ⟨fun _ => hR, fun h => absurd hodd h⟩, ?_⟩, half_lt _ hne⟩
    rw [← hbw, Nat.mul_succ] at hc; omega
  case vc21.step.isFalse.isFalse.post.success =>
    obtain ⟨hs1, hs2, hs3, hq, hc⟩ := ‹_ = r.size ∧ _ = y.size ∧ _›
    obtain ⟨hE2, hc2⟩ := ‹EW _ _ (fun i => (mulRes _ _ _ N)[i]!) _ ∧ _›
    rw [range_length, Int.sub_zero, nn_toNat] at hE2 hc2
    have hne := ‹¬_ = (0 : UInt64)›
    have hev : ¬(‹Array UInt64 × Array UInt64 × Array UInt64 × UInt64›).2.2.2.toNat % 2 = 1 := by
      have := ‹¬_ % 2 = (1 : UInt64)›; rw [← UInt64.toNat_inj] at this; simpa using this
    have hY := EqOn_trans (toM_copy _ _ _ N hE2) (toM_mulRes _ _ _ N hs3)
    have hbw := bw_half _ hne
    refine ⟨⟨hs1, by rw [hE2.1]; exact hs2, by rw [mulRes_size]; exact hs3,
      pow_round N _ _ _ (toM_bd _ N) _ hq _ _ hY ⟨fun h => absurd h hev, fun _ => EqOn_refl N _⟩, ?_⟩, half_lt _ hne⟩
    rw [← hbw, Nat.mul_succ] at hc; omega
  all_goals exact ‹_ ∧ EqOn _ _ _ ∧ _›

end Proofs.Cpp.SquareMatrix
