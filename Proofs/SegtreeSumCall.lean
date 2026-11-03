import Mathlib.Algebra.Order.Group.Nat
import Proofs.LowerBoundIndexCall
import Proofs.GenState
import Proofs.Generated.SegtreeSum

namespace Proofs.SegtreeSumCall

abbrev M64 : Nat := 18446744073709551616

/-- `rsum v a k` is the sum of the `k` entries of `v` starting at `a` (missing entries count as 0). -/
def rsum (v : List Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | a, k+1 => v.getD a 0 + rsum v (a+1) k

/-- The tree layout: `N` leaves `v[N .. 2N)` and every inner node holds the sum of its two children (mod 2^64). -/
def TInv (v : List Nat) (N : Nat) : Prop :=
  0 < N ∧ v.length = 2 * N ∧
    ∀ i, 1 ≤ i → i < N → v.getD i 0 % M64 = (v.getD (2*i) 0 + v.getD (2*i+1) 0) % M64

theorem rsum_add (v : List Nat) : ∀ (a k1 k2 : Nat), rsum v a (k1 + k2) = rsum v a k1 + rsum v (a + k1) k2 := by
  intro a k1
  induction k1 generalizing a with
  | zero => intro k2; simp [rsum]
  | succ k ih =>
    intro k2
    have : k + 1 + k2 = (k + k2) + 1 := by omega
    rw [this, rsum, ih (a+1) k2, rsum]
    have : a + 1 + k = a + (k + 1) := by omega
    rw [this]; omega

theorem rsum_pairs (v : List Nat) (N : Nat) (h : TInv v N) :
    ∀ (k a : Nat), 1 ≤ a → a + k ≤ N → rsum v (2*a) (2*k) % M64 = rsum v a k % M64 := by
  intro k
  induction k with
  | zero => intro a _ _; simp [rsum]
  | succ k ih =>
    intro a ha hk
    have e : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    have e2 : 2 * (k + 1) = 2 + 2 * k := by omega
    rw [e2, rsum_add v (2*a) 2 (2*k)]
    have r2 : rsum v (2*a) 2 = v.getD (2*a) 0 + v.getD (2*a+1) 0 := by simp [rsum]
    have r1 : rsum v a (k+1) = v.getD a 0 + rsum v (a+1) k := by rw [rsum]
    have ihh := ih (a+1) (by omega) (by omega)
    have hnode := h.2.2 a ha (by omega)
    have e3 : 2 * a + 2 = 2 * (a + 1) := by omega
    rw [r2, e3, r1]
    have := Nat.add_mod (v.getD (2*a) 0 + v.getD (2*a+1) 0) (rsum v (2*(a+1)) (2*k)) M64
    have := Nat.add_mod (v.getD a 0) (rsum v (a+1) k) M64
    rw [Nat.add_mod (v.getD (2*a) 0 + v.getD (2*a+1) 0) (rsum v (2*(a+1)) (2*k)) M64, ← hnode, ihh,
      ← Nat.add_mod]

/-- The loop state of `segtree_sum_product` after one iteration. -/
def pl1 (l : Nat) : Nat := if l % 2 = 1 then l + 1 else l
def pr1 (r : Nat) : Nat := if r % 2 = 1 then r - 1 else r
def pleft (v : List Nat) (l left : Nat) : Nat := if l % 2 = 1 then (left + v.getD l 0) % M64 else left
def pright (v : List Nat) (r right : Nat) : Nat := if r % 2 = 1 then (right + v.getD (r - 1) 0) % M64 else right

/-- The invariant of the product loop: what is still to be added equals the node sum over `[l, r)`. -/
def PInv (v : List Nat) (N T : Nat) (l r left right : Nat) : Prop :=
  1 ≤ l ∧ r ≤ 2 * N ∧ left < M64 ∧ right < M64 ∧ (left + right + rsum v l (r - l)) % M64 = T % M64

theorem prod_step (v : List Nat) (N T : Nat) (h : TInv v N) (l r left right : Nat) (hI : PInv v N T l r left right)
    (hlr : l < r) :
    PInv v N T (pl1 l / 2) (pr1 r / 2) (pleft v l left) (pright v r right) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hI
  have hl1 : 2 ≤ pl1 l := by unfold pl1; split <;> omega
  have hl1e : pl1 l % 2 = 0 := by unfold pl1; split <;> omega
  have hr1e : pr1 r % 2 = 0 := by unfold pr1; split <;> omega
  have hlr1 : pl1 l ≤ pr1 r := by unfold pl1 pr1; split <;> split <;> omega
  have hr1le : pr1 r ≤ r := by unfold pr1; split <;> omega
  have hl1ge : l ≤ pl1 l := by unfold pl1; split <;> omega
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · unfold pleft; split
    · exact Nat.mod_lt _ (by decide)
    · exact h3
  · unfold pright; split
    · exact Nat.mod_lt _ (by decide)
    · exact h4
  · -- split the node sum
    have hsplit : rsum v l (r - l) = (if l % 2 = 1 then v.getD l 0 else 0) + rsum v (pl1 l) (pr1 r - pl1 l) +
        (if r % 2 = 1 then v.getD (r - 1) 0 else 0) := by
      rcases Nat.mod_two_eq_zero_or_one l with hl | hl <;> rcases Nat.mod_two_eq_zero_or_one r with hr | hr
      · simp [pl1, pr1, hl, hr]
      · -- l even, r odd
        have e : r - l = (r - 1 - l) + 1 := by omega
        have hp1 : pl1 l = l := by simp [pl1, hl]
        have hp2 : pr1 r = r - 1 := by simp [pr1, hr]
        rw [hp1, hp2, e, rsum_add]
        have : l + (r - 1 - l) = r - 1 := by omega
        rw [this]
        simp [hl, hr, rsum]
      · -- l odd, r even
        have e : r - l = (r - (l + 1)) + 1 := by omega
        have hp1 : pl1 l = l + 1 := by simp [pl1, hl]
        have hp2 : pr1 r = r := by simp [pr1, hr]
        rw [hp1, hp2, e, rsum]
        simp [hl, hr]
      · -- both odd
        have e : r - l = ((r - 1 - (l + 1)) + 1) + 1 := by omega
        have hp1 : pl1 l = l + 1 := by simp [pl1, hl]
        have hp2 : pr1 r = r - 1 := by simp [pr1, hr]
        rw [hp1, hp2, e, rsum, rsum_add]
        have : l + 1 + (r - 1 - (l + 1)) = r - 1 := by omega
        rw [this]
        have e2 : r - 1 - (l + 1) = r - 1 - (l + 1) := rfl
        simp [hl, hr, rsum]
        omega
    have hpair := rsum_pairs v N h ((pr1 r - pl1 l) / 2) (pl1 l / 2) (by omega) (by omega)
    have e1 : 2 * (pl1 l / 2) = pl1 l := by omega
    have e2 : 2 * ((pr1 r - pl1 l) / 2) = pr1 r - pl1 l := by omega
    rw [e1, e2] at hpair
    have e3 : pr1 r / 2 - pl1 l / 2 = (pr1 r - pl1 l) / 2 := by omega
    rw [e3]
    rw [hsplit] at h5
    unfold pleft pright
    simp only [M64] at *
    split_ifs at * <;> omega

theorem getD_setE (v : List Nat) (i x j : Nat) :
    (v.set i x).getD j 0 = if j = i ∧ i < v.length then x else v.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : i = j
  · subst h
    by_cases hl : i < v.length
    · simp [hl]
    · simp [hl]
  · have : ¬ (j = i) := fun e => h e.symm
    simp [h, this]

/-- `j` lies on the path from `i` to the root. -/
def Anc (i j : Nat) : Prop := ∃ t, j = i / 2 ^ t

theorem anc_self (i : Nat) : Anc i i := ⟨0, by simp⟩

theorem anc_step (i j : Nat) : Anc i j ↔ j = i ∨ Anc (i / 2) j := by
  constructor
  · rintro ⟨t, ht⟩
    cases t with
    | zero => left; simpa using ht
    | succ s =>
      right
      refine ⟨s, ?_⟩
      rw [ht, Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]
  · rintro (h | ⟨s, hs⟩)
    · exact ⟨0, by simpa using h⟩
    · refine ⟨s + 1, ?_⟩
      rw [hs, Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

/-- Every inner node off the path from `i` to the root holds the sum of its children. -/
def SInv (v : List Nat) (N i : Nat) : Prop :=
  ∀ j, 1 ≤ j → j < N → ¬ Anc i j → v.getD j 0 % M64 = (v.getD (2*j) 0 + v.getD (2*j+1) 0) % M64

theorem sinv_step (v : List Nat) (N i : Nat) (h : SInv v N i) (hi1 : 1 ≤ i) (hiN : i < N) (hlen : v.length = 2 * N) :
    SInv (v.set i ((v.getD (2*i) 0 + v.getD (2*i+1) 0) % M64)) N (i / 2) := by
  intro j hj1 hjN hna
  have hil : i < v.length := by omega
  by_cases hji : j = i
  · subst hji
    rw [getD_setE, getD_setE, getD_setE]
    have a0 : (j = j ∧ j < v.length) := ⟨rfl, hil⟩
    have a1 : ¬ (2 * j = j ∧ j < v.length) := by omega
    have a2 : ¬ (2 * j + 1 = j ∧ j < v.length) := by omega
    rw [if_pos a0, if_neg a1, if_neg a2, Nat.mod_mod]
  · have hna' : ¬ Anc i j := by
      intro ha
      rcases (anc_step i j).mp ha with e | e
      · exact hji e
      · exact hna e
    have hold := h j hj1 hjN hna'
    have c1 : ¬ (2 * j = i) := by
      intro e; apply hna; exact ⟨0, by omega⟩
    have c2 : ¬ (2 * j + 1 = i) := by
      intro e; apply hna; exact ⟨0, by omega⟩
    rw [getD_setE, getD_setE, getD_setE]
    have b0 : ¬ (j = i ∧ i < v.length) := fun hh => hji hh.1
    have b1 : ¬ (2 * j = i ∧ i < v.length) := fun hh => c1 hh.1
    have b2 : ¬ (2 * j + 1 = i ∧ i < v.length) := fun hh => c2 hh.1
    rw [if_neg b0, if_neg b1, if_neg b2]
    exact hold

theorem sinv_zero (v : List Nat) (N : Nat) (h : SInv v N 0) :
    ∀ j, 1 ≤ j → j < N → v.getD j 0 % M64 = (v.getD (2*j) 0 + v.getD (2*j+1) 0) % M64 := by
  intro j hj1 hjN
  apply h j hj1 hjN
  rintro ⟨t, ht⟩
  simp at ht
  omega

theorem sinv_init (v : List Nat) (N p val : Nat) (hT : TInv v N) (hp1 : N ≤ p) (hp2 : p < 2 * N) :
    SInv (v.set p val) N (p / 2) := by
  intro j hj1 hjN hna
  have hpl : p < v.length := by have := hT.2.1; omega
  have c0 : ¬ (j = p) := by omega
  have c1 : ¬ (2 * j = p) := by
    intro e; apply hna; exact ⟨0, by omega⟩
  have c2 : ¬ (2 * j + 1 = p) := by
    intro e; apply hna; exact ⟨0, by omega⟩
  rw [getD_setE, getD_setE, getD_setE]
  have b0 : ¬ (j = p ∧ p < v.length) := fun hh => c0 hh.1
  have b1 : ¬ (2 * j = p ∧ p < v.length) := fun hh => c1 hh.1
  have b2 : ¬ (2 * j + 1 = p ∧ p < v.length) := fun hh => c2 hh.1
  rw [if_neg b0, if_neg b1, if_neg b2]
  exact hT.2.2 j hj1 hjN


section Program
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.StraightLine Proofs.Mod61Body Proofs.VecExpr Proofs.VecStraight Proofs.VecCall Proofs.VecKit
open Proofs.CppNestedFacts Proofs.IntSim Proofs.ScalarCall Proofs.VecWrite Proofs.VecWriteCall Proofs.VecKitW
open Proofs.QuotientSearch Proofs.VectorFillCall Proofs.PrefixSumsCall
open Proofs.VectorSumCall (conv_signed i32_valid)
open Proofs.CppState (Cell)
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.FenwickCall (pexecW_branch_trueB pexecW_branch_falseB)
open Proofs.LowerBoundIndexCall (validN env_gen stepsL stepsL_log stepsL_succ stepsL_mono)
open Proofs.GenState

abbrev ci (x : Nat) : Cell := ⟨i32, (x : Int)⟩
abbrev cu (x : Nat) : Cell := ⟨u64, (x : Int)⟩
/-- The cells of the product loop: `l`, `r`, `n_node`, `left`, `right`. -/
abbrev L5 (l r n a b : Nat) : List Cell := [ci l, ci r, ci n, cu a, cu b]
abbrev stP (P : List Cell) (l r n a b : Nat) : PS := gS P (L5 l r n a b)

abbrev rdL : NExpr := .read u64 (.local 0) (.cast u64 (.variable i32 1))
abbrev rdR : NExpr := .read u64 (.local 0) (.cast u64 (.variable i32 2))
abbrev c1E : NExpr := .binary bT .ne (.divrem i32 true (.variable i32 1) (.literal i32 2)) (.literal i32 0)
abbrev c2E : NExpr := .binary bT .ne (.divrem i32 true (.variable i32 2) (.literal i32 2)) (.literal i32 0)
abbrev accL : NStmt := .assign 4 u64 (.binary u64 .add (.variable u64 4) rdL)
abbrev incL : NStmt := .assign 1 i32 (.binary i32 .add (.variable i32 1) (.literal i32 1))
abbrev decR : NStmt := .assign 2 i32 (.binary i32 .sub (.variable i32 2) (.literal i32 1))
abbrev accR : NStmt := .assign 5 u64 (.binary u64 .add (.variable u64 5) rdR)
abbrev yes1 : Command := .sequence (.scope (.sequence (.primitive accL) (.sequence (.primitive incL) (.primitive .skip)))) (.primitive .skip)
abbrev yes2 : Command := .sequence (.scope (.sequence (.primitive decR) (.sequence (.primitive accR) (.primitive .skip)))) (.primitive .skip)
abbrev br1 : Command := .branch c1E yes1 (.primitive .skip)
abbrev br2 : Command := .branch c2E yes2 (.primitive .skip)
abbrev halveL : NStmt := .assign 1 i32 (.divrem i32 false (.variable i32 1) (.literal i32 2))
abbrev halveR : NStmt := .assign 2 i32 (.divrem i32 false (.variable i32 2) (.literal i32 2))
abbrev loopBodyP : Command := .sequence (.scope (.sequence br1 (.sequence br2 (.sequence (.primitive halveL)
  (.sequence (.primitive halveR) (.primitive .skip)))))) (.primitive .skip)
abbrev loopCondP : NExpr := .binary bT .lt (.variable i32 1) (.variable i32 2)
abbrev loopCP : Command := .whileLoop loopCondP loopBodyP
abbrev declN : NStmt := .declare i32 true (.cast i32 (.size (.integer u64) (.local 0)))
abbrev setN : NStmt := .assign 3 i32 (.divrem i32 false (.variable i32 3) (.literal i32 2))
abbrev declZ : NStmt := .declare u64 true (.cast u64 (.literal i32 0))
abbrev setL0 : NStmt := .assign 1 i32 (.binary i32 .add (.variable i32 1) (.variable i32 3))
abbrev setR0 : NStmt := .assign 2 i32 (.binary i32 .add (.variable i32 2) (.variable i32 3))
abbrev retP : NStmt := .ret (.binary u64 .add (.variable u64 4) (.variable u64 5))
abbrev bodyCmdP : Command := .sequence (.primitive declN) (.sequence (.primitive setN) (.sequence (.primitive declZ)
  (.sequence (.primitive declZ) (.sequence (.primitive setL0) (.sequence (.primitive setR0) (.sequence loopCP
    (.sequence (.primitive retP) (.primitive .skip))))))))

theorem body_eqP : Proofs.SegtreeSumInstance.segtree_sum_product_std_vector_unsigned_long_long.body = bodyCmdP := rfl

theorem envP1 (P : List Cell) (l r n a b : Nat) (h : l < 2147483648) : penv1 (stP P l r n a b) 1 i32 = some (l : Int) :=
  gS_env P (L5 l r n a b) 0 (ci l) rfl (validN l h)
theorem envP2 (P : List Cell) (l r n a b : Nat) (h : r < 2147483648) : penv1 (stP P l r n a b) 2 i32 = some (r : Int) :=
  gS_env P (L5 l r n a b) 1 (ci r) rfl (validN r h)
theorem envP3 (P : List Cell) (l r n a b : Nat) (h : n < 2147483648) : penv1 (stP P l r n a b) 3 i32 = some (n : Int) :=
  gS_env P (L5 l r n a b) 2 (ci n) rfl (validN n h)
theorem envP4 (P : List Cell) (l r n a b : Nat) (h : a < 18446744073709551616) : penv1 (stP P l r n a b) 4 u64 = some (a : Int) :=
  gS_env P (L5 l r n a b) 3 (cu a) rfl (u64_lt a h)
theorem envP5 (P : List Cell) (l r n a b : Nat) (h : b < 18446744073709551616) : penv1 (stP P l r n a b) 5 u64 = some (b : Int) :=
  gS_env P (L5 l r n a b) 4 (cu b) rfl (u64_lt b h)

theorem idxL (P : List Cell) (l r n a b : Nat) (h : l < 2147483648) :
    (NExpr.cast u64 (.variable i32 1)).denote (penv1 (stP P l r n a b)) = some (l : Int) := by
  rw [den_cast, den_variable, envP1 P l r n a b h, Option.bind_some, convert_u64]
  congr 1
  exact Int.emod_eq_of_lt (by omega) (by omega)

theorem idxR (P : List Cell) (l r n a b : Nat) (h : r < 2147483648) :
    (NExpr.cast u64 (.variable i32 2)).denote (penv1 (stP P l r n a b)) = some (r : Int) := by
  rw [den_cast, den_variable, envP2 P l r n a b h, Option.bind_some, convert_u64]
  congr 1
  exact Int.emod_eq_of_lt (by omega) (by omega)

theorem rdL_val (vec : List Int) (P : List Cell) (l r n a b : Nat) (xn : Nat) (h : l < 2147483648)
    (hx : vec[l]? = some (xn : Int)) (hxv : u64.valid (xn : Int) = true) :
    vdenL u64 vec (penv1 (stP P l r n a b)) rdL = some (xn : Int) := by
  have hrc : rdL.scalarOnly = false := rfl
  rw [vdenL_read _ _ _ _ _ hrc, if_pos ⟨rfl, rfl⟩, idxL P l r n a b h, Option.bind_some]
  unfold elemAtL
  rw [if_pos (Int.natCast_nonneg l), Int.toNat_natCast, hx, Option.bind_some, if_pos hxv]

theorem rdR_val (vec : List Int) (P : List Cell) (l r n a b : Nat) (xn : Nat) (h : r < 2147483648)
    (hx : vec[r]? = some (xn : Int)) (hxv : u64.valid (xn : Int) = true) :
    vdenL u64 vec (penv1 (stP P l r n a b)) rdR = some (xn : Int) := by
  have hrc : rdR.scalarOnly = false := rfl
  rw [vdenL_read _ _ _ _ _ hrc, if_pos ⟨rfl, rfl⟩, idxR P l r n a b h, Option.bind_some]
  unfold elemAtL
  rw [if_pos (Int.natCast_nonneg r), Int.toNat_natCast, hx, Option.bind_some, if_pos hxv]

theorem dr2_den (env : Nat → Ty → Option Int) (rem : Bool) (k l : Nat) (e : env k i32 = some (l : Int)) :
    (NExpr.divrem i32 rem (.variable i32 k) (.literal i32 2)).denote env = checkedDivRem i32 rem (l : Int) 2 := by
  rw [den_divrem, den_variable, e, den_literal, if_pos (show i32.valid 2 = true from rfl), Option.bind_some, Option.bind_some]

theorem rem2_val (l : Nat) (h : l < 2147483648) : checkedDivRem i32 true (l : Int) 2 = some ((l % 2 : Nat) : Int) := by
  unfold checkedDivRem
  have hq : (l : Int).tdiv 2 = ((l / 2 : Nat) : Int) := by
    rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]; omega
  have hr : (l : Int).tmod 2 = ((l % 2 : Nat) : Int) := by
    rw [Int.tmod_eq_emod_of_nonneg (by omega)]; omega
  have hvq : i32.valid (((l / 2 : Nat)) : Int) = true := validN _ (by omega)
  rw [hq, if_neg (by decide), if_neg (by simp only [hvq, Bool.not_true]; decide), hr]
  exact conv_signed i32 rfl rfl _ (validN _ (by omega))

theorem quo2_val (l : Nat) (h : l < 2147483648) : checkedDivRem i32 false (l : Int) 2 = some ((l / 2 : Nat) : Int) := by
  unfold checkedDivRem
  have hq : (l : Int).tdiv 2 = ((l / 2 : Nat) : Int) := by
    rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]; omega
  have hvq : i32.valid (((l / 2 : Nat)) : Int) = true := validN _ (by omega)
  rw [hq, if_neg (by decide), if_neg (by simp only [hvq, Bool.not_true]; decide)]
  exact conv_signed i32 rfl rfl _ hvq

theorem parity_val (k l : Nat) (h : l < 2147483648) :
    bT.convert (binaryValue .ne ((l % 2 : Nat) : Int) 0) = some (if l % 2 = 0 then 0 else 1) := by
  have : binaryValue .ne ((l % 2 : Nat) : Int) 0 = if l % 2 = 0 then 0 else 1 := by
    show (if (((l % 2 : Nat) : Int) != 0) = true then 1 else 0) = _
    by_cases hz : l % 2 = 0
    · simp [hz]
    · have : (((l % 2 : Nat) : Int) != 0) = true := by simp; omega
      rw [if_neg hz, if_pos this]
  rw [this]
  simp only [bT]; unfold Ty.convert
  by_cases hz : l % 2 = 0 <;> simp [hz]

theorem c1_val (vec : List Int) (P : List Cell) (l r n a b : Nat) (h : l < 2147483648) :
    vdenL u64 vec (penv1 (stP P l r n a b)) c1E = some (if l % 2 = 0 then 0 else 1) := by
  have hs : c1E.scalarOnly = true := rfl
  rw [vdenL_scalar _ _ _ _ hs, den_binary, dr2_den _ true 1 l (envP1 P l r n a b h), rem2_val l h, Option.bind_some,
    den_literal, if_pos (show i32.valid 0 = true from rfl), Option.bind_some]
  exact parity_val 0 l h

theorem c2_val (vec : List Int) (P : List Cell) (l r n a b : Nat) (h : r < 2147483648) :
    vdenL u64 vec (penv1 (stP P l r n a b)) c2E = some (if r % 2 = 0 then 0 else 1) := by
  have hs : c2E.scalarOnly = true := rfl
  rw [vdenL_scalar _ _ _ _ hs, den_binary, dr2_den _ true 2 r (envP2 P l r n a b h), rem2_val r h, Option.bind_some,
    den_literal, if_pos (show i32.valid 0 = true from rfl), Option.bind_some]
  exact parity_val 0 r h

theorem accL_val (vec : List Int) (P : List Cell) (l r n a b : Nat) (xn : Nat) (hl : l < 2147483648)
    (ha : a < 18446744073709551616) (hx : vec[l]? = some (xn : Int)) (hxv : u64.valid (xn : Int) = true) :
    vdenL u64 vec (penv1 (stP P l r n a b)) (.binary u64 .add (.variable u64 4) rdL) = some (((a + xn) % M64 : Nat) : Int) := by
  have hb : (NExpr.binary u64 .add (.variable u64 4) rdL).scalarOnly = false := rfl
  have hv : vdenL u64 vec (penv1 (stP P l r n a b)) (NExpr.variable u64 4) = some (a : Int) := by
    rw [vdenL_scalar _ _ _ _ rfl, den_variable]; exact envP4 P l r n a b ha
  rw [vdenL_binary _ _ _ _ _ _ _ hb, hv, rdL_val vec P l r n a b xn hl hx hxv, Option.bind_some, Option.bind_some]
  have : binaryValue .add (a : Int) (xn : Int) = ((a + xn : Nat) : Int) := by
    show (a : Int) + (xn : Int) = _; push_cast; rfl
  rw [this, convert_u64]
  congr 1

theorem accR_val (vec : List Int) (P : List Cell) (l r n a b : Nat) (xn : Nat) (hr : r < 2147483648)
    (hb : b < 18446744073709551616) (hx : vec[r]? = some (xn : Int)) (hxv : u64.valid (xn : Int) = true) :
    vdenL u64 vec (penv1 (stP P l r n a b)) (.binary u64 .add (.variable u64 5) rdR) = some (((b + xn) % M64 : Nat) : Int) := by
  have hbs : (NExpr.binary u64 .add (.variable u64 5) rdR).scalarOnly = false := rfl
  have hv : vdenL u64 vec (penv1 (stP P l r n a b)) (NExpr.variable u64 5) = some (b : Int) := by
    rw [vdenL_scalar _ _ _ _ rfl, den_variable]; exact envP5 P l r n a b hb
  rw [vdenL_binary _ _ _ _ _ _ _ hbs, hv, rdR_val vec P l r n a b xn hr hx hxv, Option.bind_some, Option.bind_some]
  have : binaryValue .add (b : Int) (xn : Int) = ((b + xn : Nat) : Int) := by
    show (b : Int) + (xn : Int) = _; push_cast; rfl
  rw [this, convert_u64]
  congr 1

theorem incL_val (vec : List Int) (P : List Cell) (l r n a b : Nat) (h : l + 1 < 2147483648) :
    vdenL u64 vec (penv1 (stP P l r n a b)) (.binary i32 .add (.variable i32 1) (.literal i32 1)) = some ((l + 1 : Nat) : Int) := by
  have hs : (NExpr.binary i32 .add (.variable i32 1) (.literal i32 1)).scalarOnly = true := rfl
  rw [vdenL_scalar _ _ _ _ hs, den_binary, den_variable, envP1 P l r n a b (by omega), Option.bind_some,
    den_literal, if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
  have : binaryValue .add (l : Int) 1 = ((l + 1 : Nat) : Int) := by
    show (l : Int) + 1 = _; push_cast; rfl
  rw [this]
  exact conv_signed i32 rfl rfl _ (validN _ h)

theorem decR_val (vec : List Int) (P : List Cell) (l r n a b : Nat) (h : r < 2147483648) (h1 : 1 ≤ r) :
    vdenL u64 vec (penv1 (stP P l r n a b)) (.binary i32 .sub (.variable i32 2) (.literal i32 1)) = some ((r - 1 : Nat) : Int) := by
  have hs : (NExpr.binary i32 .sub (.variable i32 2) (.literal i32 1)).scalarOnly = true := rfl
  rw [vdenL_scalar _ _ _ _ hs, den_binary, den_variable, envP2 P l r n a b h, Option.bind_some,
    den_literal, if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
  have : binaryValue .sub (r : Int) 1 = ((r - 1 : Nat) : Int) := by
    show (r : Int) - 1 = _; omega
  rw [this]
  exact conv_signed i32 rfl rfl _ (validN _ (by omega))

theorem halveL_val (vec : List Int) (P : List Cell) (l r n a b : Nat) (h : l < 2147483648) :
    vdenL u64 vec (penv1 (stP P l r n a b)) (.divrem i32 false (.variable i32 1) (.literal i32 2)) = some ((l / 2 : Nat) : Int) := by
  have hs : (NExpr.divrem i32 false (.variable i32 1) (.literal i32 2)).scalarOnly = true := rfl
  rw [vdenL_scalar _ _ _ _ hs, dr2_den _ false 1 l (envP1 P l r n a b h), quo2_val l h]

theorem halveR_val (vec : List Int) (P : List Cell) (l r n a b : Nat) (h : r < 2147483648) :
    vdenL u64 vec (penv1 (stP P l r n a b)) (.divrem i32 false (.variable i32 2) (.literal i32 2)) = some ((r / 2 : Nat) : Int) := by
  have hs : (NExpr.divrem i32 false (.variable i32 2) (.literal i32 2)).scalarOnly = true := rfl
  rw [vdenL_scalar _ _ _ _ hs, dr2_den _ false 2 r (envP2 P l r n a b h), quo2_val r h]

theorem loopCond_val (vec : List Int) (P : List Cell) (l r n a b : Nat) (hl : l < 2147483648) (hr : r < 2147483648) :
    vdenL u64 vec (penv1 (stP P l r n a b)) loopCondP = some (if l < r then 1 else 0) := by
  have hs : loopCondP.scalarOnly = true := rfl
  rw [vdenL_scalar _ _ _ _ hs, den_binary, den_variable, envP1 P l r n a b hl, Option.bind_some, den_variable,
    envP2 P l r n a b hr, Option.bind_some]
  have : binaryValue .lt (l : Int) (r : Int) = if l < r then 1 else 0 := by
    show (if (l : Int) < (r : Int) then 1 else 0) = _
    by_cases h : l < r
    · have : (l : Int) < (r : Int) := by omega
      simp [h]
    · have : ¬ ((l : Int) < (r : Int)) := by omega
      simp [h]
  rw [this]
  simp only [bT]; unfold Ty.convert
  by_cases h : l < r <;> simp [h]

theorem stP_len (P : List Cell) (l r n a b l' r' n' a' b' : Nat) :
    (stP P l' r' n' a' b').mem.length = (stP P l r n a b).mem.length ∧
      (stP P l' r' n' a' b').bs.length = (stP P l r n a b).bs.length := by
  simp [gS_mem_len, gS_bs_len]

theorem stP_take (P : List Cell) (l r n a b l' r' n' a' b' : Nat) :
    (⟨(stP P l' r' n' a' b').mem.take (stP P l r n a b).mem.length,
      (stP P l' r' n' a' b').bs.take (stP P l r n a b).bs.length⟩ : PS) = stP P l' r' n' a' b' :=
  Proofs.PexecKit.scope_take _ _ (stP_len P l r n a b l' r' n' a' b').1 (stP_len P l r n a b l' r' n' a' b').2

theorem stP_setL (vec : List Int) (P : List Cell) (l r n a b l' : Nat) (e : NExpr) (hv : vdenL u64 vec (penv1 (stP P l r n a b)) e = some (l' : Int))
    (hl' : l' < 2147483648) (hl : l < 2147483648) :
    pstmtW u64 (.assign 1 i32 e) (stP P l r n a b) vec =
      some ⟨stP P l' r n a b, vec, none, (vwp e).1 + 1, P.length + 2 * 5 + (vwp e).2 + 2, 0⟩ := by
  have := gS_assign u64 P (L5 l r n a b) vec 0 (by simp) i32 e (l' : Int) (l' : Int) hv (ci l) rfl rfl (validN l hl)
    (conv_signed i32 rfl rfl _ (validN l' hl'))
  exact this

theorem stP_setR (vec : List Int) (P : List Cell) (l r n a b r' : Nat) (e : NExpr) (hv : vdenL u64 vec (penv1 (stP P l r n a b)) e = some (r' : Int))
    (hr' : r' < 2147483648) (hr : r < 2147483648) :
    pstmtW u64 (.assign 2 i32 e) (stP P l r n a b) vec =
      some ⟨stP P l r' n a b, vec, none, (vwp e).1 + 1, P.length + 2 * 5 + (vwp e).2 + 2, 0⟩ := by
  have := gS_assign u64 P (L5 l r n a b) vec 1 (by simp) i32 e (r' : Int) (r' : Int) hv (ci r) rfl rfl (validN r hr)
    (conv_signed i32 rfl rfl _ (validN r' hr'))
  exact this

theorem stP_setN (vec : List Int) (P : List Cell) (l r n a b n' : Nat) (e : NExpr) (hv : vdenL u64 vec (penv1 (stP P l r n a b)) e = some (n' : Int))
    (hn' : n' < 2147483648) (hn : n < 2147483648) :
    pstmtW u64 (.assign 3 i32 e) (stP P l r n a b) vec =
      some ⟨stP P l r n' a b, vec, none, (vwp e).1 + 1, P.length + 2 * 5 + (vwp e).2 + 2, 0⟩ := by
  have := gS_assign u64 P (L5 l r n a b) vec 2 (by simp) i32 e (n' : Int) (n' : Int) hv (ci n) rfl rfl (validN n hn)
    (conv_signed i32 rfl rfl _ (validN n' hn'))
  exact this

theorem stP_setA (vec : List Int) (P : List Cell) (l r n a b a' : Nat) (e : NExpr) (hv : vdenL u64 vec (penv1 (stP P l r n a b)) e = some (a' : Int))
    (ha' : a' < 18446744073709551616) (ha : a < 18446744073709551616) :
    pstmtW u64 (.assign 4 u64 e) (stP P l r n a b) vec =
      some ⟨stP P l r n a' b, vec, none, (vwp e).1 + 1, P.length + 2 * 5 + (vwp e).2 + 2, 0⟩ := by
  have := gS_assign u64 P (L5 l r n a b) vec 3 (by simp) u64 e (a' : Int) (a' : Int) hv (cu a) rfl rfl (u64_lt a ha)
    (Ty.convert_of_valid _ _ (u64_lt a' ha'))
  exact this

theorem stP_setB (vec : List Int) (P : List Cell) (l r n a b b' : Nat) (e : NExpr) (hv : vdenL u64 vec (penv1 (stP P l r n a b)) e = some (b' : Int))
    (hb' : b' < 18446744073709551616) (hb : b < 18446744073709551616) :
    pstmtW u64 (.assign 5 u64 e) (stP P l r n a b) vec =
      some ⟨stP P l r n a b', vec, none, (vwp e).1 + 1, P.length + 2 * 5 + (vwp e).2 + 2, 0⟩ := by
  have := gS_assign u64 P (L5 l r n a b) vec 4 (by simp) u64 e (b' : Int) (b' : Int) hv (cu b) rfl rfl (u64_lt b hb)
    (Ty.convert_of_valid _ _ (u64_lt b' hb'))
  exact this

theorem vec_get (vec : List Int) (v : List Nat) (hvec : vec = v.map (fun x : Nat => (x : Int))) (j : Nat) (hj : j < v.length) :
    vec[j]? = some ((v.getD j 0 : Nat) : Int) := by
  subst hvec
  simp [List.getElem?_map, hj, List.getD_eq_getElem?_getD]

theorem getD_lt (v : List Nat) (hvM : ∀ x ∈ v, x < M64) (j : Nat) (hj : j < v.length) : v.getD j 0 < M64 := by
  have : v.getD j 0 = v[j] := by simp [List.getD_eq_getElem?_getD, hj]
  rw [this]
  exact hvM _ (List.getElem_mem hj)

theorem br1_exec (vec : List Int) (v : List Nat) (hvec : vec = v.map (fun x : Nat => (x : Int))) (hvM : ∀ x ∈ v, x < M64)
    (P : List Cell) (l r n a b : Nat) (hlr : l < r) (hr : r ≤ v.length) (hlen : v.length < 2147483648)
    (ha : a < M64) (hb : b < M64) (fu : Nat) :
    ∃ r1, pexecW u64 fu br1 (stP P l r n a b) vec = some r1 ∧ r1.ps = stP P (pl1 l) r n (pleft v l a) b ∧
      r1.vec = vec ∧ r1.ret = none ∧ r1.cost ≤ 60 ∧ r1.need ≤ P.length + 60 ∧ r1.wk = 0 := by
  have hc := c1_val vec P l r n a b (by omega)
  by_cases hev : l % 2 = 0
  · rw [if_pos hev] at hc
    have br := pexecW_branch_falseB u64 fu c1E yes1 (.primitive .skip) (stP P l r n a b) vec hc _ (pexecW_skip u64 fu _ _)
    refine ⟨_, br, ?_, rfl, rfl, ?_, ?_, rfl⟩
    · simp [pl1, pleft, hev]
    · simp [vwp, NExpr.nodes, Container.nodes]
    · simp [vwp, NExpr.nodes, Container.nodes, gS_size]
  · rw [if_neg hev] at hc
    have hodd : l % 2 = 1 := by omega
    have hlv : l < v.length := by omega
    have hx := vec_get vec v hvec l hlv
    have hxv := u64_lt _ (getD_lt v hvM l hlv)
    have av := accL_val vec P l r n a b (v.getD l 0) (by omega) ha hx hxv
    have a' : (a + v.getD l 0) % M64 < M64 := Nat.mod_lt _ (by decide)
    have s1 := stP_setA vec P l r n a b ((a + v.getD l 0) % M64) _ av a' ha
    have iv := incL_val vec P l r n ((a + v.getD l 0) % M64) b (by omega)
    have s2 := stP_setL vec P l r n ((a + v.getD l 0) % M64) b (l + 1) _ iv (by omega) (by omega)
    have q1 := (pexecW_prim u64 fu accL _ _).trans s1
    have q2 := (pexecW_prim u64 fu incL _ _).trans s2
    have t2 := seqW_some q2 rfl (pexecW_skip u64 fu (stP P (l + 1) r n ((a + v.getD l 0) % M64) b) vec)
    have t1 := seqW_some q1 rfl t2
    have sc := pexecW_scope u64 fu _ _ _ _ t1
    simp only [stP_take] at sc
    have y1 := seqW_some sc rfl (pexecW_skip u64 fu (stP P (l + 1) r n ((a + v.getD l 0) % M64) b) vec)
    have br := pexecW_branch_trueB u64 fu c1E yes1 (.primitive .skip) (stP P l r n a b) vec 1 hc (by simp) _ y1
    refine ⟨_, br, ?_, rfl, rfl, ?_, ?_, rfl⟩
    · simp [pl1, pleft, hodd]
    · simp [vwp, NExpr.nodes, Container.nodes]
    · simp [vwp, NExpr.nodes, Container.nodes, gS_size]

theorem br2_exec (vec : List Int) (v : List Nat) (hvec : vec = v.map (fun x : Nat => (x : Int))) (hvM : ∀ x ∈ v, x < M64)
    (P : List Cell) (l r n a b : Nat) (hlr : l ≤ r) (hr : r ≤ v.length) (hlen : v.length < 2147483648)
    (ha : a < M64) (hb : b < M64) (fu : Nat) :
    ∃ r1, pexecW u64 fu br2 (stP P l r n a b) vec = some r1 ∧ r1.ps = stP P l (pr1 r) n a (pright v r b) ∧
      r1.vec = vec ∧ r1.ret = none ∧ r1.cost ≤ 60 ∧ r1.need ≤ P.length + 60 ∧ r1.wk = 0 := by
  have hc := c2_val vec P l r n a b (by omega)
  by_cases hev : r % 2 = 0
  · rw [if_pos hev] at hc
    have br := pexecW_branch_falseB u64 fu c2E yes2 (.primitive .skip) (stP P l r n a b) vec hc _ (pexecW_skip u64 fu _ _)
    refine ⟨_, br, ?_, rfl, rfl, ?_, ?_, rfl⟩
    · simp [pr1, pright, hev]
    · simp [vwp, NExpr.nodes, Container.nodes]
    · simp [vwp, NExpr.nodes, Container.nodes, gS_size]
  · rw [if_neg hev] at hc
    have hodd : r % 2 = 1 := by omega
    have hrv : r - 1 < v.length := by omega
    have hx := vec_get vec v hvec (r - 1) hrv
    have hxv := u64_lt _ (getD_lt v hvM (r - 1) hrv)
    have dv := decR_val vec P l r n a b (by omega) (by omega)
    have s1 := stP_setR vec P l r n a b (r - 1) _ dv (by omega) (by omega)
    have av := accR_val vec P l (r - 1) n a b (v.getD (r - 1) 0) (by omega) hb hx hxv
    have a' : (b + v.getD (r - 1) 0) % M64 < M64 := Nat.mod_lt _ (by decide)
    have s2 := stP_setB vec P l (r - 1) n a b ((b + v.getD (r - 1) 0) % M64) _ av a' hb
    have q1 := (pexecW_prim u64 fu decR _ _).trans s1
    have q2 := (pexecW_prim u64 fu accR _ _).trans s2
    have t2 := seqW_some q2 rfl (pexecW_skip u64 fu (stP P l (r - 1) n a ((b + v.getD (r - 1) 0) % M64)) vec)
    have t1 := seqW_some q1 rfl t2
    have sc := pexecW_scope u64 fu _ _ _ _ t1
    simp only [stP_take] at sc
    have y1 := seqW_some sc rfl (pexecW_skip u64 fu (stP P l (r - 1) n a ((b + v.getD (r - 1) 0) % M64)) vec)
    have br := pexecW_branch_trueB u64 fu c2E yes2 (.primitive .skip) (stP P l r n a b) vec 1 hc (by simp) _ y1
    refine ⟨_, br, ?_, rfl, rfl, ?_, ?_, rfl⟩
    · simp [pr1, pright, hodd]
    · simp [vwp, NExpr.nodes, Container.nodes]
    · simp [vwp, NExpr.nodes, Container.nodes, gS_size]

theorem pleft_lt (v : List Nat) (l a : Nat) (ha : a < M64) : pleft v l a < M64 := by
  unfold pleft; split
  · exact Nat.mod_lt _ (by decide)
  · exact ha

theorem pright_lt (v : List Nat) (r b : Nat) (hb : b < M64) : pright v r b < M64 := by
  unfold pright; split
  · exact Nat.mod_lt _ (by decide)
  · exact hb

theorem pl1_le (l r : Nat) (h : l < r) : pl1 l ≤ r := by unfold pl1; split <;> omega
theorem pr1_le (r : Nat) : pr1 r ≤ r := by unfold pr1; split <;> omega

theorem prod_iter (vec : List Int) (v : List Nat) (hvec : vec = v.map (fun x : Nat => (x : Int))) (hvM : ∀ x ∈ v, x < M64)
    (P : List Cell) (l r n a b : Nat) (hlr : l < r) (hr : r ≤ v.length) (hlen : v.length < 2147483648)
    (ha : a < M64) (hb : b < M64) (fu : Nat) :
    ∃ r1, pexecW u64 fu loopBodyP (stP P l r n a b) vec = some r1 ∧
      r1.ps = stP P (pl1 l / 2) (pr1 r / 2) n (pleft v l a) (pright v r b) ∧
      r1.vec = vec ∧ r1.ret = none ∧ r1.cost ≤ 400 ∧ r1.need ≤ P.length + 100 ∧ r1.wk = 0 := by
  obtain ⟨e1, h1, p1, v1, ret1, c1, n1, w1⟩ := br1_exec vec v hvec hvM P l r n a b hlr hr hlen ha hb fu
  have hpl := pl1_le l r hlr
  have hpr := pr1_le r
  obtain ⟨e2, h2, p2, v2, ret2, c2, n2, w2⟩ :=
    br2_exec vec v hvec hvM P (pl1 l) r n (pleft v l a) b hpl hr hlen (pleft_lt v l a ha) hb fu
  have hv3 := halveL_val vec P (pl1 l) (pr1 r) n (pleft v l a) (pright v r b) (by omega)
  have s3 := stP_setL vec P (pl1 l) (pr1 r) n (pleft v l a) (pright v r b) (pl1 l / 2) _ hv3 (by omega) (by omega)
  have hv4 := halveR_val vec P (pl1 l / 2) (pr1 r) n (pleft v l a) (pright v r b) (by omega)
  have s4 := stP_setR vec P (pl1 l / 2) (pr1 r) n (pleft v l a) (pright v r b) (pr1 r / 2) _ hv4 (by omega) (by omega)
  have q3 := (pexecW_prim u64 fu halveL _ _).trans s3
  have q4 := (pexecW_prim u64 fu halveR _ _).trans s4
  have t4 := seqW_some q4 rfl (pexecW_skip u64 fu (stP P (pl1 l / 2) (pr1 r / 2) n (pleft v l a) (pright v r b)) vec)
  have t3 := seqW_some q3 rfl t4
  have hX := seqW_some h2 ret2 (by rw [p2, v2]; exact t3)
  have hBr := seqW_some h1 ret1 (by rw [p1, v1]; exact hX)
  have sc := pexecW_scope u64 fu _ _ _ _ hBr
  simp only [stP_take] at sc
  have fin := seqW_some sc rfl (pexecW_skip u64 fu (stP P (pl1 l / 2) (pr1 r / 2) n (pleft v l a) (pright v r b)) vec)
  refine ⟨_, fin, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, Container.nodes] at *
    omega
  · simp [vwp, NExpr.nodes, Container.nodes, gS_size] at *
    omega
  · simp [w1, w2]

theorem vwp_condP : vwp loopCondP = (3, 3) := by decide

theorem width_half (l r : Nat) (h : l < r) : pr1 r / 2 - pl1 l / 2 ≤ (r - l) / 2 := by
  unfold pl1 pr1; split <;> split <;> omega

theorem PInv_exit (v : List Nat) (N T l r a b : Nat) (h : PInv v N T l r a b) (hlr : ¬ l < r) :
    (a + b) % M64 = T % M64 := by
  obtain ⟨_, _, _, _, h5⟩ := h
  have : r - l = 0 := by omega
  rw [this] at h5
  simpa [rsum] using h5

theorem prod_loop (vec : List Int) (v : List Nat) (hvec : vec = v.map (fun x : Nat => (x : Int))) (hvM : ∀ x ∈ v, x < M64)
    (P : List Cell) (N T n : Nat) (hT : TInv v N) (hN : v.length < 2147483648) :
    ∀ (m l r a b : Nat), r - l = m → l ≤ r → PInv v N T l r a b → ∀ fu, stepsL m + 1 ≤ fu →
      ∃ (res : PRW) (a' b' : Nat), pexecW u64 fu loopCP (stP P l r n a b) vec = some res ∧
        (∃ l' r', res.ps = stP P l' r' n a' b') ∧ a' < M64 ∧ b' < M64 ∧ (a' + b') % M64 = T % M64 ∧
        res.vec = vec ∧ res.ret = none ∧ res.cost ≤ 410 * stepsL m + 10 ∧ res.need ≤ P.length + 100 ∧ res.wk = 0 := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro l r a b hm hle hI fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hlen2 := hT.2.1
    obtain ⟨hl1, hr2, ha, hb, _⟩ := hI
    have hc := loopCond_val vec P l r n a b (by omega) (by omega)
    by_cases hlt : l < r
    · rw [if_pos hlt] at hc
      obtain ⟨r1, h1, p1, v1, ret1, c1, n1, w1⟩ := prod_iter vec v hvec hvM P l r n a b hlt (by omega) hN ha hb (fu' + 1)
      have hI' := prod_step v N T hT l r a b ⟨hl1, hr2, ha, hb, ‹_›⟩ hlt
      have hwh := width_half l r hlt
      have hm' : stepsL m = 1 + stepsL (m / 2) := stepsL_succ m (by omega)
      have hms := stepsL_mono (m / 2) (pr1 r / 2 - pl1 l / 2) (by omega)
      have hle' : pl1 l / 2 ≤ pr1 r / 2 := by unfold pl1 pr1; split <;> split <;> omega
      obtain ⟨r2, a2, b2, h2, ⟨l2, r2', hps2⟩, ha2, hb2, hT2, v2, ret2, c2, n2, w2⟩ :=
        ih (pr1 r / 2 - pl1 l / 2) (by omega) (pl1 l / 2) (pr1 r / 2) (pleft v l a) (pright v r b) rfl hle' hI' fu'
          (by omega)
      rw [pexecW_while, hc]
      simp only [Bind.bind, Option.bind, int_one_ne, ite_false, h1, ret1, p1, v1, h2, vwp_condP]
      refine ⟨⟨r2.ps, r2.vec, r2.ret, 3 + 1 + r1.cost + r2.cost, max ((stP P l r n a b).mem.length +
        (stP P l r n a b).bs.length + 3 + 2) (max r1.need r2.need), r1.wk + r2.wk⟩, a2, b2, by simp, ⟨l2, r2', hps2⟩,
        ha2, hb2, hT2, v2, ret2, ?_, ?_, ?_⟩
      · simp <;> omega
      · simp [gS_size, n1, n2] <;> omega
      · simp [w1, w2]
    · rw [if_neg hlt] at hc
      rw [pexecW_while, hc]
      simp only [Bind.bind, Option.bind, ite_true, vwp_condP]
      refine ⟨_, a, b, rfl, ⟨l, r, rfl⟩, ha, hb, ?_, rfl, rfl, ?_, ?_, rfl⟩
      · exact PInv_exit v N T l r a b ⟨hl1, hr2, ha, hb, ‹_›⟩ hlt
      · simp
      · simp [gS_size]

-- The initial cells: the parameters `l`, `r`, then `n_node`.
abbrev L3 (l r n : Nat) : List Cell := [ci l, ci r, ci n]
abbrev L2 (l r : Nat) : List Cell := [ci l, ci r]

theorem size_valP (vec : List Int) (ps : PS) (hn : vec.length < 2147483648) :
    vdenL u64 vec (penv1 ps) (.cast i32 (.size (.integer u64) (.local 0))) = some (vec.length : Int) := by
  have hr2 : (NExpr.cast i32 (.size (.integer u64) (.local 0))).scalarOnly = false := rfl
  have hr : (NExpr.size (.integer u64) (.local 0)).scalarOnly = false := rfl
  have hsz : vdenL u64 vec (penv1 ps) (.size (.integer u64) (.local 0)) = some (vec.length : Int) := by
    simp [vdenL, hr]
  rw [vdenL_cast u64 vec _ _ _ hr2, hsz, Option.bind_some]
  exact conv_signed i32 rfl rfl _ (validN _ hn)

theorem zero_valP (vec : List Int) (ps : PS) :
    vdenL u64 vec (penv1 ps) (.cast u64 (.literal i32 0)) = some 0 := by
  have hs : (NExpr.cast u64 (.literal i32 0)).scalarOnly = true := rfl
  rw [vdenL_scalar _ _ _ _ hs, den_cast, den_literal, if_pos (show i32.valid 0 = true from rfl), Option.bind_some]
  rfl

theorem setL0_val (vec : List Int) (P : List Cell) (l r n a b : Nat) (hl : l < 2147483648) (hn : n < 2147483648)
    (h : l + n < 2147483648) :
    vdenL u64 vec (penv1 (stP P l r n a b)) (.binary i32 .add (.variable i32 1) (.variable i32 3)) = some ((l + n : Nat) : Int) := by
  have hs : (NExpr.binary i32 .add (.variable i32 1) (.variable i32 3)).scalarOnly = true := rfl
  rw [vdenL_scalar _ _ _ _ hs, den_binary, den_variable, envP1 P l r n a b hl, Option.bind_some, den_variable,
    envP3 P l r n a b hn, Option.bind_some]
  have : binaryValue .add (l : Int) (n : Int) = ((l + n : Nat) : Int) := by
    show (l : Int) + (n : Int) = _; push_cast; rfl
  rw [this]
  exact conv_signed i32 rfl rfl _ (validN _ h)

theorem setR0_val (vec : List Int) (P : List Cell) (l r n a b : Nat) (hr : r < 2147483648) (hn : n < 2147483648)
    (h : r + n < 2147483648) :
    vdenL u64 vec (penv1 (stP P l r n a b)) (.binary i32 .add (.variable i32 2) (.variable i32 3)) = some ((r + n : Nat) : Int) := by
  have hs : (NExpr.binary i32 .add (.variable i32 2) (.variable i32 3)).scalarOnly = true := rfl
  rw [vdenL_scalar _ _ _ _ hs, den_binary, den_variable, envP2 P l r n a b hr, Option.bind_some, den_variable,
    envP3 P l r n a b hn, Option.bind_some]
  have : binaryValue .add (r : Int) (n : Int) = ((r + n : Nat) : Int) := by
    show (r : Int) + (n : Int) = _; push_cast; rfl
  rw [this]
  exact conv_signed i32 rfl rfl _ (validN _ h)

theorem retP_val (vec : List Int) (P : List Cell) (l r n a b : Nat) (ha : a < M64) (hb : b < M64) :
    vdenL u64 vec (penv1 (stP P l r n a b)) (.binary u64 .add (.variable u64 4) (.variable u64 5)) =
      some (((a + b) % M64 : Nat) : Int) := by
  have hs : (NExpr.binary u64 .add (.variable u64 4) (.variable u64 5)).scalarOnly = true := rfl
  rw [vdenL_scalar _ _ _ _ hs, den_binary, den_variable, envP4 P l r n a b ha, Option.bind_some, den_variable,
    envP5 P l r n a b hb, Option.bind_some]
  have : binaryValue .add (a : Int) (b : Int) = ((a + b : Nat) : Int) := by
    show (a : Int) + (b : Int) = _; push_cast; rfl
  rw [this, convert_u64]
  congr 1

theorem body_execP (vec : List Int) (v : List Nat) (hvec : vec = v.map (fun x : Nat => (x : Int))) (hvM : ∀ x ∈ v, x < M64)
    (P : List Cell) (N l0 r0 : Nat) (hT : TInv v N) (hN : v.length < 2147483648) (hlr : l0 ≤ r0) (hrN : r0 ≤ N) (fu : Nat)
    (hfu : stepsL (r0 - l0) + 1 ≤ fu) :
    ∃ res : PRW, pexecW u64 fu bodyCmdP (gS P (L2 l0 r0)) vec = some res ∧
      res.ret = some ((rsum v (l0 + N) (r0 - l0) % M64 : Nat) : Int) ∧ (∃ cs, res.ps = gS P cs) ∧ res.vec = vec ∧
      res.cost ≤ 410 * stepsL (r0 - l0) + 100 ∧ res.need ≤ P.length + 100 ∧ res.wk = 0 := by
  have hvl : v.length = 2 * N := hT.2.1
  have hvlen : vec.length = 2 * N := by rw [hvec]; simp [hvl]
  have hN0 := hT.1
  -- n_node := size
  have sz := size_valP vec (gS P (L2 l0 r0)) (by omega)
  rw [hvlen] at sz
  have d1 := gS_decl u64 P (L2 l0 r0) vec i32 _ ((2 * N : Nat) : Int) ((2 * N : Nat) : Int) sz
    (conv_signed i32 rfl rfl _ (validN _ (by omega)))
  have q1 := (pexecW_prim u64 fu declN _ _).trans d1
  -- n_node /= 2
  have e3 : penv1 (gS P (L3 l0 r0 (2 * N))) 3 i32 = some ((2 * N : Nat) : Int) :=
    gS_env P (L3 l0 r0 (2 * N)) 2 (ci (2 * N)) rfl (validN _ (by omega))
  have hv2 : vdenL u64 vec (penv1 (gS P (L3 l0 r0 (2 * N)))) (.divrem i32 false (.variable i32 3) (.literal i32 2)) =
      some ((N : Nat) : Int) := by
    have hs : (NExpr.divrem i32 false (.variable i32 3) (.literal i32 2)).scalarOnly = true := rfl
    rw [vdenL_scalar _ _ _ _ hs, dr2_den _ false 3 (2 * N) e3, quo2_val (2 * N) (by omega)]
    have : 2 * N / 2 = N := by omega
    rw [this]
  have s2 := gS_assign u64 P (L3 l0 r0 (2 * N)) vec 2 (by simp) i32 _ ((N : Nat) : Int) ((N : Nat) : Int) hv2
    (ci (2 * N)) rfl rfl (validN _ (by omega)) (conv_signed i32 rfl rfl _ (validN _ (by omega)))
  have q2 := (pexecW_prim u64 fu setN _ _).trans s2
  -- left := 0, right := 0
  have z1 := gS_decl u64 P (L3 l0 r0 N) vec u64 _ 0 0 (zero_valP vec (gS P (L3 l0 r0 N))) (Ty.convert_of_valid _ _ (u64_lt 0 (by decide)))
  have q3 := (pexecW_prim u64 fu declZ _ _).trans z1
  have z2 := gS_decl u64 P (L3 l0 r0 N ++ [cu 0]) vec u64 _ 0 0 (zero_valP vec (gS P (L3 l0 r0 N ++ [cu 0]))) (Ty.convert_of_valid _ _ (u64_lt 0 (by decide)))
  have q4 := (pexecW_prim u64 fu declZ _ _).trans z2
  -- l += n_node, r += n_node
  have sl := stP_setL vec P l0 r0 N 0 0 (l0 + N) _ (setL0_val vec P l0 r0 N 0 0 (by omega) (by omega) (by omega))
    (by omega) (by omega)
  have q5 := (pexecW_prim u64 fu setL0 _ _).trans sl
  have sr := stP_setR vec P (l0 + N) r0 N 0 0 (r0 + N) _ (setR0_val vec P (l0 + N) r0 N 0 0 (by omega) (by omega) (by omega))
    (by omega) (by omega)
  have q6 := (pexecW_prim u64 fu setR0 _ _).trans sr
  -- the loop
  have hI : PInv v N (rsum v (l0 + N) (r0 - l0)) (l0 + N) (r0 + N) 0 0 := by
    refine ⟨by omega, by omega, by decide, by decide, ?_⟩
    have : r0 + N - (l0 + N) = r0 - l0 := by omega
    rw [this]; simp
  obtain ⟨rl, a', b', hL, ⟨l', r', hps⟩, ha', hb', hT', vL, retL, cL, nL, wL⟩ :=
    prod_loop vec v hvec hvM P N (rsum v (l0 + N) (r0 - l0)) N hT hN (r0 + N - (l0 + N)) (l0 + N) (r0 + N) 0 0 rfl
      (by omega) hI fu (by have : r0 + N - (l0 + N) = r0 - l0 := by omega
                           rw [this]; exact hfu)
  have rv := retP_val vec P l' r' N a' b' ha' hb'
  have g1 := pstmtW_ret_ok u64 (stP P l' r' N a' b') vec _ _ rv
  have g2 := (pexecW_prim u64 fu retP _ _).trans g1
  have g3 := seqW_ret (b := .primitive .skip) g2 rfl
  have h7 := seqW_some hL retL (by rw [hps, vL]; exact g3)
  have h6 := seqW_some q6 rfl h7
  have h5 := seqW_some q5 rfl h6
  have h4 := seqW_some q4 rfl h5
  have h3 := seqW_some q3 rfl h4
  have h2 := seqW_some q2 rfl h3
  have h1 := seqW_some q1 rfl h2
  refine ⟨_, h1, ?_, ⟨L5 l' r' N a' b', rfl⟩, rfl, ?_, ?_, ?_⟩
  · show some (((a' + b') % M64 : Nat) : Int) = _
    rw [hT']
  · have hr0 : r0 + N - (l0 + N) = r0 - l0 := by omega
    rw [hr0] at cL
    simp [vwp, NExpr.nodes, Container.nodes] at *
    omega
  · simp [vwp, NExpr.nodes, Container.nodes, gS_size] at *
    omega
  · simp [wL]

/-- The caller owns a root vector of `unsigned long long`, passed by const reference. -/
structure VOKU (caller : NState) (vslot vb V vsc : Nat) (m : Bool) (vbuf : Buffer Value) : Prop where
  valid : caller.frame.state.wellFormed = true
  slot : caller.vectorSlot vslot = some vb
  binding : caller.frame.bindings[vb]? = some ⟨V,.integer u64,false,.root vsc⟩
  vtag : caller.frame.state.forest.lookup V = some ⟨.integer u64,none,some vsc,[]⟩
  vfound : caller.frame.state.storage.lookup V = some vbuf
  lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length
  flag : caller.frame.rootWritable[V]? = some m
  strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope
  base : caller.scalars.baseMemory ≤ caller.scalars.memory.length

/-- The caller owns a writable root vector of `unsigned long long`, passed by reference. -/
structure VOKUW (caller : NState) (vslot vb V vsc : Nat) (vbuf : Buffer Value) : Prop where
  valid : caller.frame.state.wellFormed = true
  slot : caller.vectorSlot vslot = some vb
  binding : caller.frame.bindings[vb]? = some ⟨V,.integer u64,true,.root vsc⟩
  vtag : caller.frame.state.forest.lookup V = some ⟨.integer u64,none,some vsc,[]⟩
  vfound : caller.frame.state.storage.lookup V = some vbuf
  lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length
  flag : caller.frame.rootWritable[V]? = some true
  strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope
  base : caller.scalars.baseMemory ≤ caller.scalars.memory.length

theorem prepare_sp (caller : NState) {vslot vb V vsc : Nat} {m : Bool} {vbuf : Buffer Value}
    (ok : VOKU caller vslot vb V vsc m vbuf) (e1 e2 : NExpr) (v1 v2 : Int)
    (h1 : e1.scalarOnly = true) (h2 : e2.scalarOnly = true) (t1ty : e1.resultType = i32) (t2ty : e2.resultType = i32)
    (d1 : e1.denote (envOf caller) = some v1) (d2 : e2.denote (envOf caller) = some v2)
    (n1 : i32.valid v1 = true) (n2 : i32.valid v2 = true) :
    ∃ t1 t2, Good (caller.charge 1 1) t1 e1.nodes e1.nodes ∧ Good t1 t2 e2.nodes e2.nodes ∧
      ∃ Sinit, prepare caller Proofs.SegtreeSumInstance.segtree_sum_product_std_vector_unsigned_long_long.parameters
          [.vectorReference vslot,.value e1,.value e2] = some Sinit ∧
        Sinit.slots = [.vector 0,.scalar 0,.scalar 1] ∧ Sinit.scalars.memory = callerP caller ++ [⟨i32,v1⟩,⟨i32,v2⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer u64,false,.root vsc⟩]⟩ ∧
        Sinit.scalars.work = t2.scalars.work+4 ∧ t2.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨resolved,_,_⟩ := resolve_vroot caller.frame vb V vsc u64 false m vbuf ok.binding ok.valid ok.vtag ok.vfound
    ok.lengths ok.flag (by simp)
  have rvec : resolve caller (.vector u64 false) (.vectorReference vslot) =
      some (caller.charge 1 1,.vector V vsc u64 false) := by
    simp [resolve,ok.slot,ok.binding,resolved]
  have core1 := core_charge caller 1 1
  obtain ⟨t1,ran1,g1⟩ := scalar_eval e1 (caller.charge 1 1) v1 h1 (by rw [envOf_core core1]; exact d1)
  obtain ⟨t2,ran2,g2⟩ := scalar_eval e2 t1 v2 h2 (by rw [envOf_core g1.1, envOf_core core1]; exact d2)
  refine ⟨t1,t2,g1,g2,?_⟩
  have frameT : t2.frame = caller.frame := by rw [g2.1.1, g1.1.1]; rfl
  have fs : t2.frame.state = caller.frame.state := by rw [frameT]
  have fr : t2.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t2.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t2.scalars.memory = caller.scalars.memory := by
    have b := g2.1.2.2.2.1; have c := g1.1.2.2.2.1; rw [b, c]; rfl
  have hbind : t2.scalars.bindings = caller.scalars.bindings := by
    have b := g2.1.2.2.2.2.1; have c := g1.1.2.2.2.2.1; rw [b, c]; rfl
  have hbase : t2.scalars.baseMemory = caller.scalars.baseMemory := by
    have b := g2.1.2.2.2.2.2; have c := g1.1.2.2.2.2.2; rw [b, c]; rfl
  have res1 : resolve (caller.charge 1 1) (.scalar i32 false true) (.value e1) = some (t1,.scalar i32 true v1) := by
    simp [resolve,t1ty,ran1]
  have res2 : resolve t1 (.scalar i32 false true) (.value e2) = some (t2,.scalar i32 true v2) := by
    simp [resolve,t2ty,ran2]
  have bound : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).bindRoot V (.integer u64) vsc false =
      some (⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer u64,false,.root vsc⟩]⟩,0) := by
    have vobject : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).object V (.integer u64) =
        some (vbuf,⟨.integer u64,none,some vsc,[]⟩) :=
      object_runs _ V _ vbuf _ ok.valid ok.vfound ok.vtag rfl
    have vrooted : caller.frame.state.forest.rootOwner V = some V := CppVectorOwnership.root_runs _ V _ ok.vtag rfl
    have vmax : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).maximum V = some m :=
      maximum_runs _ V V m ok.lengths vrooted ok.flag
    simp only [Frame.bindRoot,vobject,vmax,Bind.bind,Option.bind]
    simp [Frame.addBinding]
  have hp : Proofs.SegtreeSumInstance.segtree_sum_product_std_vector_unsigned_long_long.parameters =
      [.vector u64 false,.scalar i32 false true,.scalar i32 false true] := rfl
  rw [hp]
  simp [prepare,ok.valid,resolveAll,rvec,res1,res2]
  simp [fs,fr,fb,hmem,hbind,hbase,bound,bindAll,bindOne,CppState.bindArgument,n1,n2,callerP,
    NState.observe,CppState.State.observe]
  left
  have a1 := g1.2.2.2.2.1
  have a2 := g2.2.2.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at a1
  omega

set_option maxHeartbeats 4000000 in
theorem prepare_ss (caller : NState) {vslot vb V vsc : Nat} {vbuf : Buffer Value}
    (ok : VOKUW caller vslot vb V vsc vbuf) (e1 e2 : NExpr) (v1 v2 : Int)
    (h1 : e1.scalarOnly = true) (h2 : e2.scalarOnly = true) (t1ty : e1.resultType = i32) (t2ty : e2.resultType = u64)
    (d1 : e1.denote (envOf caller) = some v1) (d2 : e2.denote (envOf caller) = some v2)
    (n1 : i32.valid v1 = true) (n2 : u64.valid v2 = true) :
    ∃ t1 t2, Good (caller.charge 1 1) t1 e1.nodes e1.nodes ∧ Good t1 t2 e2.nodes e2.nodes ∧
      ∃ Sinit, prepare caller Proofs.SegtreeSumInstance.segtree_sum_set_std_vector_unsigned_long_long.parameters
          [.vectorReference vslot,.value e1,.value e2] = some Sinit ∧
        Sinit.slots = [.vector 0,.scalar 0,.scalar 1] ∧ Sinit.scalars.memory = callerP caller ++ [⟨i32,v1⟩,⟨u64,v2⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer u64,true,.root vsc⟩]⟩ ∧
        Sinit.scalars.work = t2.scalars.work+4 ∧ t2.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨resolved,_,_⟩ := resolve_vroot caller.frame vb V vsc u64 true true vbuf ok.binding ok.valid ok.vtag ok.vfound
    ok.lengths ok.flag (fun _ => rfl)
  have rvec : resolve caller (.vector u64 true) (.vectorReference vslot) =
      some (caller.charge 1 1,.vector V vsc u64 true) := by
    simp [resolve,ok.slot,ok.binding,resolved]
  have core1 := core_charge caller 1 1
  obtain ⟨t1,ran1,g1⟩ := scalar_eval e1 (caller.charge 1 1) v1 h1 (by rw [envOf_core core1]; exact d1)
  obtain ⟨t2,ran2,g2⟩ := scalar_eval e2 t1 v2 h2 (by rw [envOf_core g1.1, envOf_core core1]; exact d2)
  refine ⟨t1,t2,g1,g2,?_⟩
  have frameT : t2.frame = caller.frame := by rw [g2.1.1, g1.1.1]; rfl
  have fs : t2.frame.state = caller.frame.state := by rw [frameT]
  have fr : t2.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t2.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t2.scalars.memory = caller.scalars.memory := by
    have b := g2.1.2.2.2.1; have c := g1.1.2.2.2.1; rw [b, c]; rfl
  have hbind : t2.scalars.bindings = caller.scalars.bindings := by
    have b := g2.1.2.2.2.2.1; have c := g1.1.2.2.2.2.1; rw [b, c]; rfl
  have hbase : t2.scalars.baseMemory = caller.scalars.baseMemory := by
    have b := g2.1.2.2.2.2.2; have c := g1.1.2.2.2.2.2; rw [b, c]; rfl
  have res1 : resolve (caller.charge 1 1) (.scalar i32 false true) (.value e1) = some (t1,.scalar i32 true v1) := by
    simp [resolve,t1ty,ran1]
  have res2 : resolve t1 (.scalar u64 false true) (.value e2) = some (t2,.scalar u64 true v2) := by
    simp [resolve,t2ty,ran2]
  have bound : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).bindRoot V (.integer u64) vsc true =
      some (⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer u64,true,.root vsc⟩]⟩,0) := by
    have vobject : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).object V (.integer u64) =
        some (vbuf,⟨.integer u64,none,some vsc,[]⟩) :=
      object_runs _ V _ vbuf _ ok.valid ok.vfound ok.vtag rfl
    have vrooted : caller.frame.state.forest.rootOwner V = some V := CppVectorOwnership.root_runs _ V _ ok.vtag rfl
    have vmax : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).maximum V = some true :=
      maximum_runs _ V V true ok.lengths vrooted ok.flag
    simp only [Frame.bindRoot,vobject,vmax,Bind.bind,Option.bind]
    simp [Frame.addBinding]
  have hp : Proofs.SegtreeSumInstance.segtree_sum_set_std_vector_unsigned_long_long.parameters =
      [.vector u64 true,.scalar i32 false true,.scalar u64 false true] := rfl
  rw [hp]
  simp [prepare,ok.valid,resolveAll,rvec,res1,res2]
  simp [fs,fr,fb,hmem,hbind,hbase,bound,bindAll,bindOne,CppState.bindArgument,n1,n2,callerP,
    NState.observe,CppState.State.observe]
  left
  have a1 := g1.2.2.2.2.1
  have a2 := g2.2.2.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at a1
  omega

set_option maxHeartbeats 4000000 in
theorem segtree_sum_product_correct (caller : NState) {vslot vb V vsc : Nat} {m : Bool} {vbuf : Buffer Value}
    (ok : VOKU caller vslot vb V vsc m vbuf) (v : List Nat) (hvM : ∀ x ∈ v, x < M64)
    (hitems : vbuf.items = (v.map (fun x : Nat => (x : Int))).map Value.integer)
    (N : Nat) (hT : TInv v N) (hN : v.length < 2147483648)
    (hbvalid : vbuf.Valid (accepts (.integer u64))) (hlimit : vbuf.limit = CppVectorBindings.sizeLimit u64)
    (howner : vbuf.owner = V)
    (e1 e2 : NExpr) (l0 r0 : Nat) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ty1 : e1.resultType = i32) (ty2 : e2.resultType = i32)
    (d1 : e1.denote (envOf caller) = some (l0 : Int)) (d2 : e2.denote (envOf caller) = some (r0 : Int))
    (hlr : l0 ≤ r0) (hrN : r0 ≤ N) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState), prepare caller Proofs.SegtreeSumInstance.segtree_sum_product_std_vector_unsigned_long_long.parameters
        [.vectorReference vslot,.value e1,.value e2] = some Sinit ∧
      Proofs.SegtreeSumInstance.segtree_sum_product_std_vector_unsigned_long_long.callFuel fuel caller [.vectorReference vslot,.value e1,.value e2] =
        .finished (res,.scalar ((rsum v (l0 + N) (r0 - l0) % M64 : Nat) : Int)) ∧
      ScalarPost3 caller Sinit res (e1.nodes + e2.nodes) (410 * Nat.log2 N + 700) caller.scalars.memory 0 V
        (v.map (fun x : Nat => (x : Int))) := by
  have hvl : v.length = 2 * N := hT.2.1
  obtain ⟨t1,t2,g1,g2,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_sp caller ok e1 e2 (l0 : Int) (r0 : Int) hs1 hs2 ty1 ty2 d1 d2 (validN l0 (by omega)) (validN r0 (by omega))
  let vc : VCtx := ⟨u64,false,m,V,vsc,vbuf,v.map (fun x : Nat => (x : Int)),hitems,fun h => absurd h (by decide),
    by simp; omega,caller.frame.state.liveSpace,caller.frame.state.storage.work,caller.scope+1,
    caller.frame.state.storage.objects.length⟩
  have fwS : FW vc (v.map (fun x : Nat => (x : Int))) vbuf 0 Sinit.frame := by
    rw [sFrame]
    refine ⟨ok.valid,ok.lengths,rfl,rfl,?_,rfl,rfl,ok.vtag,ok.vfound,ok.flag,hitems,hbvalid,hlimit,howner,by simp; omega⟩
    intro owner k h
    have := ok.strict owner k h
    show k < caller.scope+1
    omega
  have hsteps : stepsL (r0 - l0) ≤ Nat.log2 N + 1 :=
    Nat.le_trans (stepsL_mono N (r0 - l0) (by omega)) (stepsL_log N)
  obtain ⟨rr,hexec,hret,⟨cs,hrps⟩,hrvec,hcost,hneed,hwk⟩ := body_execP (v.map (fun x : Nat => (x : Int))) v rfl hvM (callerP caller) N l0 r0 hT hN
    hlr hrN (stepsL (r0 - l0) + 1) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(l0 : Int)⟩ : Cell),(⟨i32,(r0 : Int)⟩ : Cell)]).take caller.scalars.memory.length =
      caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(l0 : Int)⟩ : Cell),(⟨i32,(r0 : Int)⟩ : Cell)],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]⟩ : PS) = gS (callerP caller) (L2 l0 r0) := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  have gw2 := g2.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1
  have hres : u64.valid ((rsum v (l0 + N) (r0 - l0) % M64 : Nat) : Int) = true :=
    u64_lt _ (Nat.mod_lt _ (by decide))
  have hpost := call_vecw vc false (fun h => absurd h (by decide)) caller Proofs.SegtreeSumInstance.segtree_sum_product_std_vector_unsigned_long_long
    [.vectorReference vslot,.value e1,.value e2] Sinit
    (callerP caller ++ [(⟨i32,(l0 : Int)⟩ : Cell),(⟨i32,(r0 : Int)⟩ : Cell)])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok.base (by decide) (stepsL (r0 - l0) + 1) rr
    (by rw [hmk]; exact hexec) _ hret u64 rfl hres (by omega) (by simp) (e1.nodes + e2.nodes)
    (410 * Nat.log2 N + 700) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hwk, hrvec] at post
  exact post

-- ===== segtree_sum_set =====
abbrev L4 (idx val n i : Nat) : List Cell := [ci idx, cu val, ci n, ci i]
abbrev stS (P : List Cell) (idx val n i : Nat) : PS := gS P (L4 idx val n i)

abbrev wIdx : NExpr := .cast u64 (.variable i32 4)
abbrev idx2i : NExpr := .cast u64 (.binary i32 .mul (.literal i32 2) (.variable i32 4))
abbrev idx2i1 : NExpr := .cast u64 (.binary i32 .add (.binary i32 .mul (.literal i32 2) (.variable i32 4)) (.literal i32 1))
abbrev sumE : NExpr := .binary u64 .add (.read u64 (.local 0) idx2i) (.read u64 (.local 0) idx2i1)
abbrev wStmt : NStmt := .write (.local 0) u64 wIdx sumE
abbrev halveI : NStmt := .assign 4 i32 (.divrem i32 false (.variable i32 4) (.literal i32 2))
abbrev condI : NExpr := .binary bT .ge (.variable i32 4) (.literal i32 1)
abbrev loopBodyS : Command := .sequence (.scope (.sequence (.primitive wStmt) (.sequence (.primitive halveI) (.primitive .skip))))
  (.primitive .skip)
abbrev loopCS : Command := .whileLoop condI loopBodyS
abbrev declI : NStmt := .declare i32 true (.binary i32 .add (.variable i32 1) (.variable i32 3))
abbrev wLeaf : NStmt := .write (.local 0) u64 wIdx (.variable u64 2)
abbrev bodyCmdS : Command := .sequence (.primitive declN) (.sequence (.primitive setN) (.sequence (.primitive declI)
  (.sequence (.primitive wLeaf) (.sequence (.primitive halveI) (.sequence loopCS (.primitive .skip))))))

theorem body_eqS : Proofs.SegtreeSumInstance.segtree_sum_set_std_vector_unsigned_long_long.body = bodyCmdS := rfl

theorem envS1 (P : List Cell) (idx val n i : Nat) (h : idx < 2147483648) : penv1 (stS P idx val n i) 1 i32 = some (idx : Int) :=
  gS_env P (L4 idx val n i) 0 (ci idx) rfl (validN idx h)
theorem envS2 (P : List Cell) (idx val n i : Nat) (h : val < 18446744073709551616) : penv1 (stS P idx val n i) 2 u64 = some (val : Int) :=
  gS_env P (L4 idx val n i) 1 (cu val) rfl (u64_lt val h)
theorem envS3 (P : List Cell) (idx val n i : Nat) (h : n < 2147483648) : penv1 (stS P idx val n i) 3 i32 = some (n : Int) :=
  gS_env P (L4 idx val n i) 2 (ci n) rfl (validN n h)
theorem envS4 (P : List Cell) (idx val n i : Nat) (h : i < 2147483648) : penv1 (stS P idx val n i) 4 i32 = some (i : Int) :=
  gS_env P (L4 idx val n i) 3 (ci i) rfl (validN i h)

theorem wIdx_den (P : List Cell) (idx val n i : Nat) (h : i < 2147483648) :
    wIdx.denote (penv1 (stS P idx val n i)) = some (i : Int) := by
  rw [den_cast, den_variable, envS4 P idx val n i h, Option.bind_some, convert_u64]
  congr 1
  exact Int.emod_eq_of_lt (by omega) (by omega)

theorem mul2_den (env : Nat → Ty → Option Int) (i : Nat) (e : env 4 i32 = some (i : Int)) (h : 2 * i < 2147483648) :
    (NExpr.binary i32 .mul (.literal i32 2) (.variable i32 4)).denote env = some ((2 * i : Nat) : Int) := by
  rw [den_binary, den_literal, if_pos (show i32.valid 2 = true from rfl), Option.bind_some, den_variable, e, Option.bind_some]
  have : binaryValue .mul (2 : Int) (i : Int) = ((2 * i : Nat) : Int) := by
    show (2 : Int) * (i : Int) = _; push_cast; rfl
  rw [this]
  exact conv_signed i32 rfl rfl _ (validN _ h)

theorem idx2i_den (P : List Cell) (idx val n i : Nat) (h : 2 * i < 2147483648) :
    idx2i.denote (penv1 (stS P idx val n i)) = some ((2 * i : Nat) : Int) := by
  rw [den_cast, mul2_den _ i (envS4 P idx val n i (by omega)) h, Option.bind_some, convert_u64]
  congr 1
  exact Int.emod_eq_of_lt (by omega) (by omega)

theorem idx2i1_den (P : List Cell) (idx val n i : Nat) (h : 2 * i + 1 < 2147483648) :
    idx2i1.denote (penv1 (stS P idx val n i)) = some ((2 * i + 1 : Nat) : Int) := by
  rw [den_cast, den_binary, mul2_den _ i (envS4 P idx val n i (by omega)) (by omega), Option.bind_some,
    den_literal, if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
  have : binaryValue .add ((2 * i : Nat) : Int) 1 = ((2 * i + 1 : Nat) : Int) := by
    show ((2 * i : Nat) : Int) + 1 = _; push_cast; rfl
  rw [this, conv_signed i32 rfl rfl _ (validN _ h), Option.bind_some, convert_u64]
  congr 1
  exact Int.emod_eq_of_lt (by omega) (by omega)

theorem sumE_val (vec : List Int) (P : List Cell) (idx val n i : Nat) (x1 x2 : Nat) (h : 2 * i + 1 < 2147483648)
    (hx1 : vec[2 * i]? = some (x1 : Int)) (hx2 : vec[2 * i + 1]? = some (x2 : Int))
    (v1 : u64.valid (x1 : Int) = true) (v2 : u64.valid (x2 : Int) = true) :
    vdenL u64 vec (penv1 (stS P idx val n i)) sumE = some (((x1 + x2) % M64 : Nat) : Int) := by
  have hb : sumE.scalarOnly = false := rfl
  have hr1 : (NExpr.read u64 (.local 0) idx2i).scalarOnly = false := rfl
  have hr2 : (NExpr.read u64 (.local 0) idx2i1).scalarOnly = false := rfl
  have r1 : vdenL u64 vec (penv1 (stS P idx val n i)) (NExpr.read u64 (.local 0) idx2i) = some (x1 : Int) := by
    rw [vdenL_read _ _ _ _ _ hr1, if_pos ⟨rfl, rfl⟩, idx2i_den P idx val n i (by omega), Option.bind_some]
    unfold elemAtL
    rw [if_pos (Int.natCast_nonneg _), Int.toNat_natCast, hx1, Option.bind_some, if_pos v1]
  have r2 : vdenL u64 vec (penv1 (stS P idx val n i)) (NExpr.read u64 (.local 0) idx2i1) = some (x2 : Int) := by
    rw [vdenL_read _ _ _ _ _ hr2, if_pos ⟨rfl, rfl⟩, idx2i1_den P idx val n i h, Option.bind_some]
    unfold elemAtL
    rw [if_pos (Int.natCast_nonneg _), Int.toNat_natCast, hx2, Option.bind_some, if_pos v2]
  rw [vdenL_binary _ _ _ _ _ _ _ hb, r1, r2, Option.bind_some, Option.bind_some]
  have : binaryValue .add (x1 : Int) (x2 : Int) = ((x1 + x2 : Nat) : Int) := by
    show (x1 : Int) + (x2 : Int) = _; push_cast; rfl
  rw [this, convert_u64]
  congr 1

theorem condI_val (vec : List Int) (P : List Cell) (idx val n i : Nat) (h : i < 2147483648) :
    vdenL u64 vec (penv1 (stS P idx val n i)) condI = some (if 1 ≤ i then 1 else 0) := by
  have hs : condI.scalarOnly = true := rfl
  rw [vdenL_scalar _ _ _ _ hs, den_binary, den_variable, envS4 P idx val n i h, Option.bind_some,
    den_literal, if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
  have : binaryValue .ge (i : Int) 1 = if 1 ≤ i then 1 else 0 := by
    show (if (i : Int) ≥ 1 then 1 else 0) = _
    by_cases hh : 1 ≤ i
    · have : (i : Int) ≥ 1 := by omega
      simp [hh]
    · have : ¬ ((i : Int) ≥ 1) := by omega
      simp [hh]
  rw [this]
  simp only [bT]; unfold Ty.convert
  by_cases hh : 1 ≤ i <;> simp [hh]

theorem halveI_val (vec : List Int) (P : List Cell) (idx val n i : Nat) (h : i < 2147483648) :
    vdenL u64 vec (penv1 (stS P idx val n i)) (.divrem i32 false (.variable i32 4) (.literal i32 2)) = some ((i / 2 : Nat) : Int) := by
  have hs : (NExpr.divrem i32 false (.variable i32 4) (.literal i32 2)).scalarOnly = true := rfl
  rw [vdenL_scalar _ _ _ _ hs, dr2_den _ false 4 i (envS4 P idx val n i h), quo2_val i h]

theorem declI_val (vec : List Int) (P : List Cell) (idx val n i : Nat) (hi : idx < 2147483648) (hn : n < 2147483648)
    (h : idx + n < 2147483648) :
    vdenL u64 vec (penv1 (stS P idx val n i)) (.binary i32 .add (.variable i32 1) (.variable i32 3)) = some ((idx + n : Nat) : Int) := by
  have hs : (NExpr.binary i32 .add (.variable i32 1) (.variable i32 3)).scalarOnly = true := rfl
  rw [vdenL_scalar _ _ _ _ hs, den_binary, den_variable, envS1 P idx val n i hi, Option.bind_some, den_variable,
    envS3 P idx val n i hn, Option.bind_some]
  have : binaryValue .add (idx : Int) (n : Int) = ((idx + n : Nat) : Int) := by
    show (idx : Int) + (n : Int) = _; push_cast; rfl
  rw [this]
  exact conv_signed i32 rfl rfl _ (validN _ h)

theorem valE_val (vec : List Int) (P : List Cell) (idx val n i : Nat) (h : val < 18446744073709551616) :
    vdenL u64 vec (penv1 (stS P idx val n i)) (.variable u64 2) = some (val : Int) := by
  rw [vdenL_scalar _ _ _ _ rfl, den_variable]; exact envS2 P idx val n i h

theorem stS_len (P : List Cell) (idx val n i idx' val' n' i' : Nat) :
    (stS P idx' val' n' i').mem.length = (stS P idx val n i).mem.length ∧
      (stS P idx' val' n' i').bs.length = (stS P idx val n i).bs.length := by
  simp [gS_mem_len, gS_bs_len]

theorem stS_take (P : List Cell) (idx val n i idx' val' n' i' : Nat) :
    (⟨(stS P idx' val' n' i').mem.take (stS P idx val n i).mem.length,
      (stS P idx' val' n' i').bs.take (stS P idx val n i).bs.length⟩ : PS) = stS P idx' val' n' i' :=
  Proofs.PexecKit.scope_take _ _ (stS_len P idx val n i idx' val' n' i').1 (stS_len P idx val n i idx' val' n' i').2

theorem stS_setI (vec : List Int) (P : List Cell) (idx val n i i' : Nat) (e : NExpr)
    (hv : vdenL u64 vec (penv1 (stS P idx val n i)) e = some (i' : Int)) (hi' : i' < 2147483648) (hi : i < 2147483648) :
    pstmtW u64 (.assign 4 i32 e) (stS P idx val n i) vec =
      some ⟨stS P idx val n i', vec, none, (vwp e).1 + 1, P.length + 2 * 4 + (vwp e).2 + 2, 0⟩ := by
  have := gS_assign u64 P (L4 idx val n i) vec 3 (by simp) i32 e (i' : Int) (i' : Int) hv (ci i) rfl rfl (validN i hi)
    (conv_signed i32 rfl rfl _ (validN i' hi'))
  exact this

theorem set_iter (vec : List Int) (v : List Nat) (hvec : vec = v.map (fun x : Nat => (x : Int))) (hvM : ∀ x ∈ v, x < M64)
    (P : List Cell) (idx val N i : Nat) (hi1 : 1 ≤ i) (hiN : i < N) (hlen : v.length = 2 * N)
    (hN : v.length < 2147483648) (fu : Nat) :
    ∃ r1, pexecW u64 fu loopBodyS (stS P idx val N i) vec = some r1 ∧ r1.ps = stS P idx val N (i / 2) ∧
      r1.vec = (v.set i ((v.getD (2 * i) 0 + v.getD (2 * i + 1) 0) % M64)).map (fun x : Nat => (x : Int)) ∧
      r1.ret = none ∧ r1.cost ≤ 300 ∧ r1.need ≤ P.length + 100 ∧ r1.wk = 1 := by
  have h1 : 2 * i < v.length := by omega
  have h2 : 2 * i + 1 < v.length := by omega
  have hx1 := vec_get vec v hvec (2 * i) h1
  have hx2 := vec_get vec v hvec (2 * i + 1) h2
  have sv := sumE_val vec P idx val N i (v.getD (2 * i) 0) (v.getD (2 * i + 1) 0) (by omega) hx1 hx2
    (u64_lt _ (getD_lt v hvM _ h1)) (u64_lt _ (getD_lt v hvM _ h2))
  have hxl : vec.length = v.length := by rw [hvec]; simp
  have w := pstmtW_write_ok u64 (stS P idx val N i) vec wIdx sumE
    (((v.getD (2 * i) 0 + v.getD (2 * i + 1) 0) % M64 : Nat) : Int) i sv (wIdx_den P idx val N i (by omega))
    (by omega) (u64_lt _ (Nat.mod_lt _ (by decide)))
  have q1 := (pexecW_prim u64 fu wStmt _ _).trans w
  have hv2 := halveI_val (vec.set i (((v.getD (2 * i) 0 + v.getD (2 * i + 1) 0) % M64 : Nat) : Int)) P idx val N i (by omega)
  have s2 := stS_setI (vec.set i (((v.getD (2 * i) 0 + v.getD (2 * i + 1) 0) % M64 : Nat) : Int)) P idx val N i (i / 2) _ hv2
    (by omega) (by omega)
  have q2 := (pexecW_prim u64 fu halveI _ _).trans s2
  have t2 := seqW_some q2 rfl (pexecW_skip u64 fu (stS P idx val N (i / 2))
    (vec.set i (((v.getD (2 * i) 0 + v.getD (2 * i + 1) 0) % M64 : Nat) : Int)))
  have t1 := seqW_some q1 rfl t2
  have sc := pexecW_scope u64 fu _ _ _ _ t1
  simp only [stS_take] at sc
  have fin := seqW_some sc rfl (pexecW_skip u64 fu (stS P idx val N (i / 2))
    (vec.set i (((v.getD (2 * i) 0 + v.getD (2 * i + 1) 0) % M64 : Nat) : Int)))
  refine ⟨_, fin, rfl, ?_, rfl, ?_, ?_, ?_⟩
  · show vec.set i _ = _
    rw [hvec, List.map_set]
  · simp [vwp, NExpr.nodes, Container.nodes]
  · simp [vwp, NExpr.nodes, Container.nodes, gS_size]
  · simp

theorem vwp_condI : vwp condI = (3, 3) := by decide

theorem mem_set_lt (v : List Nat) (i x : Nat) (hx : x < M64) (hv : ∀ y ∈ v, y < M64) : ∀ y ∈ v.set i x, y < M64 := by
  intro y hy
  rcases List.mem_or_eq_of_mem_set hy with h | h
  · exact hv y h
  · rw [h]; exact hx

theorem set_loop (P : List Cell) (idx val N : Nat) (hidx : idx < 2147483648) (hval : val < M64) (hN : 2 * N < 2147483648) :
    ∀ (i : Nat) (v : List Nat) (vec : List Int), vec = v.map (fun x : Nat => (x : Int)) → (∀ x ∈ v, x < M64) →
      v.length = 2 * N → i < N → SInv v N i → ∀ fu, stepsL i + 1 ≤ fu →
      ∃ (res : PRW) (v' : List Nat), pexecW u64 fu loopCS (stS P idx val N i) vec = some res ∧
        (∃ i', res.ps = stS P idx val N i') ∧ res.vec = v'.map (fun x : Nat => (x : Int)) ∧ v'.length = v.length ∧
        (∀ x ∈ v', x < M64) ∧ (∀ k, N ≤ k → v'.getD k 0 = v.getD k 0) ∧
        (∀ j, 1 ≤ j → j < N → v'.getD j 0 % M64 = (v'.getD (2 * j) 0 + v'.getD (2 * j + 1) 0) % M64) ∧
        res.ret = none ∧ res.cost ≤ 330 * stepsL i + 10 ∧ res.need ≤ P.length + 100 ∧ res.wk = stepsL i := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro v vec hvec hvM hlen hiN hS fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := condI_val vec P idx val N i (by omega)
    by_cases hi1 : 1 ≤ i
    · rw [if_pos hi1] at hc
      obtain ⟨r1, h1, p1, v1, ret1, c1, n1, w1⟩ :=
        set_iter vec v hvec hvM P idx val N i hi1 hiN hlen (by omega) (fu' + 1)
      have hS' := sinv_step v N i hS hi1 hiN hlen
      have hm' : stepsL i = 1 + stepsL (i / 2) := stepsL_succ i (by omega)
      obtain ⟨r2, v', h2, ⟨i2, hps2⟩, hv2, hl2, hM2, hleaf2, htree2, ret2, c2, n2, w2⟩ :=
        ih (i / 2) (by omega) _ _ v1 (by
            intro x hx; exact mem_set_lt v i _ (Nat.mod_lt _ (by decide)) hvM x hx)
          (by simp [hlen]) (by omega) hS' fu' (by omega)
      rw [v1] at h2
      rw [pexecW_while, hc]
      simp only [Bind.bind, Option.bind, int_one_ne, ite_false, h1, ret1, p1, v1, h2, vwp_condI]
      refine ⟨⟨r2.ps, r2.vec, r2.ret, 3 + 1 + r1.cost + r2.cost, max ((stS P idx val N i).mem.length +
        (stS P idx val N i).bs.length + 3 + 2) (max r1.need r2.need), r1.wk + r2.wk⟩, v', by simp, ⟨i2, hps2⟩, hv2, ?_,
        hM2, ?_, htree2, ret2, ?_, ?_, ?_⟩
      · rw [hl2]; simp
      · intro k hk
        rw [hleaf2 k hk, getD_setE]
        have : ¬ (k = i ∧ i < v.length) := by omega
        rw [if_neg this]
      · simp <;> omega
      · simp [gS_size, n1, n2] <;> omega
      · simp [w1, w2]; omega
    · rw [if_neg hi1] at hc
      have hi0 : i = 0 := by omega
      subst hi0
      rw [pexecW_while, hc]
      simp only [Bind.bind, Option.bind, ite_true, vwp_condI]
      refine ⟨_, v, rfl, ⟨0, rfl⟩, hvec, rfl, hvM, fun k _ => rfl, sinv_zero v N hS, rfl, ?_, ?_, ?_⟩
      · simp [stepsL]
      · simp [gS_size]
      · simp [stepsL]

abbrev L2s (idx val : Nat) : List Cell := [ci idx, cu val]
abbrev L3s (idx val n : Nat) : List Cell := [ci idx, cu val, ci n]

theorem declI_val3 (vec : List Int) (P : List Cell) (idx val n : Nat) (hi : idx < 2147483648) (hn : n < 2147483648)
    (h : idx + n < 2147483648) :
    vdenL u64 vec (penv1 (gS P (L3s idx val n))) (.binary i32 .add (.variable i32 1) (.variable i32 3)) = some ((idx + n : Nat) : Int) := by
  have hs : (NExpr.binary i32 .add (.variable i32 1) (.variable i32 3)).scalarOnly = true := rfl
  have e1 : penv1 (gS P (L3s idx val n)) 1 i32 = some (idx : Int) := gS_env P (L3s idx val n) 0 (ci idx) rfl (validN idx hi)
  have e3 : penv1 (gS P (L3s idx val n)) 3 i32 = some (n : Int) := gS_env P (L3s idx val n) 2 (ci n) rfl (validN n hn)
  rw [vdenL_scalar _ _ _ _ hs, den_binary, den_variable, e1, Option.bind_some, den_variable, e3, Option.bind_some]
  have : binaryValue .add (idx : Int) (n : Int) = ((idx + n : Nat) : Int) := by
    show (idx : Int) + (n : Int) = _; push_cast; rfl
  rw [this]
  exact conv_signed i32 rfl rfl _ (validN _ h)

theorem body_execS (vec : List Int) (v : List Nat) (hvec : vec = v.map (fun x : Nat => (x : Int))) (hvM : ∀ x ∈ v, x < M64)
    (P : List Cell) (N idx val : Nat) (hT : TInv v N) (hN : v.length < 2147483648) (hidx : idx < N) (hval : val < M64)
    (fu : Nat) (hfu : stepsL ((idx + N) / 2) + 1 ≤ fu) :
    ∃ (res : PRW) (v' : List Nat), pexecW u64 fu bodyCmdS (gS P (L2s idx val)) vec = some res ∧ res.ret = none ∧
      (∃ cs, res.ps = gS P cs) ∧ res.vec = v'.map (fun x : Nat => (x : Int)) ∧ TInv v' N ∧ (∀ x ∈ v', x < M64) ∧
      v'.getD (N + idx) 0 = val ∧ (∀ m, m < N → m ≠ idx → v'.getD (N + m) 0 = v.getD (N + m) 0) ∧
      res.cost ≤ 330 * stepsL ((idx + N) / 2) + 400 ∧ res.need ≤ P.length + 100 ∧ res.wk = 1 + stepsL ((idx + N) / 2) := by
  have hvl : v.length = 2 * N := hT.2.1
  have hvlen : vec.length = 2 * N := by rw [hvec]; simp [hvl]
  have hN0 := hT.1
  have sz := size_valP vec (gS P (L2s idx val)) (by omega)
  rw [hvlen] at sz
  have d1 := gS_decl u64 P (L2s idx val) vec i32 _ ((2 * N : Nat) : Int) ((2 * N : Nat) : Int) sz
    (conv_signed i32 rfl rfl _ (validN _ (by omega)))
  have q1 := (pexecW_prim u64 fu declN _ _).trans d1
  have e3 : penv1 (gS P (L3s idx val (2 * N))) 3 i32 = some ((2 * N : Nat) : Int) :=
    gS_env P (L3s idx val (2 * N)) 2 (ci (2 * N)) rfl (validN _ (by omega))
  have hv2 : vdenL u64 vec (penv1 (gS P (L3s idx val (2 * N)))) (.divrem i32 false (.variable i32 3) (.literal i32 2)) =
      some ((N : Nat) : Int) := by
    have hs : (NExpr.divrem i32 false (.variable i32 3) (.literal i32 2)).scalarOnly = true := rfl
    rw [vdenL_scalar _ _ _ _ hs, dr2_den _ false 3 (2 * N) e3, quo2_val (2 * N) (by omega)]
    have : 2 * N / 2 = N := by omega
    rw [this]
  have s2 := gS_assign u64 P (L3s idx val (2 * N)) vec 2 (by simp) i32 _ ((N : Nat) : Int) ((N : Nat) : Int) hv2
    (ci (2 * N)) rfl rfl (validN _ (by omega)) (conv_signed i32 rfl rfl _ (validN _ (by omega)))
  have q2 := (pexecW_prim u64 fu setN _ _).trans s2
  have dI := gS_decl u64 P (L3s idx val N) vec i32 _ ((idx + N : Nat) : Int) ((idx + N : Nat) : Int)
    (declI_val3 vec P idx val N (by omega) (by omega) (by omega)) (conv_signed i32 rfl rfl _ (validN _ (by omega)))
  have q3 := (pexecW_prim u64 fu declI _ _).trans dI
  -- the leaf write
  have hw := pstmtW_write_ok u64 (stS P idx val N (idx + N)) vec wIdx (.variable u64 2) (val : Int) (idx + N)
    (valE_val vec P idx val N (idx + N) hval) (wIdx_den P idx val N (idx + N) (by omega)) (by omega) (u64_lt val hval)
  have q4 := (pexecW_prim u64 fu wLeaf _ _).trans hw
  have hv5 := halveI_val (vec.set (idx + N) (val : Int)) P idx val N (idx + N) (by omega)
  have s5 := stS_setI (vec.set (idx + N) (val : Int)) P idx val N (idx + N) ((idx + N) / 2) _ hv5 (by omega) (by omega)
  have q5 := (pexecW_prim u64 fu halveI _ _).trans s5
  -- the loop
  have hv1 : vec.set (idx + N) (val : Int) = (v.set (idx + N) val).map (fun x : Nat => (x : Int)) := by
    rw [hvec, List.map_set]
  have hS := sinv_init v N (idx + N) val hT (by omega) (by omega)
  obtain ⟨rl, v', hL, ⟨i', hps⟩, hvl', hlen', hM', hleaf', htree', retL, cL, nL, wL⟩ :=
    set_loop P idx val N (by omega) hval (by omega) ((idx + N) / 2) (v.set (idx + N) val) _ hv1
      (mem_set_lt v _ val hval hvM) (by simp [hvl]) (by omega) hS fu hfu
  have h6 := seqW_some hL retL (pexecW_skip u64 fu rl.ps rl.vec)
  have h5 := seqW_some q5 rfl h6
  have h4 := seqW_some q4 rfl h5
  have h3 := seqW_some q3 rfl h4
  have h2 := seqW_some q2 rfl h3
  have h1 := seqW_some q1 rfl h2
  have hsz : rl.ps.mem.length + rl.ps.bs.length = P.length + 8 := by
    rw [hps]; simp [gS_mem_len, gS_bs_len]
  refine ⟨_, v', h1, rfl, ⟨L4 idx val N i', hps⟩, hvl', ⟨hN0, by rw [hlen']; simp [hvl], ?_⟩, hM', ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj1 hjN; exact htree' j hj1 hjN
  · rw [hleaf' (N + idx) (by omega), getD_setE]
    have : N + idx = idx + N := by omega
    rw [this, if_pos ⟨rfl, by omega⟩]
  · intro m hm hne
    rw [hleaf' (N + m) (by omega), getD_setE]
    have : ¬ (N + m = idx + N ∧ idx + N < v.length) := by omega
    rw [if_neg this]
  · simp [vwp, NExpr.nodes, Container.nodes] at *
    omega
  · simp [vwp, NExpr.nodes, Container.nodes, gS_size, nL] <;> omega
  · simp [wL]

set_option maxHeartbeats 4000000 in
theorem segtree_sum_set_correct (caller : NState) {vslot vb V vsc : Nat} {vbuf : Buffer Value}
    (ok : VOKUW caller vslot vb V vsc vbuf) (v : List Nat) (hvM : ∀ x ∈ v, x < M64)
    (hitems : vbuf.items = (v.map (fun x : Nat => (x : Int))).map Value.integer)
    (N : Nat) (hT : TInv v N) (hN : v.length < 2147483648)
    (hbvalid : vbuf.Valid (accepts (.integer u64))) (hlimit : vbuf.limit = CppVectorBindings.sizeLimit u64)
    (howner : vbuf.owner = V)
    (e1 e2 : NExpr) (idx val : Nat) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ty1 : e1.resultType = i32) (ty2 : e2.resultType = u64)
    (d1 : e1.denote (envOf caller) = some (idx : Int)) (d2 : e2.denote (envOf caller) = some (val : Int))
    (hidx : idx < N) (hval : val < M64) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState) (v' : List Nat),
      prepare caller Proofs.SegtreeSumInstance.segtree_sum_set_std_vector_unsigned_long_long.parameters
        [.vectorReference vslot,.value e1,.value e2] = some Sinit ∧
      Proofs.SegtreeSumInstance.segtree_sum_set_std_vector_unsigned_long_long.callFuel fuel caller [.vectorReference vslot,.value e1,.value e2] =
        .finished (res,Ret.unit) ∧
      TInv v' N ∧ (∀ x ∈ v', x < M64) ∧ v'.getD (N + idx) 0 = val ∧
      (∀ m, m < N → m ≠ idx → v'.getD (N + m) 0 = v.getD (N + m) 0) ∧
      ScalarPost3 caller Sinit res (e1.nodes + e2.nodes) (330 * Nat.log2 N + 800) caller.scalars.memory (Nat.log2 N + 3) V
        (v'.map (fun x : Nat => (x : Int))) := by
  have hvl : v.length = 2 * N := hT.2.1
  obtain ⟨t1,t2,g1,g2,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_ss caller ok e1 e2 (idx : Int) (val : Int) hs1 hs2 ty1 ty2 d1 d2 (validN idx (by omega)) (u64_lt val hval)
  let vc : VCtx := ⟨u64,true,true,V,vsc,vbuf,v.map (fun x : Nat => (x : Int)),hitems,fun _ => rfl,
    by simp; omega,caller.frame.state.liveSpace,caller.frame.state.storage.work,caller.scope+1,
    caller.frame.state.storage.objects.length⟩
  have fwS : FW vc (v.map (fun x : Nat => (x : Int))) vbuf 0 Sinit.frame := by
    rw [sFrame]
    refine ⟨ok.valid,ok.lengths,rfl,rfl,?_,rfl,rfl,ok.vtag,ok.vfound,ok.flag,hitems,hbvalid,hlimit,howner,by simp; omega⟩
    intro owner k h
    have := ok.strict owner k h
    show k < caller.scope+1
    omega
  have hsteps : stepsL ((idx + N) / 2) ≤ Nat.log2 N + 1 := by
    have h1 : (idx + N) / 2 ≤ N := by omega
    exact Nat.le_trans (stepsL_mono N _ h1) (stepsL_log N)
  obtain ⟨rr,v',hexec,hret,⟨cs,hrps⟩,hrvec,hT',hM',hleaf,hothers,hcost,hneed,hwk⟩ :=
    body_execS (v.map (fun x : Nat => (x : Int))) v rfl hvM (callerP caller) N idx val hT hN hidx hval
      (stepsL ((idx + N) / 2) + 1) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(idx : Int)⟩ : Cell),(⟨u64,(val : Int)⟩ : Cell)]).take caller.scalars.memory.length =
      caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(idx : Int)⟩ : Cell),(⟨u64,(val : Int)⟩ : Cell)],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]⟩ : PS) = gS (callerP caller) (L2s idx val) := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  have gw2 := g2.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1
  have hpost := call_vecw_unit vc true (fun _ => ⟨rfl,rfl⟩) caller Proofs.SegtreeSumInstance.segtree_sum_set_std_vector_unsigned_long_long
    [.vectorReference vslot,.value e1,.value e2] Sinit
    (callerP caller ++ [(⟨i32,(idx : Int)⟩ : Cell),(⟨u64,(val : Int)⟩ : Cell)])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok.base (by decide) (stepsL ((idx + N) / 2) + 1) rr
    (by rw [hmk]; exact hexec) hret rfl (by omega) (by simp) (e1.nodes + e2.nodes)
    (330 * Nat.log2 N + 800) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,v',hprep,hrun,hT',hM',hleaf,hothers,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvec] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) (by omega)

end Program

end Proofs.SegtreeSumCall
