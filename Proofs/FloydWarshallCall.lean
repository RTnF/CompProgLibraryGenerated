import Proofs.ForLoop
import Proofs.Generated.FloydWarshall

namespace Proofs.FloydWarshallCall

/-- The Floyd-Warshall recurrence on a weight matrix `W`: shortest distances through the vertices `< k`. -/
def Dm (W : Nat → Nat → Nat) : Nat → Nat → Nat → Nat
  | 0 => W
  | k + 1 => fun i j => min (Dm W k i j) (Dm W k i k + Dm W k k j)

theorem Dm_stable_col (W : Nat → Nat → Nat) (k i : Nat) : Dm W (k + 1) i k = Dm W k i k := by
  simp only [Dm]
  omega

theorem Dm_stable_row (W : Nat → Nat → Nat) (k j : Nat) : Dm W (k + 1) k j = Dm W k k j := by
  simp only [Dm]
  omega

theorem Dm_le (W : Nat → Nat → Nat) : ∀ k i j, Dm W k i j ≤ W i j := by
  intro k
  induction k with
  | zero => intro i j; simp [Dm]
  | succ k ih => intro i j; simp only [Dm]; exact Nat.le_trans (Nat.min_le_left _ _) (ih i j)

/-- Matrix after the rows `< i` and the first `j` entries of row `i` were processed in round `k`. -/
def Em (W : Nat → Nat → Nat) (k i j p q : Nat) : Nat :=
  if p < i ∨ (p = i ∧ q < j) then Dm W (k + 1) p q else Dm W k p q

theorem Em_col (W : Nat → Nat → Nat) (k i j p : Nat) : Em W k i j p k = Dm W k p k := by
  unfold Em
  split
  · exact Dm_stable_col W k p
  · rfl

theorem Em_row (W : Nat → Nat → Nat) (k i j q : Nat) : Em W k i j k q = Dm W k k q := by
  unfold Em
  split
  · exact Dm_stable_row W k q
  · rfl

theorem Em_here (W : Nat → Nat → Nat) (k i j : Nat) : Em W k i j i j = Dm W k i j := by
  unfold Em
  split
  · omega
  · rfl

theorem Em_next (W : Nat → Nat → Nat) (k i j : Nat) : Em W k i (j + 1) i j = Dm W (k + 1) i j := by
  unfold Em
  rw [if_pos (by omega)]

theorem Em_other (W : Nat → Nat → Nat) (k i j p q : Nat) (h : ¬ (p = i ∧ q = j)) :
    Em W k i (j + 1) p q = Em W k i j p q := by
  unfold Em
  by_cases h1 : p < i ∨ (p = i ∧ q < j)
  · rw [if_pos h1, if_pos (by omega)]
  · rw [if_neg h1, if_neg (by omega)]

theorem Em_row_end (W : Nat → Nat → Nat) (k i n p q : Nat) (hq : q < n) : Em W k i n p q = Em W k (i + 1) 0 p q := by
  unfold Em
  by_cases h : p < i ∨ (p = i ∧ q < n)
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

theorem Em_start (W : Nat → Nat → Nat) (k p q : Nat) : Em W k 0 0 p q = Dm W k p q := by
  unfold Em
  rw [if_neg (by omega)]

theorem Em_end (W : Nat → Nat → Nat) (k n p q : Nat) (hp : p < n) : Em W k n 0 p q = Dm W (k + 1) p q := by
  unfold Em
  rw [if_pos (by omega)]

theorem idx_inj (n p q p' q' : Nat) (hq : q < n) (hq' : q' < n) (h : p * n + q = p' * n + q') : p = p' ∧ q = q' := by
  have h1 : (p * n + q) / n = p := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hq]; omega
  have h2 : (p' * n + q') / n = p' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hq']; omega
  have h3 : (p * n + q) % n = q := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq]
  have h4 : (p' * n + q') % n = q' := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq']
  rw [h] at h1 h3
  exact ⟨h1.symm.trans h2, h3.symm.trans h4⟩

/-- Walks from `i` to `j` of total length `L` whose intermediate vertices are all `< k`, in the complete digraph with edge
lengths `W` (a walk is a single edge, or two walks joined at an intermediate vertex `m < k`). -/
inductive Walk (W : Nat → Nat → Nat) : Nat → Nat → Nat → Nat → Prop
  | edge (k i j : Nat) : Walk W k i j (W i j)
  | join (k i m j L1 L2 : Nat) : Walk W k i m L1 → m < k → Walk W k m j L2 → Walk W k i j (L1 + L2)

theorem Walk.mono (W : Nat → Nat → Nat) {k k' i j L : Nat} (h : Walk W k i j L) (hk : k ≤ k') : Walk W k' i j L :=
  match h with
  | .edge _ _ _ => .edge _ _ _
  | .join _ _ m _ _ _ h1 hm h2 => .join _ _ m _ _ _ (Walk.mono W h1 hk) (by omega) (Walk.mono W h2 hk)

theorem Dm_tri (W : Nat → Nat → Nat) : ∀ k m, m < k → ∀ i j, Dm W k i j ≤ Dm W k i m + Dm W k m j := by
  intro k
  induction k with
  | zero => intro m hm; omega
  | succ k ih =>
    intro m hm i j
    by_cases hmk : m = k
    · subst hmk
      rw [Dm_stable_col W m i, Dm_stable_row W m j]
      simp only [Dm]
      omega
    · have hm' : m < k := by omega
      have t1 := ih m hm' i j
      have t3 := ih m hm' i k
      have t4 := ih m hm' k j
      simp only [Dm]
      omega

theorem Walk_ge (W : Nat → Nat → Nat) {k i j L : Nat} (h : Walk W k i j L) : Dm W k i j ≤ L :=
  match h with
  | .edge _ _ _ => Dm_le W _ _ _
  | .join _ _ m _ L1 L2 h1 hm h2 => by
    have a1 := Walk_ge W h1
    have a2 := Walk_ge W h2
    have := Dm_tri W _ m hm i j
    omega

theorem Walk_exists (W : Nat → Nat → Nat) : ∀ k i j, Walk W k i j (Dm W k i j) := by
  intro k
  induction k with
  | zero => intro i j; exact Walk.edge 0 i j
  | succ k ih =>
    intro i j
    simp only [Dm]
    by_cases h : Dm W k i j ≤ Dm W k i k + Dm W k k j
    · rw [Nat.min_eq_left h]; exact (ih i j).mono W (by omega)
    · rw [Nat.min_eq_right (by omega)]
      exact Walk.join (k + 1) i k j _ _ ((ih i k).mono W (by omega)) (by omega) ((ih k j).mono W (by omega))

section Program
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.ForLoop
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.VecKit Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN env_gen)

abbrev fidx (a b : Nat) : NExpr :=
  .cast u64 (.binary i32 .add (.binary i32 .mul (.variable i32 a) (.variable i32 1)) (.variable i32 b))
abbrev idxIK : NExpr := fidx 3 2
abbrev idxKJ : NExpr := fidx 2 4
abbrev idxIJ : NExpr := fidx 3 4
abbrev rdE (e : NExpr) : NExpr := .read s64 (.local 0) e
abbrev declVia : NStmt := .declare s64 true (.binary s64 .add (rdE idxIK) (rdE idxKJ))
abbrev condV : NExpr := .binary bT .lt (.variable s64 5) (rdE idxIJ)
abbrev wrV : NStmt := .write (.local 0) s64 idxIJ (.variable s64 5)
abbrev BJ : Command := .sequence (.primitive declVia) (.sequence (.branch condV
  (.sequence (.scope (.sequence (.primitive wrV) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (.primitive .skip))
abbrev BI : Command := .sequence (forStmt 3 BJ) (.primitive .skip)
abbrev BK : Command := .sequence (forStmt 2 BI) (.primitive .skip)
abbrev bodyFW : Command := .sequence (forStmt 1 BK) (.primitive .skip)

theorem body_eqF : Proofs.FloydWarshallInstance.floyd_warshall_std_vector_long_long.body = bodyFW := rfl

open Proofs.FenwickCall (pexecW_branch_trueB pexecW_branch_falseB)

abbrev cv (x : Nat) : Cell := ⟨s64, (x : Int)⟩

theorem fidx_den (env : Nat → Ty → Option Int) (a b na nb n : Nat) (h1 : env 1 i32 = some (n : Int))
    (ha : env a i32 = some (na : Int)) (hb : env b i32 = some (nb : Int)) (hlt : na * n + nb < 2147483648) :
    (fidx a b).denote env = some ((na * n + nb : Nat) : Int) := by
  have hm : na * n < 2147483648 := by omega
  rw [den_cast, den_binary, den_binary, den_variable, ha, Option.bind_some, den_variable, h1, Option.bind_some]
  have e1 : binaryValue .mul (na : Int) (n : Int) = ((na * n : Nat) : Int) := by
    show (na : Int) * (n : Int) = _; push_cast; rfl
  rw [e1, conv_signed i32 rfl rfl _ (validN _ hm), Option.bind_some, den_variable, hb, Option.bind_some]
  have e2 : binaryValue .add ((na * n : Nat) : Int) (nb : Int) = ((na * n + nb : Nat) : Int) := by
    show ((na * n : Nat) : Int) + (nb : Int) = _; push_cast; rfl
  rw [e2, conv_signed i32 rfl rfl _ (validN _ hlt), Option.bind_some, convert_u64]
  congr 1
  exact Int.emod_eq_of_lt (by omega) (by omega)

theorem rd_val (vec : List Int) (env : Nat → Ty → Option Int) (e : NExpr) (idx : Nat) (x : Nat)
    (he : e.denote env = some (idx : Int)) (hs : e.scalarOnly = true)
    (hx : vec[idx]? = some (x : Int)) (hxv : s64.valid (x : Int) = true) :
    vdenL s64 vec env (rdE e) = some (x : Int) := by
  have hrc : (rdE e).scalarOnly = false := rfl
  rw [vdenL_read _ _ _ _ _ hrc, if_pos ⟨rfl, hs⟩, he, Option.bind_some]
  unfold elemAtL
  rw [if_pos (Int.natCast_nonneg idx), Int.toNat_natCast, hx, Option.bind_some, if_pos hxv]

theorem vec_getF (vec : List Int) (v : List Nat) (hvec : vec = v.map (fun x : Nat => (x : Int))) (j : Nat) (hj : j < v.length) :
    vec[j]? = some ((v.getD j 0 : Nat) : Int) := by
  subst hvec
  simp [List.getElem?_map, hj, List.getD_eq_getElem?_getD]

theorem idx_lt (n i k : Nat) (hi : i < n) (hk : k < n) : i * n + k < n * n := by
  have : (i + 1) * n ≤ n * n := Nat.mul_le_mul_right n hi
  rw [Nat.add_mul] at this
  omega

abbrev C4 (n k i j : Nat) : List Cell := [ci n, ci k, ci i, ci j]
abbrev C5 (n k i j via : Nat) : List Cell := [ci n, ci k, ci i, ci j, cv via]

theorem env4 (P : List Cell) (n k i j : Nat) (hn : n < 2147483648) (hk : k < 2147483648) (hi : i < 2147483648)
    (hj : j < 2147483648) (via : Nat) :
    (∀ cs : List Cell, cs = C4 n k i j ∨ cs = C5 n k i j via →
      penv1 (gS P cs) 1 i32 = some (n : Int) ∧ penv1 (gS P cs) 2 i32 = some (k : Int) ∧
        penv1 (gS P cs) 3 i32 = some (i : Int) ∧ penv1 (gS P cs) 4 i32 = some (j : Int)) := by
  intro cs hcs
  rcases hcs with rfl | rfl
  · exact ⟨gS_env P _ 0 (ci n) rfl (validN n hn), gS_env P _ 1 (ci k) rfl (validN k hk),
      gS_env P _ 2 (ci i) rfl (validN i hi), gS_env P _ 3 (ci j) rfl (validN j hj)⟩
  · exact ⟨gS_env P _ 0 (ci n) rfl (validN n hn), gS_env P _ 1 (ci k) rfl (validN k hk),
      gS_env P _ 2 (ci i) rfl (validN i hi), gS_env P _ 3 (ci j) rfl (validN j hj)⟩

theorem s64v (x : Nat) (h : x < 9223372036854775808) : s64.valid (x : Int) = true := by
  rw [valid_s64]; exact decide_eq_true ⟨by omega, by omega⟩

theorem lt_bT (a b : Nat) : bT.convert (binaryValue .lt (a : Int) (b : Int)) = some (if a < b then 1 else 0) := by
  have : binaryValue .lt (a : Int) (b : Int) = if a < b then 1 else 0 := by
    show (if (a : Int) < (b : Int) then 1 else 0) = _
    by_cases h : a < b
    · have : (a : Int) < (b : Int) := by omega
      simp [h]
    · have : ¬ ((a : Int) < (b : Int)) := by omega
      simp [h]
  rw [this]
  simp only [bT]; unfold Ty.convert
  by_cases h : a < b <;> simp [h]

theorem fw_jbody (vec : List Int) (v : List Nat) (hvec : vec = v.map (fun x : Nat => (x : Int)))
    (hvB : ∀ x ∈ v, x < 4611686018427387904) (P : List Cell) (n k i j : Nat) (hk : k < n) (hi : i < n) (hj : j < n)
    (hnn : n * n < 2147483648) (hlen : v.length = n * n) (fu : Nat) :
    ∃ r : PRW, pexecW s64 fu BJ (gS P (C4 n k i j)) vec = some r ∧ r.ret = none ∧
      r.ps = gS P (C4 n k i j ++ [cv (v.getD (i * n + k) 0 + v.getD (k * n + j) 0)]) ∧
      r.vec = (if v.getD (i * n + k) 0 + v.getD (k * n + j) 0 < v.getD (i * n + j) 0 then
        v.set (i * n + j) (v.getD (i * n + k) 0 + v.getD (k * n + j) 0) else v).map (fun x : Nat => (x : Int)) ∧
      r.cost ≤ 400 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 1 := by
  have hn32 : n < 2147483648 := by
    have : n ≤ n * n := Nat.le_mul_self n
    omega
  have hlIK := idx_lt n i k hi hk
  have hlKJ := idx_lt n k j hk hj
  have hlIJ := idx_lt n i j hi hj
  have gv : ∀ idx, idx < n * n → v.getD idx 0 < 4611686018427387904 := by
    intro idx hidx
    have : v.getD idx 0 = v[idx]'(by omega) := by simp [List.getD_eq_getElem?_getD, hlen, hidx]
    rw [this]; exact hvB _ (List.getElem_mem _)
  have x1b := gv _ hlIK
  have x2b := gv _ hlKJ
  have x3b := gv _ hlIJ
  obtain ⟨E1, E2, E3, E4⟩ := env4 P n k i j hn32 (by omega) (by omega) (by omega) 0 (C4 n k i j) (Or.inl rfl)
  have dIK := fidx_den (penv1 (gS P (C4 n k i j))) 3 2 i k n E1 E3 E2 (by omega)
  have dKJ := fidx_den (penv1 (gS P (C4 n k i j))) 2 4 k j n E1 E2 E4 (by omega)
  have r1 := rd_val vec (penv1 (gS P (C4 n k i j))) idxIK (i * n + k) (v.getD (i * n + k) 0) dIK rfl
    (vec_getF vec v hvec _ (by omega)) (s64v _ (by omega))
  have r2 := rd_val vec (penv1 (gS P (C4 n k i j))) idxKJ (k * n + j) (v.getD (k * n + j) 0) dKJ rfl
    (vec_getF vec v hvec _ (by omega)) (s64v _ (by omega))
  have hsum : vdenL s64 vec (penv1 (gS P (C4 n k i j))) (.binary s64 .add (rdE idxIK) (rdE idxKJ)) =
      some ((v.getD (i * n + k) 0 + v.getD (k * n + j) 0 : Nat) : Int) := by
    have hb : (NExpr.binary s64 .add (rdE idxIK) (rdE idxKJ)).scalarOnly = false := rfl
    rw [vdenL_binary _ _ _ _ _ _ _ hb, r1, r2, Option.bind_some, Option.bind_some]
    have : binaryValue .add ((v.getD (i * n + k) 0 : Nat) : Int) ((v.getD (k * n + j) 0 : Nat) : Int) =
        ((v.getD (i * n + k) 0 + v.getD (k * n + j) 0 : Nat) : Int) := by
      show _ + _ = _; push_cast; rfl
    rw [this]
    exact conv_signed s64 rfl rfl _ (s64v _ (by omega))
  have d1 := gS_decl s64 P (C4 n k i j) vec s64 _ ((v.getD (i * n + k) 0 + v.getD (k * n + j) 0 : Nat) : Int)
    ((v.getD (i * n + k) 0 + v.getD (k * n + j) 0 : Nat) : Int) hsum (conv_signed s64 rfl rfl _ (s64v _ (by omega)))
  have q1 := (pexecW_prim s64 fu declVia _ _).trans d1
  -- the state after the declaration
  obtain ⟨F1, F2, F3, F4⟩ := env4 P n k i j hn32 (by omega) (by omega) (by omega)
    (v.getD (i * n + k) 0 + v.getD (k * n + j) 0) (C5 n k i j (v.getD (i * n + k) 0 + v.getD (k * n + j) 0)) (Or.inr rfl)
  have F5 : penv1 (gS P (C5 n k i j (v.getD (i * n + k) 0 + v.getD (k * n + j) 0))) 5 s64 =
      some ((v.getD (i * n + k) 0 + v.getD (k * n + j) 0 : Nat) : Int) :=
    gS_env P (C5 n k i j (v.getD (i * n + k) 0 + v.getD (k * n + j) 0)) 4 (cv _) rfl (s64v _ (by omega))
  have dIJ := fidx_den (penv1 (gS P (C5 n k i j (v.getD (i * n + k) 0 + v.getD (k * n + j) 0)))) 3 4 i j n F1 F3 F4
    (by omega)
  have r3 := rd_val vec (penv1 (gS P (C5 n k i j (v.getD (i * n + k) 0 + v.getD (k * n + j) 0)))) idxIJ (i * n + j)
    (v.getD (i * n + j) 0) dIJ rfl (vec_getF vec v hvec _ (by omega)) (s64v _ (by omega))
  have hcond : vdenL s64 vec (penv1 (gS P (C5 n k i j (v.getD (i * n + k) 0 + v.getD (k * n + j) 0)))) condV =
      some (if v.getD (i * n + k) 0 + v.getD (k * n + j) 0 < v.getD (i * n + j) 0 then 1 else 0) := by
    have hb : condV.scalarOnly = false := rfl
    have hv5 : vdenL s64 vec (penv1 (gS P (C5 n k i j (v.getD (i * n + k) 0 + v.getD (k * n + j) 0))))
        (NExpr.variable s64 5) = some ((v.getD (i * n + k) 0 + v.getD (k * n + j) 0 : Nat) : Int) := by
      rw [vdenL_scalar _ _ _ _ rfl, den_variable]; exact F5
    rw [vdenL_binary _ _ _ _ _ _ _ hb, hv5, r3, Option.bind_some, Option.bind_some]
    exact lt_bT _ _
  have hvl : vec.length = n * n := by rw [hvec]; simp [hlen]
  by_cases hlt : v.getD (i * n + k) 0 + v.getD (k * n + j) 0 < v.getD (i * n + j) 0
  · rw [if_pos hlt] at hcond
    have hx5 : vdenL s64 vec (penv1 (gS P (C5 n k i j (v.getD (i * n + k) 0 + v.getD (k * n + j) 0))))
        (NExpr.variable s64 5) = some ((v.getD (i * n + k) 0 + v.getD (k * n + j) 0 : Nat) : Int) := by
      rw [vdenL_scalar _ _ _ _ rfl, den_variable]; exact F5
    have hpI : vdenL s64 vec (penv1 (gS P (C5 n k i j (v.getD (i * n + k) 0 + v.getD (k * n + j) 0)))) idxIJ =
        some ((i * n + j : Nat) : Int) := by
      rw [vdenL_scalar _ _ _ _ rfl]; exact dIJ
    have w := pstmtW_write_ok s64 (gS P (C5 n k i j (v.getD (i * n + k) 0 + v.getD (k * n + j) 0))) vec idxIJ
      (.variable s64 5) ((v.getD (i * n + k) 0 + v.getD (k * n + j) 0 : Nat) : Int) (i * n + j) hx5 hpI (by omega)
      (s64v _ (by omega))
    have a1 := (pexecW_prim s64 fu wrV _ _).trans w
    have a2 := seqW_some a1 rfl (pexecW_skip s64 fu (gS P (C5 n k i j (v.getD (i * n + k) 0 + v.getD (k * n + j) 0)))
      (vec.set (i * n + j) ((v.getD (i * n + k) 0 + v.getD (k * n + j) 0 : Nat) : Int)))
    have a3 := pexecW_scope s64 fu _ _ _ _ a2
    have a4 := Proofs.PexecKit.scope_take (gS P (C5 n k i j (v.getD (i * n + k) 0 + v.getD (k * n + j) 0)))
      (gS P (C5 n k i j (v.getD (i * n + k) 0 + v.getD (k * n + j) 0))) rfl rfl
    simp only [a4] at a3
    have a5 := seqW_some a3 rfl (pexecW_skip s64 fu (gS P (C5 n k i j (v.getD (i * n + k) 0 + v.getD (k * n + j) 0)))
      (vec.set (i * n + j) ((v.getD (i * n + k) 0 + v.getD (k * n + j) 0 : Nat) : Int)))
    have br := pexecW_branch_trueB s64 fu condV _ (.primitive .skip) _ vec 1 hcond (by simp) _ a5
    have b1 := seqW_some br rfl (pexecW_skip s64 fu _ _)
    have b2 := seqW_some q1 rfl b1
    refine ⟨_, b2, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · rw [if_pos hlt, hvec, List.map_set]
    · simp [vwp, NExpr.nodes, Container.nodes, gS_size]
    · simp [vwp, NExpr.nodes, Container.nodes, gS_size]
    · simp
  · rw [if_neg hlt] at hcond
    have br := pexecW_branch_falseB s64 fu condV (.sequence (.scope (.sequence (.primitive wrV) (.primitive .skip))) (.primitive .skip))
      (.primitive .skip) _ vec hcond _ (pexecW_skip s64 fu _ _)
    have b1 := seqW_some br rfl (pexecW_skip s64 fu _ _)
    have b2 := seqW_some q1 rfl b1
    refine ⟨_, b2, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · rw [if_neg hlt, hvec]
    · simp [vwp, NExpr.nodes, Container.nodes, gS_size]
    · simp [vwp, NExpr.nodes, Container.nodes, gS_size]
    · simp

/-- The vector holds the matrix `Em W k i j` (entries `< 2^62`). -/
def InvF (W : Nat → Nat → Nat) (n k i j : Nat) (vec : List Int) : Prop :=
  ∃ v : List Nat, vec = v.map (fun x : Nat => (x : Int)) ∧ v.length = n * n ∧ (∀ x ∈ v, x < 4611686018427387904) ∧
    ∀ p q, p < n → q < n → v.getD (p * n + q) 0 = Em W k i j p q

theorem getD_setF (v : List Nat) (i x j : Nat) :
    (v.set i x).getD j 0 = if j = i ∧ i < v.length then x else v.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : i = j
  · subst h
    by_cases hl : i < v.length
    · simp [hl]
    · simp [hl]
  · have : ¬ (j = i) := fun e => h e.symm
    simp [h, this]

theorem jbody_step (W : Nat → Nat → Nat) (P : List Cell) (n k i : Nat) (hk : k < n) (hi : i < n) (hnn : n * n < 2147483648) :
    ∀ (t : Nat) (vec : List Int) (fu : Nat), t < n → InvF W n k i t vec → 0 ≤ fu →
      ∃ (r : PRW) (cs' : List Cell), pexecW s64 fu BJ (gS P ([ci n, ci k, ci i] ++ [ci t])) vec = some r ∧ r.ret = none ∧
        r.ps = gS P ([ci n, ci k, ci i] ++ [ci t] ++ cs') ∧ InvF W n k i (t + 1) r.vec ∧ r.cost ≤ 400 ∧
        r.need ≤ P.length + 100 ∧ r.wk ≤ 1 := by
  intro t vec fu ht hI _
  obtain ⟨v, hvec, hlen, hvB, hmat⟩ := hI
  obtain ⟨r, hr, hret, hps, hrv, hc, hn, hw⟩ := fw_jbody vec v hvec hvB P n k i t hk hi ht hnn hlen fu
  have h1 : v.getD (i * n + k) 0 = Dm W k i k := (hmat i k hi hk).trans (Em_col W k i t i)
  have h2 : v.getD (k * n + t) 0 = Dm W k k t := (hmat k t hk ht).trans (Em_row W k i t t)
  have h3 : v.getD (i * n + t) 0 = Dm W k i t := (hmat i t hi ht).trans (Em_here W k i t)
  refine ⟨r, [cv (v.getD (i * n + k) 0 + v.getD (k * n + t) 0)], hr, hret, hps, ?_, hc, hn, hw⟩
  refine ⟨if v.getD (i * n + k) 0 + v.getD (k * n + t) 0 < v.getD (i * n + t) 0 then
    v.set (i * n + t) (v.getD (i * n + k) 0 + v.getD (k * n + t) 0) else v, hrv, ?_, ?_, ?_⟩
  · split <;> simp [hlen]
  · intro x hx
    split at hx
    · rcases List.mem_or_eq_of_mem_set hx with h | h
      · exact hvB x h
      · have : v.getD (i * n + t) 0 < 4611686018427387904 := by
          have : v.getD (i * n + t) 0 = v[i * n + t]'(by have := idx_lt n i t hi ht; omega) := by
            simp [List.getD_eq_getElem?_getD, hlen, idx_lt n i t hi ht]
          rw [this]; exact hvB _ (List.getElem_mem _)
        omega
    · exact hvB x hx
  · intro p q hp hq
    by_cases hpq : p = i ∧ q = t
    · obtain ⟨rfl, rfl⟩ := hpq
      rw [Em_next]
      have hlt : p * n + q < v.length := by have := idx_lt n p q hp hq; omega
      split
      · rename_i hv
        rw [getD_setF, if_pos ⟨rfl, hlt⟩, h1, h2]
        rw [h1, h2, h3] at hv
        simp only [Dm]
        omega
      · rename_i hv
        rw [h3]
        rw [h1, h2, h3] at hv
        simp only [Dm]
        omega
    · have hne : p * n + q ≠ i * n + t := fun e => hpq (idx_inj n p q i t hq ht e)
      have hlt : i * n + t < v.length := by have := idx_lt n i t hi ht; omega
      rw [Em_other W k i t p q hpq, ← hmat p q hp hq]
      split
      · rw [getD_setF, if_neg (fun h => hne h.1)]
      · rfl

theorem n_small (n : Nat) (h : n * n < 2147483648) : n < 2147483647 := by
  by_cases h1 : n ≤ 1
  · omega
  · have : 2 * n ≤ n * n := Nat.mul_le_mul_right n (by omega)
    omega

def costJ (n : Nat) : Nat := (400 + 20) * n + 30
def costI (n : Nat) : Nat := (costJ n + 20) * n + 30
def costK (n : Nat) : Nat := (costI n + 20) * n + 30

theorem InvF_rowend (W : Nat → Nat → Nat) (n k i : Nat) (vec : List Int) (h : InvF W n k i n vec) :
    InvF W n k (i + 1) 0 vec := by
  obtain ⟨v, hv, hl, hb, hm⟩ := h
  exact ⟨v, hv, hl, hb, fun p q hp hq => by rw [hm p q hp hq, Em_row_end W k i n p q hq]⟩

theorem InvF_roundend (W : Nat → Nat → Nat) (n k : Nat) (vec : List Int) (h : InvF W n k n 0 vec) :
    InvF W n (k + 1) 0 0 vec := by
  obtain ⟨v, hv, hl, hb, hm⟩ := h
  exact ⟨v, hv, hl, hb, fun p q hp hq => by rw [hm p q hp hq, Em_end W k n p q hp, Em_start]⟩

theorem ibody_step (W : Nat → Nat → Nat) (P : List Cell) (n k : Nat) (hk : k < n) (hnn : n * n < 2147483648) :
    ∀ (i : Nat) (vec : List Int) (fu : Nat), i < n → InvF W n k i 0 vec → n + 1 ≤ fu →
      ∃ (r : PRW) (cs' : List Cell), pexecW s64 fu BI (gS P ([ci n, ci k] ++ [ci i])) vec = some r ∧ r.ret = none ∧
        r.ps = gS P ([ci n, ci k] ++ [ci i] ++ cs') ∧ InvF W n k (i + 1) 0 r.vec ∧ r.cost ≤ costJ n ∧
        r.need ≤ P.length + 100 ∧ r.wk ≤ n := by
  intro i vec fu hi hI hfu
  have hn32 : n < 2147483647 := n_small n hnn
  obtain ⟨r, hr, hps, hIn, hret, hc, hnd, hw⟩ :=
    for_stmt_run s64 P [ci n, ci k, ci i] 3 n rfl rfl (by omega) hn32 BJ (InvF W n k i) 400 100 1 0 (by omega)
      (jbody_step W P n k i hk hi hnn) vec hI fu (by omega)
  have t1 := seqW_some hr hret (by rw [hps]; exact pexecW_skip s64 fu (gS P [ci n, ci k, ci i]) r.vec)
  refine ⟨_, [], t1, rfl, ?_, InvF_rowend W n k i _ hIn, ?_, ?_, ?_⟩
  · simpa using hps
  · simp [costJ]; omega
  · simp [gS_size] at *; omega
  · simp at *; omega

theorem kbody_step (W : Nat → Nat → Nat) (P : List Cell) (n : Nat) (hnn : n * n < 2147483648) :
    ∀ (k : Nat) (vec : List Int) (fu : Nat), k < n → InvF W n k 0 0 vec → 2 * n + 2 ≤ fu →
      ∃ (r : PRW) (cs' : List Cell), pexecW s64 fu BK (gS P ([ci n] ++ [ci k])) vec = some r ∧ r.ret = none ∧
        r.ps = gS P ([ci n] ++ [ci k] ++ cs') ∧ InvF W n (k + 1) 0 0 r.vec ∧ r.cost ≤ costI n ∧
        r.need ≤ P.length + 100 ∧ r.wk ≤ n * n := by
  intro k vec fu hk hI hfu
  have hn32 : n < 2147483647 := n_small n hnn
  obtain ⟨r, hr, hps, hIn, hret, hc, hnd, hw⟩ :=
    for_stmt_run s64 P [ci n, ci k] 2 n rfl rfl (by omega) hn32 BI (fun i vec => InvF W n k i 0 vec) (costJ n) 100 n (n + 1)
      (by omega) (ibody_step W P n k hk hnn) vec hI fu (by omega)
  have t1 := seqW_some hr hret (by rw [hps]; exact pexecW_skip s64 fu (gS P [ci n, ci k]) r.vec)
  refine ⟨_, [], t1, rfl, ?_, InvF_roundend W n k _ hIn, ?_, ?_, ?_⟩
  · simpa using hps
  · simp [costI]; omega
  · simp [gS_size] at *; omega
  · simp at *; omega

theorem body_execF (W : Nat → Nat → Nat) (P : List Cell) (n : Nat) (hnn : n * n < 2147483648) (vec : List Int)
    (hI : InvF W n 0 0 0 vec) (fu : Nat) (hfu : 3 * n + 3 ≤ fu) :
    ∃ r : PRW, pexecW s64 fu bodyFW (gS P [ci n]) vec = some r ∧ r.ret = none ∧ r.ps = gS P [ci n] ∧
      InvF W n n 0 0 r.vec ∧ r.cost ≤ costK n ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ n * n * n := by
  have hn32 : n < 2147483647 := n_small n hnn
  obtain ⟨r, hr, hps, hIn, hret, hc, hnd, hw⟩ :=
    for_stmt_run s64 P [ci n] 1 n rfl rfl (by omega) hn32 BK (fun k vec => InvF W n k 0 0 vec) (costI n) 100 (n * n) (2 * n + 2)
      (by omega) (kbody_step W P n hnn) vec hI fu (by omega)
  have t1 := seqW_some hr hret (by rw [hps]; exact pexecW_skip s64 fu (gS P [ci n]) r.vec)
  refine ⟨_, t1, rfl, ?_, hIn, ?_, ?_, ?_⟩
  · simpa using hps
  · simp [costK]; omega
  · simp [gS_size] at *; omega
  · simp at *; omega

theorem prepare_fwc (caller : NState) {vslot vb V vsc : Nat} {vbuf : Buffer Value}
    (ok : VOKW caller vslot vb V vsc vbuf) (e : NExpr) (v : Int) (hs : e.scalarOnly = true)
    (hty : e.resultType = i32) (value : e.denote (envOf caller) = some v) (hv : i32.valid v = true) :
    ∃ t, Good (caller.charge 1 1) t e.nodes e.nodes ∧
      ∃ Sinit, prepare caller Proofs.FloydWarshallInstance.floyd_warshall_std_vector_long_long.parameters [.vectorReference vslot,.value e] = some Sinit ∧
        Sinit.slots = [.vector 0,.scalar 0] ∧ Sinit.scalars.memory = callerP caller ++ [⟨i32,v⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer s64,true,.root vsc⟩]⟩ ∧
        Sinit.scalars.work = t.scalars.work+3 ∧ t.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨resolved,_,_⟩ := resolve_vroot caller.frame vb V vsc s64 true true vbuf ok.binding ok.valid ok.vtag ok.vfound
    ok.lengths ok.flag (fun _ => rfl)
  have rvec : resolve caller (.vector s64 true) (.vectorReference vslot) =
      some (caller.charge 1 1,.vector V vsc s64 true) := by
    simp [resolve,ok.slot,ok.binding,resolved]
  obtain ⟨t,ran,good⟩ := scalar_eval e (caller.charge 1 1) v hs
    (by rw [envOf_core (core_charge caller 1 1)]; exact value)
  refine ⟨t,good,?_⟩
  have res : resolve (caller.charge 1 1) (.scalar i32 false true) (.value e) = some (t,.scalar i32 true v) := by
    simp [resolve,hty,ran]
  have frameT : t.frame = caller.frame := good.1.1
  have fs : t.frame.state = caller.frame.state := by rw [frameT]
  have fr : t.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t.scalars.memory = caller.scalars.memory := good.1.2.2.2.1
  have hbind : t.scalars.bindings = caller.scalars.bindings := good.1.2.2.2.2.1
  have hbase : t.scalars.baseMemory = caller.scalars.baseMemory := good.1.2.2.2.2.2
  have bound : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).bindRoot V (.integer s64) vsc true =
      some (⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer s64,true,.root vsc⟩]⟩,0) := by
    have vobject : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).object V (.integer s64) =
        some (vbuf,⟨.integer s64,none,some vsc,[]⟩) :=
      object_runs _ V _ vbuf _ ok.valid ok.vfound ok.vtag rfl
    have vrooted : caller.frame.state.forest.rootOwner V = some V := CppVectorOwnership.root_runs _ V _ ok.vtag rfl
    have vmax : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).maximum V = some true :=
      maximum_runs _ V V true ok.lengths vrooted ok.flag
    simp only [Frame.bindRoot,vobject,vmax,Bind.bind,Option.bind]
    simp [Frame.addBinding]
  have hp : Proofs.FloydWarshallInstance.floyd_warshall_std_vector_long_long.parameters = [.vector s64 true,.scalar i32 false true] := rfl
  rw [hp]
  simp [prepare,ok.valid,resolveAll,rvec,res]
  simp [fs,fr,fb,hmem,hbind,hbase,bound,bindAll,bindOne,CppState.bindArgument,hv,callerP,
    NState.observe,CppState.State.observe]
  left
  have g := good.2.2.2.2.1
  simp [NState.charge,NState.observe,CppState.State.observe] at g
  omega



set_option maxHeartbeats 4000000 in
theorem floyd_warshall_correct (caller : NState) {vslot vb V vsc : Nat} {vbuf : Buffer Value}
    (ok : VOKW caller vslot vb V vsc vbuf) (v0 : List Nat) (hvB : ∀ x ∈ v0, x < 4611686018427387904)
    (hitems : vbuf.items = (v0.map (fun x : Nat => (x : Int))).map Value.integer)
    (n : Nat) (hlen : v0.length = n * n) (hnn : n * n < 2147483648)
    (hbvalid : vbuf.Valid (accepts (.integer s64))) (hlimit : vbuf.limit = CppVectorBindings.sizeLimit s64)
    (howner : vbuf.owner = V) (e : NExpr) (hs : e.scalarOnly = true) (ty : e.resultType = i32)
    (value : e.denote (envOf caller) = some (n : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState) (v' : List Nat),
      prepare caller Proofs.FloydWarshallInstance.floyd_warshall_std_vector_long_long.parameters [.vectorReference vslot,.value e] = some Sinit ∧
      Proofs.FloydWarshallInstance.floyd_warshall_std_vector_long_long.callFuel fuel caller [.vectorReference vslot,.value e] =
        .finished (res,Ret.unit) ∧
      v'.length = n * n ∧
      (∀ p q, p < n → q < n → v'.getD (p * n + q) 0 = Dm (fun p q => v0.getD (p * n + q) 0) n p q) ∧
      (∀ x ∈ v', x < 4611686018427387904) ∧
      ScalarPost3 caller Sinit res e.nodes (costK n + 100) caller.scalars.memory (n * n * n) V
        (v'.map (fun x : Nat => (x : Int))) := by
  have hn32 : n < 2147483648 := by have := n_small n hnn; omega
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_fwc caller ok e (n : Int) hs ty value (validN n hn32)
  let vc : VCtx := ⟨s64,true,true,V,vsc,vbuf,v0.map (fun x : Nat => (x : Int)),hitems,fun _ => rfl,
    by simp; omega,caller.frame.state.liveSpace,caller.frame.state.storage.work,caller.scope+1,
    caller.frame.state.storage.objects.length⟩
  have fwS : FW vc (v0.map (fun x : Nat => (x : Int))) vbuf 0 Sinit.frame := by
    rw [sFrame]
    refine ⟨ok.valid,ok.lengths,rfl,rfl,?_,rfl,rfl,ok.vtag,ok.vfound,ok.flag,hitems,hbvalid,hlimit,howner,by simp; omega⟩
    intro owner k h
    have := ok.strict owner k h
    show k < caller.scope+1
    omega
  have hI : InvF (fun p q => v0.getD (p * n + q) 0) n 0 0 0 (v0.map (fun x : Nat => (x : Int))) :=
    ⟨v0, rfl, hlen, hvB, fun p q hp hq => by rw [Em_start]; rfl⟩
  obtain ⟨rr,hexec,hret,hrps,hIn,hcost,hneed,hwk⟩ :=
    body_execF (fun p q => v0.getD (p * n + q) 0) (callerP caller) n hnn _ hI (3 * n + 3) (Nat.le_refl _)
  obtain ⟨v', hv', hl', hb', hm'⟩ := hIn
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)]).take caller.scalars.memory.length =
      caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)], [⟨(callerP caller).length,true⟩]⟩ : PS) =
      gS (callerP caller) [ci n] := by
    simp [gS]
  have gw := good.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw
  have hpost := call_vecw_unit vc true (fun _ => ⟨rfl,rfl⟩) caller Proofs.FloydWarshallInstance.floyd_warshall_std_vector_long_long
    [.vectorReference vslot,.value e] Sinit
    (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)]) [⟨(callerP caller).length,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok.base (by decide) (3 * n + 3) rr
    (by rw [hmk, body_eqF]; exact hexec) hret rfl (by omega) (by simp) e.nodes (costK n + 100) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,v',hprep,hrun,hl',?_,hb',?_⟩
  · intro p q hp hq
    rw [hm' p q hp hq, Em_start]
  · have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
      rw [hrps]
      simp only [gS_mem, callerP, List.append_assoc]
      rw [List.take_append_of_le_length (by simp)]
      exact List.take_length
    rw [hs', hv'] at post
    exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk


/-- The Floyd-Warshall matrix is the matrix of shortest walk lengths over the vertices `< n`. -/
theorem Dm_shortest (W : Nat → Nat → Nat) (n i j : Nat) :
    Walk W n i j (Dm W n i j) ∧ ∀ L, Walk W n i j L → Dm W n i j ≤ L :=
  ⟨Walk_exists W n i j, fun _ h => Walk_ge W h⟩


theorem floyd_warshall_shortest (v0 v' : List Nat) (n p q : Nat) (hp : p < n) (hq : q < n)
    (h : ∀ p q, p < n → q < n → v'.getD (p * n + q) 0 = Dm (fun p q => v0.getD (p * n + q) 0) n p q) :
    Walk (fun p q => v0.getD (p * n + q) 0) n p q (v'.getD (p * n + q) 0) ∧
      ∀ L, Walk (fun p q => v0.getD (p * n + q) 0) n p q L → v'.getD (p * n + q) 0 ≤ L := by
  rw [h p q hp hq]
  exact Dm_shortest _ n p q

end Program

end Proofs.FloydWarshallCall
