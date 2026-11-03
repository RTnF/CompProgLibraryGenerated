import Proofs.MultiVecCallN
import Proofs.ForLoopBN
import Proofs.BellmanFordExec
import Proofs.Generated.CumulativeSum
import Proofs.CumulativeSum2DMath

namespace Proofs.CumulativeSum2DExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVecN Proofs.MultiKitN Proofs.ForLoopMN Proofs.ForLoopCN
open Proofs.ForLoopBN Proofs.VecStmtX
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.PrefixSumsCall (bT)
open Proofs.CumulativeSum2DMath
open Proofs.BellmanFordExec (cidx_den M31 i32_valid_nat s64_valid_of)

/-! ### `CumulativeSum2D<long long>::CumulativeSum2D(const vector<vector<long long>> &)` (nv = 2: slot 0 = `cs` (writable
nested), slot 1 = `v`).  Cells: 0 = n, 1 = m, 2 = i, 3 = run, 4 = j, 5 = x, 6 = up -/

abbrev cs64 (x : Int) : Cell := ⟨s64, x⟩
abbrev iIx (nv : Nat) : NExpr := .cast u64 (.variable i32 (nv + 2))
abbrev iIx1 (nv : Nat) : NExpr := .cast u64 (.binary i32 .add (.variable i32 (nv + 2)) (.literal i32 1))
abbrev jIx (nv : Nat) : NExpr := .cast u64 (.variable i32 (nv + 4))
abbrev jIx1 (nv : Nat) : NExpr := .cast u64 (.binary i32 .add (.variable i32 (nv + 4)) (.literal i32 1))
abbrev readX (nv : Nat) : NExpr := .read s64 (.row (.local 1) (.integer s64) (iIx nv)) (jIx nv)
abbrev readUp (nv : Nat) : NExpr := .read s64 (.row (.local 0) (.integer s64) (iIx nv)) (jIx1 nv)
abbrev writeS (nv : Nat) : NStmt :=
  .write (.row (.local 0) (.integer s64) (iIx1 nv)) s64 (jIx1 nv) (.binary s64 .add (.variable s64 (nv + 6)) (.variable s64 (nv + 3)))
abbrev bodyIn2 (nv : Nat) : Command :=
  .sequence (.primitive (.declare s64 true (readX nv)))
    (.sequence (.primitive (.assign (nv + 3) s64 (.binary s64 .add (.variable s64 (nv + 3)) (.variable s64 (nv + 5)))))
      (.sequence (.primitive (.declare s64 true (readUp nv))) (.sequence (.primitive (writeS nv)) Sk)))
abbrev innerFor2 (nv : Nat) : Command := forStmtB nv 4 1 (bodyIn2 nv)
abbrev bodyOut2 (nv : Nat) : Command :=
  .sequence (.primitive (.declare s64 true (.cast s64 (.literal i32 0)))) (.sequence (innerFor2 nv) Sk)
abbrev outerFor2 (nv : Nat) : Command := forStmtB nv 2 0 (bodyOut2 nv)
abbrev colsE2 (nv : Nat) : NExpr := .cast i32 (.size (.integer s64) (.row (.local 1) (.integer s64) (iIx nv)))
abbrev checkBody (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (colsE2 nv)))
    (.sequence (.primitive (.check (.binary bT .eq (.variable i32 (nv + 3)) (.variable i32 (nv + 1))))) Sk)
abbrev loop1 (nv : Nat) : Command := forStmtB nv 2 0 (checkBody nv)
abbrev nE : NExpr := .cast i32 (.size (.vector (.integer s64)) (.local 1))
abbrev mE : NExpr := .cast i32 (.size (.integer s64) (.row (.local 1) (.integer s64) (.cast u64 (.literal i32 0))))
abbrev prog2 (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true nE))
    (.sequence (.primitive (.check (.binary bT .gt (.variable i32 (nv + 0)) (.literal i32 0))))
      (.sequence (.primitive (.declare i32 true mE))
        (.sequence (.primitive (.check (.binary bT .gt (.variable i32 (nv + 1)) (.literal i32 0))))
          (.sequence (loop1 nv) (.sequence (outerFor2 nv) Sk)))))

theorem body_eq2 : Proofs.CumulativeSumInstance.CumulativeSum2D_long_long_new0.body = prog2 2 := rfl


theorem rowKey_eq_rk (k i : Nat) : rowKey k i = rk k i := rfl

/-- Reading `v[t][j]` (slot 1) from the cells `[n, m, t, run, j]`. -/
theorem readX_val (mv : MV) (hnv : mv.nv = 2) (hf1 : mv.flat 1 = false) (hty1 : mv.ty 1 = s64) (vv : Nat → List Int)
    (P cells : List Cell) (t j : Nat) (row : List Int) (x : Int)
    (ht : cells[2]? = some (ci t)) (hj : cells[4]? = some (ci j)) (htl : t < M31) (hjl : j < M31)
    (hwr : t < mv.wrows 1) (hrow : vv (rowKey 1 t) = row) (hx : row[j]? = some x) (hxv : s64.valid x = true) :
    vdenN mv vv (penvN mv.nv (gS P cells)) (readX mv.nv) = some x := by
  have e1 := cidx_den (penvN mv.nv (gS P cells)) (mv.nv + 2) t
    (gSM_env mv.nv P cells 2 (ci t) ht (BellmanFordExec.i32_valid_nat t htl)) htl
  have e2 := cidx_den (penvN mv.nv (gS P cells)) (mv.nv + 4) j
    (gSM_env mv.nv P cells 4 (ci j) hj (BellmanFordExec.i32_valid_nat j hjl)) hjl
  simp only [readX, vdenN]
  rw [if_pos ⟨by omega, hf1, hty1.symm, hty1.symm, rfl, rfl⟩]
  rw [iIx, jIx]
  rw [e1, Option.bind_some, e2, Option.bind_some, if_pos ⟨Int.natCast_nonneg t, by rw [Int.toNat_natCast]; exact hwr⟩,
    Int.toNat_natCast, hrow]
  unfold elemAtL
  rw [if_pos (Int.natCast_nonneg j), Int.toNat_natCast, hx, Option.bind_some, hty1, if_pos hxv]

theorem idx1_den (env : Nat → Ty → Option Int) (k j : Nat) (h : env k i32 = some (j : Int)) (hj : j + 1 < M31) :
    (NExpr.cast u64 (.binary i32 .add (.variable i32 k) (.literal i32 1))).denote env = some ((j + 1 : Nat) : Int) := by
  have hl : i32.valid 1 = true := by decide
  have hv : i32.valid ((j + 1 : Nat) : Int) = true := BellmanFordExec.i32_valid_nat (j + 1) hj
  have hsum : binaryValue .add (j : Int) 1 = ((j + 1 : Nat) : Int) := by
    show (j : Int) + 1 = _
    omega
  rw [den_cast, den_binary, den_variable, h, Option.bind_some]
  show ((Option.bind (some (1 : Int)) fun b => i32.convert (binaryValue .add (j : Int) b)).bind u64.convert) = _
  have hlt : ((j + 1 : Nat) : Int) < 18446744073709551616 := by
    have : j + 1 < 2147483648 := hj
    omega
  rw [Option.bind_some, hsum, Ty.convert_of_valid _ _ hv, Option.bind_some, convert_u64,
    Int.emod_eq_of_lt (Int.natCast_nonneg _) hlt]

/-- Reading `cs[t][j + 1]` (slot 0). -/
theorem readUp_val (mv : MV) (hnv : mv.nv = 2) (hf0 : mv.flat 0 = false) (hty0 : mv.ty 0 = s64) (vv : Nat → List Int)
    (P cells : List Cell) (t j : Nat) (row : List Int) (x : Int)
    (ht : cells[2]? = some (ci t)) (hj : cells[4]? = some (ci j)) (htl : t < M31) (hjl : j + 1 < M31)
    (hwr : t < mv.wrows 0) (hrow : vv (rowKey 0 t) = row) (hx : row[j + 1]? = some x) (hxv : s64.valid x = true) :
    vdenN mv vv (penvN mv.nv (gS P cells)) (readUp mv.nv) = some x := by
  have hjl' : j < M31 := by have : j + 1 < M31 := hjl; omega
  have e1 := cidx_den (penvN mv.nv (gS P cells)) (mv.nv + 2) t
    (gSM_env mv.nv P cells 2 (ci t) ht (BellmanFordExec.i32_valid_nat t htl)) htl
  have e2 : (jIx1 mv.nv).denote (penvN mv.nv (gS P cells)) = some ((j + 1 : Nat) : Int) :=
    idx1_den _ (mv.nv + 4) j (gSM_env mv.nv P cells 4 (ci j) hj (BellmanFordExec.i32_valid_nat j hjl')) hjl
  simp only [readUp, vdenN]
  rw [if_pos ⟨by omega, hf0, hty0.symm, hty0.symm, rfl, rfl⟩]
  rw [iIx]
  rw [e1, Option.bind_some, e2, Option.bind_some, if_pos ⟨Int.natCast_nonneg t, by rw [Int.toNat_natCast]; exact hwr⟩,
    Int.toNat_natCast, hrow]
  unfold elemAtL
  rw [if_pos (Int.natCast_nonneg (j + 1)), Int.toNat_natCast, hx, Option.bind_some, hty0, if_pos hxv]


theorem take_sum_succ (r : List Int) (j : Nat) (x : Int) (h : r[j]? = some x) :
    ((r.take (j + 1)).sum) = (r.take j).sum + x := by
  rw [List.take_succ, h]
  simp [List.sum_append]

theorem vwp_readX (nv : Nat) : vwp (readX nv) = (8, 8) := by
  simp [readX, iIx, jIx, vwp, NExpr.nodes, Container.nodes]

theorem vwp_readUp (nv : Nat) : vwp (readUp nv) = (10, 10) := by
  simp [readUp, iIx, jIx1, vwp, NExpr.nodes, Container.nodes]

theorem body_in2_exec (mv : MV) (hnv : mv.nv = 2) (hf0 : mv.flat 0 = false) (hf1 : mv.flat 1 = false)
    (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (hw0 : mv.wN 0 = true) (V : List (List Int)) (m : Nat)
    (hwr0 : mv.wrows 0 = V.length + 1) (hwr1 : mv.wrows 1 = V.length) (fu : Nat) (P : List Cell) (n t j : Nat)
    (hn : n = V.length) (htn : t < n) (hjm : j < m) (hM : m + 1 < M31) (hn' : n < M31) (r : List Int) (hr : V[t]? = some r)
    (hrl : r.length = m) (x : Int) (hx : r[j]? = some x) (hxv : s64.valid x = true)
    (hRun : s64.valid ((r.take j).sum) = true) (hRun1 : s64.valid ((r.take (j + 1)).sum) = true)
    (hup : s64.valid (P2 V t (j + 1)) = true) (hnew : s64.valid (P2 V (t + 1) (j + 1)) = true) :
    ∃ res : PRM, pexecM mv fu (bodyIn2 mv.nv) (gS P ([ci n, ci m, ci t, cs64 ((r.take j).sum)] ++ [ci j])) (VCS V m t j) = some res ∧
      res.ret = none ∧
      res.ps = gS P ([ci n, ci m, ci t, cs64 ((r.take (j + 1)).sum)] ++ [ci j] ++ [cs64 x, cs64 (P2 V t (j + 1))]) ∧
      res.vv = VCS V m t (j + 1) ∧ res.cost ≤ 60 ∧ res.need ≤ P.length + 80 ∧ res.wk ≤ 1 := by
  have htM : t < M31 := by show t < 2147483648; have : n < M31 := hn'; have : n < 2147483648 := this; omega
  have hjM : j < M31 := by show j < 2147483648; have : m + 1 < M31 := hM; have : m + 1 < 2147483648 := this; omega
  have hj1M : j + 1 < M31 := by show j + 1 < 2147483648; have : m + 1 < 2147483648 := hM; omega
  have htV : t < V.length := by omega
  have hrowV : VCS V m t j (rowKey 1 t) = r := by
    rw [rowKey_eq_rk, VCS_v V m t j t (by have : n < 2147483648 := hn'; omega), hr]; rfl
  have hrowCS : VCS V m t j (rowKey 0 t) = csRow V m t j t := by
    rw [rowKey_eq_rk, VCS_cs V m t j t (by have : n < 2147483648 := hn'; omega)]
  have hupE : (csRow V m t j t)[j + 1]? = some (P2 V t (j + 1)) := by
    unfold csRow
    rw [List.getElem?_map, List.getElem?_range (by omega)]
    simp [csCell]
  have hxe := take_sum_succ r j x hx
  have h0 : ([ci n, ci m, ci t, cs64 ((r.take j).sum)] ++ [ci j] : List Cell)[2]? = some (ci t) := rfl
  have h4 : ([ci n, ci m, ci t, cs64 ((r.take j).sum)] ++ [ci j] : List Cell)[4]? = some (ci j) := rfl
  have d1 := gSM_decl mv P ([ci n, ci m, ci t, cs64 ((r.take j).sum)] ++ [ci j]) (VCS V m t j) s64 (readX mv.nv) x x
    (readX_val mv hnv hf1 hty1 _ P _ t j r x h0 h4 htM hjM (by rw [hwr1]; omega) hrowV hx hxv) (conv_signed s64 rfl rfl x hxv)
  have q1 := (pexecM_prim mv fu _ _ _).trans d1
  have ea := gSM_env mv.nv P ([ci n, ci m, ci t, cs64 ((r.take j).sum)] ++ [ci j] ++ [cs64 x]) 3 (cs64 ((r.take j).sum)) rfl hRun
  have ex := gSM_env mv.nv P ([ci n, ci m, ci t, cs64 ((r.take j).sum)] ++ [ci j] ++ [cs64 x]) 5 (cs64 x) rfl hxv
  have hv2 : vdenN mv (VCS V m t j) (penvN mv.nv (gS P ([ci n, ci m, ci t, cs64 ((r.take j).sum)] ++ [ci j] ++ [cs64 x])))
      (.binary s64 .add (.variable s64 (mv.nv + 3)) (.variable s64 (mv.nv + 5))) = some ((r.take (j + 1)).sum) := by
    rw [vdenN_scalar _ _ _ _ rfl, den_binary, den_variable, ea, Option.bind_some, den_variable, ex, Option.bind_some]
    have hs : (r.take j).sum + x = (r.take (j + 1)).sum := hxe.symm
    simp only [binaryValue]
    rw [hs]
    exact conv_signed s64 rfl rfl _ hRun1
  have d2 := gSM_assign mv P ([ci n, ci m, ci t, cs64 ((r.take j).sum)] ++ [ci j] ++ [cs64 x]) (VCS V m t j) 3 (by simp) s64
    (.binary s64 .add (.variable s64 (mv.nv + 3)) (.variable s64 (mv.nv + 5))) ((r.take (j + 1)).sum) ((r.take (j + 1)).sum) hv2
    (cs64 ((r.take j).sum)) rfl rfl hRun (conv_signed s64 rfl rfl _ hRun1)
  have hset2 : ([ci n, ci m, ci t, cs64 ((r.take j).sum)] ++ [ci j] ++ [cs64 x]).set 3 ⟨s64, (r.take (j + 1)).sum⟩ =
      [ci n, ci m, ci t, cs64 ((r.take (j + 1)).sum), ci j, cs64 x] := rfl
  rw [hset2] at d2
  have q2 := (pexecM_prim mv fu _ _ _).trans d2
  have hupv : vdenN mv (VCS V m t j) (penvN mv.nv (gS P ([ci n, ci m, ci t, cs64 ((r.take (j + 1)).sum), ci j, cs64 x])))
      (readUp mv.nv) = some (P2 V t (j + 1)) :=
    readUp_val mv hnv hf0 hty0 _ P _ t j (csRow V m t j t) (P2 V t (j + 1)) rfl rfl htM hj1M
      (by rw [hwr0]; omega) hrowCS hupE hup
  have d3 := gSM_decl mv P [ci n, ci m, ci t, cs64 ((r.take (j + 1)).sum), ci j, cs64 x] (VCS V m t j) s64 (readUp mv.nv)
    (P2 V t (j + 1)) (P2 V t (j + 1)) hupv (conv_signed s64 rfl rfl _ hup)
  have q3 := (pexecM_prim mv fu _ _ _).trans d3
  -- the row write
  have hsum1 : P2 V t (j + 1) + (r.take (j + 1)).sum = P2 V (t + 1) (j + 1) := by
    rw [P2_succ_row V t r hr (j + 1)]
  have e6 := gSM_env mv.nv P ([ci n, ci m, ci t, cs64 ((r.take (j + 1)).sum), ci j, cs64 x] ++ [cs64 (P2 V t (j + 1))]) 6
    (cs64 (P2 V t (j + 1))) rfl hup
  have e3 := gSM_env mv.nv P ([ci n, ci m, ci t, cs64 ((r.take (j + 1)).sum), ci j, cs64 x] ++ [cs64 (P2 V t (j + 1))]) 3
    (cs64 ((r.take (j + 1)).sum)) rfl hRun1
  have e2 := gSM_env mv.nv P ([ci n, ci m, ci t, cs64 ((r.take (j + 1)).sum), ci j, cs64 x] ++ [cs64 (P2 V t (j + 1))]) 2
    (ci t) rfl (BellmanFordExec.i32_valid_nat t htM)
  have e4 := gSM_env mv.nv P ([ci n, ci m, ci t, cs64 ((r.take (j + 1)).sum), ci j, cs64 x] ++ [cs64 (P2 V t (j + 1))]) 4
    (ci j) rfl (BellmanFordExec.i32_valid_nat j hjM)
  have hvE : vdenM mv (VCS V m t j) (penvN mv.nv (gS P ([ci n, ci m, ci t, cs64 ((r.take (j + 1)).sum), ci j, cs64 x] ++
      [cs64 (P2 V t (j + 1))]))) (.binary s64 .add (.variable s64 (mv.nv + 6)) (.variable s64 (mv.nv + 3))) =
      some (P2 V (t + 1) (j + 1)) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, e6, Option.bind_some, den_variable, e3, Option.bind_some]
    simp only [binaryValue]
    rw [hsum1]
    exact conv_signed s64 rfl rfl _ hnew
  have hiE : vdenM mv (VCS V m t j) (penvN mv.nv (gS P ([ci n, ci m, ci t, cs64 ((r.take (j + 1)).sum), ci j, cs64 x] ++
      [cs64 (P2 V t (j + 1))]))) (iIx1 mv.nv) = some ((t + 1 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    exact idx1_den _ (mv.nv + 2) t e2 (by have : n < M31 := hn'; show t + 1 < 2147483648; have : n < 2147483648 := this; omega)
  have hjE : vdenM mv (VCS V m t j) (penvN mv.nv (gS P ([ci n, ci m, ci t, cs64 ((r.take (j + 1)).sum), ci j, cs64 x] ++
      [cs64 (P2 V t (j + 1))]))) (jIx1 mv.nv) = some ((j + 1 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    exact idx1_den _ (mv.nv + 4) j e4 hj1M
  have hlenRow : (VCS V m t j (rowKey 0 (t + 1))).length = m + 1 := by
    rw [rowKey_eq_rk, VCS_cs V m t j (t + 1) (by have : n < 2147483648 := hn'; omega)]
    exact csRow_length V m t j (t + 1)
  have w := pstmtM_writeRow_ok mv (gS P ([ci n, ci m, ci t, cs64 ((r.take (j + 1)).sum), ci j, cs64 x] ++
      [cs64 (P2 V t (j + 1))])) (VCS V m t j) 0 (by omega) hf0 hw0 (iIx1 mv.nv) (jIx1 mv.nv)
      (.binary s64 .add (.variable s64 (mv.nv + 6)) (.variable s64 (mv.nv + 3))) (P2 V (t + 1) (j + 1)) (t + 1) (j + 1)
      rfl rfl rfl hvE hiE hjE (by rw [hwr0]; omega) (by rw [hlenRow]; omega) (by rw [hty0]; exact hnew)
  rw [hty0] at w
  have q4 := (pexecM_prim mv fu _ _ _).trans w
  have hvv : upd (VCS V m t j) (rowKey 0 (t + 1)) (((VCS V m t j) (rowKey 0 (t + 1))).set (j + 1) (P2 V (t + 1) (j + 1))) =
      VCS V m t (j + 1) := by
    have := VCS_step V m t j hjm (by have : n < 2147483648 := hn'; omega)
    rw [← this]
    funext key
    unfold upd
    by_cases hk : key = rowKey 0 (t + 1)
    · subst hk; simp [rowKey_eq_rk]
    · have hk' : key ≠ rk 0 (t + 1) := hk
      simp [hk, hk']
  rw [hvv] at q4
  have q5 := seqM_some q4 rfl (pexecM_skip mv fu _ _)
  have q6 := seqM_some q3 rfl q5
  have q7 := seqM_some q2 rfl q6
  have q8 := seqM_some q1 rfl q7
  refine ⟨_, q8, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp_readX, vwp_readUp, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [vwp_readX, vwp_readUp, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
  · simp


theorem inner2_exec (mv : MV) (hnv : mv.nv = 2) (hf0 : mv.flat 0 = false) (hf1 : mv.flat 1 = false)
    (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (hw0 : mv.wN 0 = true) (V : List (List Int)) (m : Nat)
    (hwr0 : mv.wrows 0 = V.length + 1) (hwr1 : mv.wrows 1 = V.length) (fu : Nat) (P : List Cell) (n t : Nat)
    (hn : n = V.length) (htn : t < n) (hM : m + 1 < M31) (hn' : n < M31) (r : List Int) (hr : V[t]? = some r)
    (hrl : r.length = m) (hvalid : ∀ x ∈ r, s64.valid x = true)
    (hRun : ∀ j, j ≤ m → s64.valid ((r.take j).sum) = true)
    (hP : ∀ a b, a ≤ n → b ≤ m → s64.valid (P2 V a b) = true) (hfu : m + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (innerFor2 mv.nv) (gS P [ci n, ci m, ci t, cs64 0]) (VCS V m t 0) = some res ∧
      res.ret = none ∧ res.ps = gS P [ci n, ci m, ci t, cs64 r.sum] ∧ res.vv = VCS V m t m ∧
      res.cost ≤ 80 * m + 30 ∧ res.need ≤ P.length + 80 ∧ res.wk ≤ m := by
  have hm : m < 2147483647 := by have : m + 1 < M31 := hM; have : m + 1 < 2147483648 := this; omega
  obtain ⟨res, C2, hr', hps, hC2, hI, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 4 1 m (by omega) hm (bodyIn2 mv.nv)
    (fun j vv' C => vv' = VCS V m t j ∧ C = [ci n, ci m, ci t, cs64 ((r.take j).sum)]) 60 80 1 0 (by omega)
    (by
      intro j vv' C fu' hj hCl hC1 hIv hfu'
      obtain ⟨hvvE, hCe⟩ := hIv
      subst hCe
      subst hvvE
      have hjr : j < r.length := by omega
      obtain ⟨x, hx⟩ : ∃ x, r[j]? = some x := ⟨r[j], by simp [hjr]⟩
      have hxv : s64.valid x = true := hvalid x (List.mem_of_getElem? hx)
      obtain ⟨res2, hres2, hret2, hps2, hvv2, hc2, hn2, hw2⟩ := body_in2_exec mv hnv hf0 hf1 hty0 hty1 hw0 V m hwr0 hwr1 fu' P n t j
        hn htn hj hM hn' r hr hrl x hx hxv (hRun j (by omega)) (hRun (j + 1) (by omega))
        (hP t (j + 1) (by omega) (by omega)) (hP (t + 1) (j + 1) (by omega) (by omega))
      exact ⟨res2, [cs64 x, cs64 (P2 V t (j + 1))], [ci n, ci m, ci t, cs64 ((r.take (j + 1)).sum)], hres2, hret2, hps2, rfl, rfl,
        ⟨hvv2, rfl⟩, hc2, hn2, hw2⟩)
    (VCS V m t 0) [ci n, ci m, ci t, cs64 0] rfl rfl ⟨rfl, by simp⟩ fu (by omega)
  obtain ⟨hvv, hCe⟩ := hI
  have hfull : r.take m = r := by rw [← hrl]; exact List.take_length
  rw [hfull] at hCe
  subst hCe
  refine ⟨res, hr', hret, hps, hvv, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega


theorem zero_val2 (mv : MV) (vv : Nat → List Int) (ps : PS) :
    vdenN mv vv (penvN mv.nv ps) (.cast s64 (.literal i32 0)) = some 0 := by
  rw [vdenN_scalar _ _ _ _ rfl]
  have a : i32.valid 0 = true := by simp [Ty.valid]
  have b : s64.valid 0 = true := by simp [Ty.valid]
  simp [NExpr.denote, a, Ty.convert_of_valid _ _ b]

theorem vwp_zero2 : vwp (.cast s64 (.literal i32 0)) = (2, 2) := by simp [vwp, NExpr.nodes, NExpr.scalarOnly]

theorem body_out2_exec (mv : MV) (hnv : mv.nv = 2) (hf0 : mv.flat 0 = false) (hf1 : mv.flat 1 = false)
    (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (hw0 : mv.wN 0 = true) (V : List (List Int)) (m : Nat)
    (hwr0 : mv.wrows 0 = V.length + 1) (hwr1 : mv.wrows 1 = V.length) (fu : Nat) (P : List Cell) (n t : Nat)
    (hn : n = V.length) (htn : t < n) (hM : m + 1 < M31) (hn' : n < M31) (r : List Int) (hr : V[t]? = some r)
    (hrl : r.length = m) (hvalid : ∀ x ∈ r, s64.valid x = true)
    (hRun : ∀ j, j ≤ m → s64.valid ((r.take j).sum) = true)
    (hP : ∀ a b, a ≤ n → b ≤ m → s64.valid (P2 V a b) = true) (hfu : m + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (bodyOut2 mv.nv) (gS P ([ci n, ci m] ++ [ci t])) (VCS V m t 0) = some res ∧
      res.ret = none ∧ res.ps = gS P ([ci n, ci m] ++ [ci t] ++ [cs64 r.sum]) ∧ res.vv = VCS V m (t + 1) 0 ∧
      res.cost ≤ 80 * m + 40 ∧ res.need ≤ P.length + 80 ∧ res.wk ≤ m := by
  have d1 := gSM_decl mv P ([ci n, ci m] ++ [ci t]) (VCS V m t 0) s64 (.cast s64 (.literal i32 0)) 0 0 (zero_val2 mv _ _)
    (conv_signed s64 rfl rfl 0 (by simp [Ty.valid]))
  have q1 := (pexecM_prim mv fu _ _ _).trans d1
  obtain ⟨r2, hr2, hret2, hps2, hvv2, hc2, hn2, hw2⟩ := inner2_exec mv hnv hf0 hf1 hty0 hty1 hw0 V m hwr0 hwr1 fu P n t hn htn hM hn' r hr
    hrl hvalid hRun hP hfu
  have hq : ([ci n, ci m] ++ [ci t] ++ [(⟨s64, 0⟩ : Cell)]) = [ci n, ci m, ci t, cs64 0] := rfl
  rw [hq] at q1
  have q2 := seqM_some hr2 hret2 (pexecM_skip mv fu _ _)
  rw [hps2, hvv2] at q2
  have q3 := seqM_some q1 rfl q2
  have hnext : VCS V m t m = VCS V m (t + 1) 0 := by
    funext key
    unfold VCS
    by_cases h1 : key / 4294967296 = 1
    · simp only [h1, if_true]; exact csRow_next V m t _
    · simp [h1]
  rw [hnext] at q3
  refine ⟨_, q3, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp_zero2]; omega
  · simp [vwp_zero2, gS_mem_len, gS_bs_len]; omega
  · simp; omega


theorem outer2_exec (mv : MV) (hnv : mv.nv = 2) (hf0 : mv.flat 0 = false) (hf1 : mv.flat 1 = false)
    (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (hw0 : mv.wN 0 = true) (V : List (List Int)) (m : Nat)
    (hwr0 : mv.wrows 0 = V.length + 1) (hwr1 : mv.wrows 1 = V.length) (fu : Nat) (P : List Cell) (n : Nat)
    (hn : n = V.length) (hM : m + 1 < M31) (hn' : n + 1 < M31) (hrect : ∀ r ∈ V, r.length = m)
    (hvalid : ∀ r ∈ V, ∀ x ∈ r, s64.valid x = true)
    (hRun : ∀ (t j : Nat) (r : List Int), V[t]? = some r → j ≤ m → s64.valid ((r.take j).sum) = true)
    (hP : ∀ a b, a ≤ n → b ≤ m → s64.valid (P2 V a b) = true) (hfu : m + 1 + n + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (outerFor2 mv.nv) (gS P [ci n, ci m]) (VCS V m 0 0) = some res ∧
      res.ret = none ∧ res.ps = gS P [ci n, ci m] ∧ res.vv = VCS V m n 0 ∧
      res.cost ≤ (80 * m + 60) * n + 30 ∧ res.need ≤ P.length + 80 ∧ res.wk ≤ m * n := by
  have hnn : n < 2147483647 := by have : n + 1 < M31 := hn'; have : n + 1 < 2147483648 := this; omega
  obtain ⟨res, C2, hr', hps, hC2, hI, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 2 0 n (by omega) hnn (bodyOut2 mv.nv)
    (fun t vv' C => vv' = VCS V m t 0 ∧ C = [ci n, ci m]) (80 * m + 40) 80 m (m + 1) (by omega)
    (by
      intro t vv' C fu' ht hCl hC1 hIv hfu'
      obtain ⟨hvvE, hCe⟩ := hIv
      subst hCe
      subst hvvE
      have htV : t < V.length := by omega
      obtain ⟨r, hr⟩ : ∃ r, V[t]? = some r := ⟨V[t], by simp [htV]⟩
      have hrm : r ∈ V := List.mem_of_getElem? hr
      obtain ⟨res2, hres2, hret2, hps2, hvv2, hc2, hn2, hw2⟩ := body_out2_exec mv hnv hf0 hf1 hty0 hty1 hw0 V m hwr0 hwr1 fu' P n t
        hn ht hM (by have : n + 1 < M31 := hn'; have : n + 1 < 2147483648 := this; show n < 2147483648; omega) r hr (hrect r hrm) (hvalid r hrm) (fun j hj => hRun t j r hr hj) hP (by omega)
      exact ⟨res2, [cs64 r.sum], [ci n, ci m], hres2, hret2, hps2, rfl, rfl, ⟨hvv2, rfl⟩, hc2, hn2, hw2⟩)
    (VCS V m 0 0) [ci n, ci m] rfl rfl ⟨rfl, rfl⟩ fu (by omega)
  obtain ⟨hvv, hCe⟩ := hI
  subst hCe
  refine ⟨res, hr', hret, hps, hvv, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega


theorem cols2_val (mv : MV) (hnv : mv.nv = 2) (hf1 : mv.flat 1 = false) (hty1 : mv.ty 1 = s64) (vv : Nat → List Int)
    (P cells : List Cell) (t : Nat) (r : List Int) (ht : cells[2]? = some (ci t)) (htl : t < M31)
    (hwr : t < mv.wrows 1) (hr : vv (rowKey 1 t) = r) (hl : r.length < 2147483648) :
    vdenN mv vv (penvN mv.nv (gS P cells)) (colsE2 mv.nv) = some (r.length : Int) := by
  have e1 := cidx_den (penvN mv.nv (gS P cells)) (mv.nv + 2) t
    (gSM_env mv.nv P cells 2 (ci t) ht (BellmanFordExec.i32_valid_nat t htl)) htl
  have hsz : vdenN mv vv (penvN mv.nv (gS P cells)) (.size (.integer s64) (.row (.local 1) (.integer s64) (iIx mv.nv))) =
      some (r.length : Int) := by
    simp only [vdenN]
    rw [if_pos ⟨by omega, hf1, hty1.symm, hty1.symm, rfl⟩]
    rw [iIx, e1, Option.bind_some, if_pos ⟨Int.natCast_nonneg t, by rw [Int.toNat_natCast]; exact hwr⟩, Int.toNat_natCast, hr]
  have hc := conv_signed i32 rfl rfl (r.length : Int) (validN _ hl)
  have hcast : vdenN mv vv (penvN mv.nv (gS P cells)) (colsE2 mv.nv) =
      (vdenN mv vv (penvN mv.nv (gS P cells)) (.size (.integer s64) (.row (.local 1) (.integer s64) (iIx mv.nv)))).bind
        i32.convert := by
    simp only [colsE2]; rw [vdenN]
  rw [hcast, hsz, Option.bind_some]
  exact hc

theorem eq_conv (x y : Int) : bT.convert (binaryValue .eq x y) = some (if x = y then 1 else 0) := by
  by_cases h : x = y
  · subst h; simp [binaryValue, Ty.convert, bT, Ty.valid]
  · have : (x == y) = false := by simp [h]
    simp [binaryValue, this, h, Ty.convert, bT, Ty.valid]

theorem gt_conv (x y : Int) : bT.convert (binaryValue .gt x y) = some (if x > y then 1 else 0) := by
  by_cases h : x > y
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]

theorem vwp_colsE2 (nv : Nat) : vwp (colsE2 nv) = (7, 7) := by
  simp [colsE2, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, iIx]


theorem loop1_exec (mv : MV) (hnv : mv.nv = 2) (hf1 : mv.flat 1 = false) (hty1 : mv.ty 1 = s64) (V : List (List Int))
    (m : Nat) (hwr1 : mv.wrows 1 = V.length) (fu : Nat) (P : List Cell) (n : Nat) (hn : n = V.length)
    (hM : m < 2147483647) (hn' : n < 2147483647) (hrect : ∀ r ∈ V, r.length = m) (vv0 : Nat → List Int)
    (hvv0 : ∀ t r, V[t]? = some r → vv0 (rowKey 1 t) = r) (hfu : n + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (loop1 mv.nv) (gS P [ci n, ci m]) vv0 = some res ∧ res.ret = none ∧
      res.ps = gS P [ci n, ci m] ∧ res.vv = vv0 ∧ res.cost ≤ 40 * n + 30 ∧ res.need ≤ P.length + 80 ∧ res.wk = 0 := by
  obtain ⟨res, C2, hr', hps, hC2, hI, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 2 0 n (by omega) hn' (checkBody mv.nv)
    (fun t vv' C => vv' = vv0 ∧ C = [ci n, ci m]) 20 80 0 0 (by omega)
    (by
      intro t vv' C fu' ht hCl hC1 hIv hfu'
      obtain ⟨hvvE, hCe⟩ := hIv
      subst hCe
      subst hvvE
      have htV : t < V.length := by omega
      obtain ⟨r, hr⟩ : ∃ r, V[t]? = some r := ⟨V[t], by simp [htV]⟩
      have hrm : r ∈ V := List.mem_of_getElem? hr
      have hrl := hrect r hrm
      have htM : t < M31 := by show t < 2147483648; omega
      have hv := cols2_val mv hnv hf1 hty1 vv' P ([ci n, ci m] ++ [ci t]) t r rfl htM (by rw [hwr1]; exact htV) (hvv0 t r hr)
        (by omega)
      have d1 := gSM_decl mv P ([ci n, ci m] ++ [ci t]) vv' i32 (colsE2 mv.nv) (r.length : Int) (r.length : Int) hv
        (conv_signed i32 rfl rfl _ (validN _ (by omega)))
      have q1 := (pexecM_prim mv fu' _ _ _).trans d1
      have e3 := gSM_env mv.nv P ([ci n, ci m] ++ [ci t] ++ [(⟨i32, (r.length : Int)⟩ : Cell)]) 3 (ci r.length) rfl
        (BellmanFordExec.i32_valid_nat _ (by show r.length < 2147483648; omega))
      have e1 := gSM_env mv.nv P ([ci n, ci m] ++ [ci t] ++ [(⟨i32, (r.length : Int)⟩ : Cell)]) 1 (ci m) rfl
        (BellmanFordExec.i32_valid_nat _ (by show m < 2147483648; omega))
      have hck : vdenM mv vv' (penvN mv.nv (gS P ([ci n, ci m] ++ [ci t] ++ [(⟨i32, (r.length : Int)⟩ : Cell)])))
          (.binary bT .eq (.variable i32 (mv.nv + 3)) (.variable i32 (mv.nv + 1))) = some 1 := by
        rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, e3, Option.bind_some, den_variable, e1, Option.bind_some,
          eq_conv, hrl]
        simp
      have c1 := pstmtM_check_ok mv (gS P ([ci n, ci m] ++ [ci t] ++ [(⟨i32, (r.length : Int)⟩ : Cell)])) vv' _ _ hck (by decide)
      have q2 := seqM_some ((pexecM_prim mv fu' _ _ _).trans c1) rfl (pexecM_skip mv fu' _ vv')
      have q3 := seqM_some q1 rfl q2
      refine ⟨_, [ci r.length], [ci n, ci m], q3, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
      · simp [vwp_colsE2, vwp, NExpr.nodes, NExpr.scalarOnly]
      · simp [vwp_colsE2, vwp, NExpr.nodes, NExpr.scalarOnly, gS_mem_len, gS_bs_len, Container.nodes, iIx]
      · simp)
    vv0 [ci n, ci m] rfl rfl ⟨rfl, rfl⟩ fu (by omega)
  obtain ⟨hvv, hCe⟩ := hI
  subst hCe
  refine ⟨res, hr', hret, hps, hvv, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega


theorem nE_val (mv : MV) (hnv : mv.nv = 2) (hf1 : mv.flat 1 = false) (hty1 : mv.ty 1 = s64) (V : List (List Int))
    (hwr1 : mv.wrows 1 = V.length) (vv : Nat → List Int) (ps : PS) (hn : V.length < 2147483648) :
    vdenN mv vv (penvN mv.nv ps) nE = some (V.length : Int) := by
  have hsz : vdenN mv vv (penvN mv.nv ps) (.size (.vector (.integer s64)) (.local 1)) = some (V.length : Int) := by
    simp only [vdenN]
    rw [if_pos ⟨by omega, hf1, hty1.symm⟩, hwr1]
  have hcast : vdenN mv vv (penvN mv.nv ps) nE =
      (vdenN mv vv (penvN mv.nv ps) (.size (.vector (.integer s64)) (.local 1))).bind i32.convert := by
    simp only [nE]; rw [vdenN]
  rw [hcast, hsz, Option.bind_some]
  exact conv_signed i32 rfl rfl _ (validN _ hn)

theorem mE_val (mv : MV) (hnv : mv.nv = 2) (hf1 : mv.flat 1 = false) (hty1 : mv.ty 1 = s64) (V : List (List Int))
    (hwr1 : mv.wrows 1 = V.length) (vv : Nat → List Int) (ps : PS) (r0 : List Int) (hV0 : V[0]? = some r0)
    (hrow : vv (rowKey 1 0) = r0) (hl : r0.length < 2147483648) (hpos : 0 < V.length) :
    vdenN mv vv (penvN mv.nv ps) mE = some (r0.length : Int) := by
  have hz : (NExpr.cast u64 (.literal i32 0)).denote (penvN mv.nv ps) = some ((0 : Nat) : Int) := by
    have a : i32.valid 0 = true := by simp [Ty.valid]
    have b : u64.valid 0 = true := by simp [Ty.valid]
    simp [NExpr.denote, a, Ty.convert_of_valid _ _ b]
  have hsz : vdenN mv vv (penvN mv.nv ps) (.size (.integer s64) (.row (.local 1) (.integer s64) (.cast u64 (.literal i32 0)))) =
      some (r0.length : Int) := by
    simp only [vdenN]
    rw [if_pos ⟨by omega, hf1, hty1.symm, hty1.symm, rfl⟩, hz, Option.bind_some,
      if_pos ⟨Int.natCast_nonneg 0, by rw [Int.toNat_natCast, hwr1]; exact hpos⟩, Int.toNat_natCast, hrow]
  have hcast : vdenN mv vv (penvN mv.nv ps) mE =
      (vdenN mv vv (penvN mv.nv ps) (.size (.integer s64) (.row (.local 1) (.integer s64) (.cast u64 (.literal i32 0))))).bind
        i32.convert := by
    simp only [mE]; rw [vdenN]
  rw [hcast, hsz, Option.bind_some]
  exact conv_signed i32 rfl rfl _ (validN _ hl)


theorem vwp_nE : vwp nE = (4, 4) := by simp [nE, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
theorem vwp_mE : vwp mE = (7, 7) := by simp [mE, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]

theorem ctor_exec (mv : MV) (hnv : mv.nv = 2) (hf0 : mv.flat 0 = false) (hf1 : mv.flat 1 = false)
    (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (hw0 : mv.wN 0 = true) (V : List (List Int)) (m : Nat)
    (hwr0 : mv.wrows 0 = V.length + 1) (hwr1 : mv.wrows 1 = V.length) (fu : Nat) (P : List Cell)
    (hpos : 0 < V.length) (hm : 0 < m) (hM : m + 1 < M31) (hn' : V.length + 1 < M31) (hrect : ∀ r ∈ V, r.length = m)
    (hvalid : ∀ r ∈ V, ∀ x ∈ r, s64.valid x = true)
    (hRun : ∀ (t j : Nat) (r : List Int), V[t]? = some r → j ≤ m → s64.valid ((r.take j).sum) = true)
    (hP : ∀ a b, a ≤ V.length → b ≤ m → s64.valid (P2 V a b) = true) (hfu : m + 1 + V.length + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (prog2 mv.nv) (gS P []) (VCS V m 0 0) = some res ∧ res.ret = none ∧
      res.ps = gS P [ci V.length, ci m] ∧ res.vv = VCS V m V.length 0 ∧
      res.cost ≤ (80 * m + 100) * V.length + 100 ∧ res.need ≤ P.length + 80 ∧ res.wk ≤ m * V.length := by
  have hnl : V.length < 2147483648 := by have : V.length + 1 < M31 := hn'; have : V.length + 1 < 2147483648 := this; omega
  have hM' : m + 1 < 2147483648 := hM
  have hn'' : V.length + 1 < 2147483648 := hn'
  obtain ⟨r0, hV0⟩ : ∃ r0, V[0]? = some r0 := ⟨V[0], by simp [hpos]⟩
  have hr0 : r0 ∈ V := List.mem_of_getElem? hV0
  have hr0l := hrect r0 hr0
  have hrow0 : VCS V m 0 0 (rowKey 1 0) = r0 := by
    rw [rowKey_eq_rk, VCS_v V m 0 0 0 (by omega), hV0]; rfl
  -- declare n
  have d1 := gSM_decl mv P [] (VCS V m 0 0) i32 nE (V.length : Int) (V.length : Int) (nE_val mv hnv hf1 hty1 V hwr1 _ _ hnl)
    (conv_signed i32 rfl rfl _ (validN _ hnl))
  have q1 := (pexecM_prim mv fu _ _ _).trans d1
  have hq1 : ([] ++ [(⟨i32, (V.length : Int)⟩ : Cell)]) = [ci V.length] := rfl
  rw [hq1] at q1
  -- check n > 0
  have en := gSM_env mv.nv P [ci V.length] 0 (ci V.length) rfl (BellmanFordExec.i32_valid_nat _ hnl)
  have hc1 : vdenM mv (VCS V m 0 0) (penvN mv.nv (gS P [ci V.length]))
      (.binary bT .gt (.variable i32 (mv.nv + 0)) (.literal i32 0)) = some 1 := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, en, Option.bind_some]
    have hl : i32.valid 0 = true := by simp [Ty.valid]
    simp only [NExpr.denote, hl, ite_true, Option.bind_some, gt_conv]
    simp [hpos]
  have c1 := pstmtM_check_ok mv (gS P [ci V.length]) (VCS V m 0 0) _ _ hc1 (by decide)
  have q2 := (pexecM_prim mv fu _ _ _).trans c1
  -- declare m
  have d3 := gSM_decl mv P [ci V.length] (VCS V m 0 0) i32 mE (r0.length : Int) (r0.length : Int)
    (mE_val mv hnv hf1 hty1 V hwr1 _ _ r0 hV0 hrow0 (by omega) hpos) (conv_signed i32 rfl rfl _ (validN _ (by omega)))
  have q3 := (pexecM_prim mv fu _ _ _).trans d3
  rw [hr0l] at q3
  have hq3 : ([ci V.length] ++ [(⟨i32, (m : Int)⟩ : Cell)]) = [ci V.length, ci m] := rfl
  rw [hq3] at q3
  -- check m > 0
  have em := gSM_env mv.nv P [ci V.length, ci m] 1 (ci m) rfl (BellmanFordExec.i32_valid_nat _ (by omega))
  have hc2 : vdenM mv (VCS V m 0 0) (penvN mv.nv (gS P [ci V.length, ci m]))
      (.binary bT .gt (.variable i32 (mv.nv + 1)) (.literal i32 0)) = some 1 := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, em, Option.bind_some]
    have hl : i32.valid 0 = true := by simp [Ty.valid]
    simp only [NExpr.denote, hl, ite_true, Option.bind_some, gt_conv]
    simp [hm]
  have c2 := pstmtM_check_ok mv (gS P [ci V.length, ci m]) (VCS V m 0 0) _ _ hc2 (by decide)
  have q4 := (pexecM_prim mv fu _ _ _).trans c2
  obtain ⟨l1, hl1, hret1, hps1, hvv1, hc1', hn1, hw1⟩ := loop1_exec mv hnv hf1 hty1 V m hwr1 fu P V.length rfl (by omega)
    (by omega) hrect (VCS V m 0 0)
    (fun t r hr => by
      have htl : t < V.length := (List.getElem?_eq_some_iff.mp hr).1
      rw [rowKey_eq_rk, VCS_v V m 0 0 t (by omega), hr]; rfl) (by omega)
  obtain ⟨o2, ho2, hreto, hpso, hvvo, hco, hno, hwo⟩ := outer2_exec mv hnv hf0 hf1 hty0 hty1 hw0 V m hwr0 hwr1 fu P V.length rfl hM hn'
    hrect hvalid hRun hP (by omega)
  have s6 := seqM_some ho2 hreto (pexecM_skip mv fu _ _)
  have s5 := seqM_some hl1 hret1 (by rw [hps1, hvv1]; exact s6)
  have s4 := seqM_some q4 rfl s5
  have s3 := seqM_some q3 rfl s4
  have s2 := seqM_some q2 rfl s3
  have s1 := seqM_some q1 rfl s2
  refine ⟨_, s1, rfl, hpso, hvvo, ?_, ?_, ?_⟩
  · simp [vwp_nE, vwp_mE, vwp, NExpr.nodes, NExpr.scalarOnly]
    simp only [Nat.add_mul, Nat.mul_assoc] at hco ⊢
    omega
  · simp [vwp_nE, vwp_mE, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len, hpso]
    exact ⟨hn1, hno⟩
  · simp [hwo]
    omega

/-! ### `CumulativeSum2D<long long>::sum(a, b)` (nv = 1: slot 0 = `cs`).  Cells: 0 = a, 1 = b, 2 = n, 3 = m, 4 = x -/

theorem le_conv (x y : Int) : bT.convert (binaryValue .le x y) = some (if x ≤ y then 1 else 0) := by
  by_cases h : x ≤ y
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]

theorem lt_conv (x y : Int) : bT.convert (binaryValue .lt x y) = some (if x < y then 1 else 0) := by
  by_cases h : x < y
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]

abbrev nS : NExpr := .cast i32 (.size (.vector (.integer s64)) (.local 0))
abbrev aIx : NExpr := .cast u64 (.variable i32 1)
abbrev bIx : NExpr := .cast u64 (.variable i32 2)
abbrev mS : NExpr := .cast i32 (.size (.integer s64) (.row (.local 0) (.integer s64) aIx))
abbrev xS : NExpr := .read s64 (.row (.local 0) (.integer s64) aIx) bIx
abbrev sprog2 : Command :=
  .sequence (.primitive (.check (.binary bT .le (.literal i32 0) (.variable i32 1))))
    (.sequence (.primitive (.declare i32 true nS))
      (.sequence (.primitive (.check (.binary bT .lt (.variable i32 1) (.variable i32 3))))
        (.sequence (.primitive (.check (.binary bT .le (.literal i32 0) (.variable i32 2))))
          (.sequence (.primitive (.declare i32 true mS))
            (.sequence (.primitive (.check (.binary bT .lt (.variable i32 2) (.variable i32 4))))
              (.sequence (.primitive (.declare s64 true xS))
                (.sequence (.primitive (.ret (.variable s64 5))) Sk)))))))

theorem body_eq_s2 : Proofs.CumulativeSumInstance.CumulativeSum2D_long_long_sum_2.body = sprog2 := rfl

theorem env_nat (mv : MV) (P cells : List Cell) (k x a : Nat) (hx : x = mv.nv + k) (hk : cells[k]? = some (ci a))
    (ha : a < M31) : penvN mv.nv (gS P cells) x i32 = some (a : Int) := by
  subst hx
  exact gSM_env mv.nv P cells k (ci a) hk (BellmanFordExec.i32_valid_nat a ha)

theorem chk_le0 (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (x a : Nat) (h : env x i32 = some (a : Int)) :
    vdenM mv vv env (.binary bT .le (.literal i32 0) (.variable i32 x)) = some 1 := by
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, h]
  have hl : i32.valid 0 = true := by simp [Ty.valid]
  simp only [NExpr.denote, hl, ite_true, Option.bind_some, le_conv]
  simp

theorem chk_lt (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (x y a c : Nat) (h : env x i32 = some (a : Int))
    (h' : env y i32 = some (c : Int)) (hac : a < c) :
    vdenM mv vv env (.binary bT .lt (.variable i32 x) (.variable i32 y)) = some 1 := by
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, den_variable, h, h', Option.bind_some, Option.bind_some, lt_conv]
  simp [hac]

theorem aIx_den (env : Nat → Ty → Option Int) (x a : Nat) (h : env x i32 = some (a : Int)) (ha : a < M31) :
    (NExpr.cast u64 (.variable i32 x)).denote env = some (a : Int) := cidx_den env x a h ha

theorem nS_val (mv : MV) (hnv : mv.nv = 1) (hf0 : mv.flat 0 = false) (hty0 : mv.ty 0 = s64) (n : Nat)
    (hwr0 : mv.wrows 0 = n + 1) (vv : Nat → List Int) (ps : PS) (hn : n + 1 < 2147483648) :
    vdenN mv vv (penvN mv.nv ps) nS = some ((n + 1 : Nat) : Int) := by
  have hsz : vdenN mv vv (penvN mv.nv ps) (.size (.vector (.integer s64)) (.local 0)) = some ((n + 1 : Nat) : Int) := by
    simp only [vdenN]
    rw [if_pos ⟨by omega, hf0, hty0.symm⟩, hwr0]
  have hcast : vdenN mv vv (penvN mv.nv ps) nS =
      (vdenN mv vv (penvN mv.nv ps) (.size (.vector (.integer s64)) (.local 0))).bind i32.convert := by
    simp only [nS]; rw [vdenN]
  rw [hcast, hsz, Option.bind_some]
  exact conv_signed i32 rfl rfl _ (validN _ hn)

theorem mS_val (mv : MV) (hnv : mv.nv = 1) (hf0 : mv.flat 0 = false) (hty0 : mv.ty 0 = s64) (n : Nat)
    (hwr0 : mv.wrows 0 = n + 1) (vv : Nat → List Int) (ps : PS) (a : Nat) (row : List Int)
    (ha : (aIx).denote (penvN mv.nv ps) = some (a : Int)) (han : a < n + 1) (hrow : vv (rowKey 0 a) = row)
    (hl : row.length < 2147483648) :
    vdenN mv vv (penvN mv.nv ps) mS = some (row.length : Int) := by
  have hsz : vdenN mv vv (penvN mv.nv ps) (.size (.integer s64) (.row (.local 0) (.integer s64) aIx)) =
      some (row.length : Int) := by
    simp only [vdenN]
    rw [if_pos ⟨by omega, hf0, hty0.symm, hty0.symm, rfl⟩, ha, Option.bind_some,
      if_pos ⟨Int.natCast_nonneg a, by rw [Int.toNat_natCast, hwr0]; exact han⟩, Int.toNat_natCast, hrow]
  have hcast : vdenN mv vv (penvN mv.nv ps) mS =
      (vdenN mv vv (penvN mv.nv ps) (.size (.integer s64) (.row (.local 0) (.integer s64) aIx))).bind i32.convert := by
    simp only [mS]; rw [vdenN]
  rw [hcast, hsz, Option.bind_some]
  exact conv_signed i32 rfl rfl _ (validN _ hl)

theorem xS_val (mv : MV) (hnv : mv.nv = 1) (hf0 : mv.flat 0 = false) (hty0 : mv.ty 0 = s64) (n : Nat)
    (hwr0 : mv.wrows 0 = n + 1) (vv : Nat → List Int) (ps : PS) (a b : Nat) (row : List Int) (x : Int)
    (ha : (aIx).denote (penvN mv.nv ps) = some (a : Int)) (hb : (bIx).denote (penvN mv.nv ps) = some (b : Int))
    (han : a < n + 1) (hrow : vv (rowKey 0 a) = row) (hx : row[b]? = some x) (hxv : s64.valid x = true) :
    vdenN mv vv (penvN mv.nv ps) xS = some x := by
  simp only [xS, vdenN]
  rw [if_pos ⟨by omega, hf0, hty0.symm, hty0.symm, rfl, rfl⟩]
  rw [ha, Option.bind_some, hb, Option.bind_some, if_pos ⟨Int.natCast_nonneg a, by rw [Int.toNat_natCast, hwr0]; exact han⟩,
    Int.toNat_natCast, hrow]
  unfold elemAtL
  rw [if_pos (Int.natCast_nonneg b), Int.toNat_natCast, hx, Option.bind_some, hty0, if_pos hxv]

theorem vwp_nS : vwp nS = (4, 4) := by simp [nS, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
theorem vwp_mS : vwp mS = (7, 7) := by simp [mS, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
theorem vwp_xS : vwp xS = (8, 8) := by simp [xS, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]

theorem sum2_exec (mv : MV) (hnv : mv.nv = 1) (hf0 : mv.flat 0 = false) (hty0 : mv.ty 0 = s64) (V : List (List Int)) (m : Nat)
    (hwr0 : mv.wrows 0 = V.length + 1) (fu : Nat) (P : List Cell) (a b : Nat) (ha : a ≤ V.length) (hb : b ≤ m)
    (hn' : V.length + 1 < M31) (hM : m + 1 < M31) (hv : s64.valid (P2 V a b) = true) :
    ∃ res : PRM, pexecM mv fu sprog2 (gS P [ci a, ci b]) (VCS V m V.length 0) = some res ∧
      res.ret = some (P2 V a b) ∧ res.vv = VCS V m V.length 0 ∧
      res.ps = gS P [ci a, ci b, ci (V.length + 1), ci (m + 1), cs64 (P2 V a b)] ∧
      res.cost ≤ 100 ∧ res.need ≤ P.length + 80 ∧ res.wk = 0 := by
  have hn2 : V.length + 1 < 2147483648 := hn'
  have hm2 : m + 1 < 2147483648 := hM
  have haM : a < M31 := by show a < 2147483648; omega
  have hbM : b < M31 := by show b < 2147483648; omega
  have hrow : VCS V m V.length 0 (rowKey 0 a) = csRow V m V.length 0 a := by
    rw [rowKey_eq_rk, VCS_cs V m V.length 0 a (by omega)]
  have hrowF := csRow_final V m V.length a ha
  have hxe : (csRow V m V.length 0 a)[b]? = some (P2 V a b) := by
    rw [hrowF, List.getElem?_map, List.getElem?_range (by omega)]; rfl
  set vv := VCS V m V.length 0 with hvv
  -- check 0 <= a
  have ea0 := env_nat mv P [ci a, ci b] 0 1 a (by omega) rfl haM
  have c1 := pstmtM_check_ok mv (gS P [ci a, ci b]) vv _ _ (chk_le0 mv vv _ 1 a ea0) (by decide)
  have q1 := (pexecM_prim mv fu _ _ _).trans c1
  -- declare n
  have d2 := gSM_decl mv P [ci a, ci b] vv i32 nS ((V.length + 1 : Nat) : Int) ((V.length + 1 : Nat) : Int)
    (nS_val mv hnv hf0 hty0 V.length hwr0 vv _ hn2) (conv_signed i32 rfl rfl _ (validN _ hn2))
  have q2 := (pexecM_prim mv fu _ _ _).trans d2
  have hq2 : ([ci a, ci b] ++ [(⟨i32, ((V.length + 1 : Nat) : Int)⟩ : Cell)]) = [ci a, ci b, ci (V.length + 1)] := rfl
  rw [hq2] at q2
  -- check a < n
  have ea1 := env_nat mv P [ci a, ci b, ci (V.length + 1)] 0 1 a (by omega) rfl haM
  have en1 := env_nat mv P [ci a, ci b, ci (V.length + 1)] 2 3 (V.length + 1) (by omega) rfl hn'
  have c3 := pstmtM_check_ok mv (gS P [ci a, ci b, ci (V.length + 1)]) vv _ _ (chk_lt mv vv _ 1 3 a (V.length + 1) ea1 en1 (by omega)) (by decide)
  have q3 := (pexecM_prim mv fu _ _ _).trans c3
  -- check 0 <= b
  have eb1 := env_nat mv P [ci a, ci b, ci (V.length + 1)] 1 2 b (by omega) rfl hbM
  have c4 := pstmtM_check_ok mv (gS P [ci a, ci b, ci (V.length + 1)]) vv _ _ (chk_le0 mv vv _ 2 b eb1) (by decide)
  have q4 := (pexecM_prim mv fu _ _ _).trans c4
  -- declare m
  have haE : aIx.denote (penvN mv.nv (gS P [ci a, ci b, ci (V.length + 1)])) = some (a : Int) := aIx_den _ 1 a ea1 haM
  have d5 := gSM_decl mv P [ci a, ci b, ci (V.length + 1)] vv i32 mS ((m + 1 : Nat) : Int) ((m + 1 : Nat) : Int)
    (by
      have := mS_val mv hnv hf0 hty0 V.length hwr0 vv (gS P [ci a, ci b, ci (V.length + 1)]) a (csRow V m V.length 0 a) haE
        (by omega) hrow (by rw [csRow_length]; exact hm2)
      rw [csRow_length] at this
      exact this)
    (conv_signed i32 rfl rfl _ (validN _ hm2))
  have q5 := (pexecM_prim mv fu _ _ _).trans d5
  have hq5 : ([ci a, ci b, ci (V.length + 1)] ++ [(⟨i32, ((m + 1 : Nat) : Int)⟩ : Cell)]) =
      [ci a, ci b, ci (V.length + 1), ci (m + 1)] := rfl
  rw [hq5] at q5
  -- check b < m + 1
  have eb2 := env_nat mv P [ci a, ci b, ci (V.length + 1), ci (m + 1)] 1 2 b (by omega) rfl hbM
  have em2 := env_nat mv P [ci a, ci b, ci (V.length + 1), ci (m + 1)] 3 4 (m + 1) (by omega) rfl hM
  have c6 := pstmtM_check_ok mv (gS P [ci a, ci b, ci (V.length + 1), ci (m + 1)]) vv _ _
    (chk_lt mv vv _ 2 4 b (m + 1) eb2 em2 (by omega)) (by decide)
  have q6 := (pexecM_prim mv fu _ _ _).trans c6
  -- declare x
  have ea2 := env_nat mv P [ci a, ci b, ci (V.length + 1), ci (m + 1)] 0 1 a (by omega) rfl haM
  have haE2 : aIx.denote (penvN mv.nv (gS P [ci a, ci b, ci (V.length + 1), ci (m + 1)])) = some (a : Int) :=
    aIx_den _ 1 a ea2 haM
  have hbE2 : bIx.denote (penvN mv.nv (gS P [ci a, ci b, ci (V.length + 1), ci (m + 1)])) = some (b : Int) :=
    aIx_den _ 2 b eb2 hbM
  have d7 := gSM_decl mv P [ci a, ci b, ci (V.length + 1), ci (m + 1)] vv s64 xS (P2 V a b) (P2 V a b)
    (xS_val mv hnv hf0 hty0 V.length hwr0 vv _ a b (csRow V m V.length 0 a) (P2 V a b) haE2 hbE2 (by omega) hrow hxe hv)
    (conv_signed s64 rfl rfl _ hv)
  have q7 := (pexecM_prim mv fu _ _ _).trans d7
  have hq7 : ([ci a, ci b, ci (V.length + 1), ci (m + 1)] ++ [(⟨s64, P2 V a b⟩ : Cell)]) =
      [ci a, ci b, ci (V.length + 1), ci (m + 1), cs64 (P2 V a b)] := rfl
  rw [hq7] at q7
  -- ret x
  have ex := gSM_env mv.nv P [ci a, ci b, ci (V.length + 1), ci (m + 1), cs64 (P2 V a b)] 4 (cs64 (P2 V a b)) rfl hv
  rw [show mv.nv + 4 = 5 by omega] at ex
  have hret : vdenM mv vv (penvN mv.nv (gS P [ci a, ci b, ci (V.length + 1), ci (m + 1), cs64 (P2 V a b)]))
      (.variable s64 5) = some (P2 V a b) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact ex
  have r8 := pstmtM_ret_ok mv (gS P [ci a, ci b, ci (V.length + 1), ci (m + 1), cs64 (P2 V a b)]) vv _ _ hret
  have q8 := seqM_ret (mv := mv) (fu := fu) (b := Sk) (a := .primitive (.ret (.variable s64 5))) (by rw [pexecM_prim, r8]) rfl
  have s7 := seqM_some q7 rfl q8
  have s6 := seqM_some q6 rfl s7
  have s5 := seqM_some q5 rfl s6
  have s4 := seqM_some q4 rfl s5
  have s3 := seqM_some q3 rfl s4
  have s2 := seqM_some q2 rfl s3
  have s1 := seqM_some q1 rfl s2
  refine ⟨_, s1, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp_nS, vwp_mS, vwp_xS, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [vwp_nS, vwp_mS, vwp_xS, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
  · simp

/-! ### `CumulativeSum2D<long long>::sum(a1, b1, a2, b2)` (nv = 1).  Cells: 0 = a1, 1 = b1, 2 = a2, 3 = b2, 4 = n, 5 = cols,
6 = p, 7 = q, 8 = r, 9 = s -/

abbrev ixE (x : Nat) : NExpr := .cast u64 (.variable i32 x)
abbrev szE (x : Nat) : NExpr := .cast i32 (.size (.integer s64) (.row (.local 0) (.integer s64) (ixE x)))
abbrev rdE (x y : Nat) : NExpr := .read s64 (.row (.local 0) (.integer s64) (ixE x)) (ixE y)
abbrev sprog4 : Command :=
  .sequence (.primitive (.check (.binary bT .le (.literal i32 0) (.variable i32 1))))
    (.sequence (.primitive (.check (.binary bT .le (.variable i32 1) (.variable i32 3))))
      (.sequence (.primitive (.declare i32 true nS))
        (.sequence (.primitive (.check (.binary bT .lt (.variable i32 3) (.variable i32 5))))
          (.sequence (.primitive (.check (.binary bT .le (.literal i32 0) (.variable i32 2))))
            (.sequence (.primitive (.check (.binary bT .le (.variable i32 2) (.variable i32 4))))
              (.sequence (.primitive (.declare i32 true (szE 3)))
                (.sequence (.primitive (.check (.binary bT .lt (.variable i32 4) (.variable i32 6))))
                  (.sequence (.primitive (.declare s64 true (rdE 3 4)))
                    (.sequence (.primitive (.declare s64 true (rdE 1 4)))
                      (.sequence (.primitive (.declare s64 true (rdE 3 2)))
                        (.sequence (.primitive (.declare s64 true (rdE 1 2)))
                          (.sequence (.primitive (.ret (.binary s64 .add (.binary s64 .sub (.binary s64 .sub (.variable s64 7)
                            (.variable s64 8)) (.variable s64 9)) (.variable s64 10)))) Sk))))))))))))

theorem body_eq_s4 : Proofs.CumulativeSumInstance.CumulativeSum2D_long_long_sum_4.body = sprog4 := rfl

theorem chk_leV (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (x y a c : Nat) (h : env x i32 = some (a : Int))
    (h' : env y i32 = some (c : Int)) (hac : a ≤ c) :
    vdenM mv vv env (.binary bT .le (.variable i32 x) (.variable i32 y)) = some 1 := by
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, den_variable, h, h', Option.bind_some, Option.bind_some, le_conv]
  simp [hac]

theorem szE_val (mv : MV) (hnv : mv.nv = 1) (hf0 : mv.flat 0 = false) (hty0 : mv.ty 0 = s64) (n : Nat)
    (hwr0 : mv.wrows 0 = n + 1) (vv : Nat → List Int) (ps : PS) (x a : Nat) (row : List Int)
    (ha : (ixE x).denote (penvN mv.nv ps) = some (a : Int)) (han : a < n + 1) (hrow : vv (rowKey 0 a) = row)
    (hl : row.length < 2147483648) :
    vdenN mv vv (penvN mv.nv ps) (szE x) = some (row.length : Int) := by
  have hsz : vdenN mv vv (penvN mv.nv ps) (.size (.integer s64) (.row (.local 0) (.integer s64) (ixE x))) =
      some (row.length : Int) := by
    simp only [vdenN]
    rw [if_pos ⟨by omega, hf0, hty0.symm, hty0.symm, rfl⟩, ha, Option.bind_some,
      if_pos ⟨Int.natCast_nonneg a, by rw [Int.toNat_natCast, hwr0]; exact han⟩, Int.toNat_natCast, hrow]
  have hcast : vdenN mv vv (penvN mv.nv ps) (szE x) =
      (vdenN mv vv (penvN mv.nv ps) (.size (.integer s64) (.row (.local 0) (.integer s64) (ixE x)))).bind i32.convert := by
    simp only [szE]; rw [vdenN]
  rw [hcast, hsz, Option.bind_some]
  exact conv_signed i32 rfl rfl _ (validN _ hl)

theorem rdE_val (mv : MV) (hnv : mv.nv = 1) (hf0 : mv.flat 0 = false) (hty0 : mv.ty 0 = s64) (n : Nat)
    (hwr0 : mv.wrows 0 = n + 1) (vv : Nat → List Int) (ps : PS) (x y a b : Nat) (row : List Int) (v : Int)
    (ha : (ixE x).denote (penvN mv.nv ps) = some (a : Int)) (hb : (ixE y).denote (penvN mv.nv ps) = some (b : Int))
    (han : a < n + 1) (hrow : vv (rowKey 0 a) = row) (hx : row[b]? = some v) (hxv : s64.valid v = true) :
    vdenN mv vv (penvN mv.nv ps) (rdE x y) = some v := by
  simp only [rdE, vdenN]
  rw [if_pos ⟨by omega, hf0, hty0.symm, hty0.symm, rfl, rfl⟩]
  rw [ha, Option.bind_some, hb, Option.bind_some, if_pos ⟨Int.natCast_nonneg a, by rw [Int.toNat_natCast, hwr0]; exact han⟩,
    Int.toNat_natCast, hrow]
  unfold elemAtL
  rw [if_pos (Int.natCast_nonneg b), Int.toNat_natCast, hx, Option.bind_some, hty0, if_pos hxv]

theorem vwp_szE (x : Nat) : vwp (szE x) = (7, 7) := by simp [szE, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
theorem vwp_rdE (x y : Nat) : vwp (rdE x y) = (8, 8) := by simp [rdE, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]

theorem bin_den (env : Nat → Ty → Option Int) (op : Binary) (e1 e2 : NExpr) (u w : Int) (h1 : e1.denote env = some u)
    (h2 : e2.denote env = some w) (hv : s64.valid (binaryValue op u w) = true) :
    (NExpr.binary s64 op e1 e2).denote env = some (binaryValue op u w) := by
  rw [den_binary, h1, h2, Option.bind_some, Option.bind_some, Ty.convert_of_valid _ _ hv]

theorem sum4_exec (mv : MV) (hnv : mv.nv = 1) (hf0 : mv.flat 0 = false) (hty0 : mv.ty 0 = s64) (V : List (List Int)) (m : Nat)
    (hwr0 : mv.wrows 0 = V.length + 1) (fu : Nat) (P : List Cell) (a1 b1 a2 b2 : Nat) (h1 : a1 ≤ a2) (h2 : a2 ≤ V.length)
    (h3 : b1 ≤ b2) (h4 : b2 ≤ m) (hn' : V.length + 1 < M31) (hM : m + 1 < M31)
    (hp : s64.valid (P2 V a2 b2) = true) (hq : s64.valid (P2 V a1 b2) = true) (hr : s64.valid (P2 V a2 b1) = true)
    (hs : s64.valid (P2 V a1 b1) = true) (hv1 : s64.valid (P2 V a2 b2 - P2 V a1 b2) = true)
    (hv2 : s64.valid (P2 V a2 b2 - P2 V a1 b2 - P2 V a2 b1) = true)
    (hv3 : s64.valid (P2 V a2 b2 - P2 V a1 b2 - P2 V a2 b1 + P2 V a1 b1) = true) :
    ∃ res : PRM, pexecM mv fu sprog4 (gS P [ci a1, ci b1, ci a2, ci b2]) (VCS V m V.length 0) = some res ∧
      res.ret = some (P2 V a2 b2 - P2 V a1 b2 - P2 V a2 b1 + P2 V a1 b1) ∧ res.vv = VCS V m V.length 0 ∧
      res.ps = gS P [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1), ci (m + 1), cs64 (P2 V a2 b2), cs64 (P2 V a1 b2), cs64 (P2 V a2 b1), cs64 (P2 V a1 b1)] ∧
      res.cost ≤ 200 ∧ res.need ≤ P.length + 80 ∧ res.wk = 0 := by
  have hn2 : V.length + 1 < 2147483648 := hn'
  have hm2 : m + 1 < 2147483648 := hM
  have ha1 : a1 < M31 := by show a1 < 2147483648; omega
  have ha2 : a2 < M31 := by show a2 < 2147483648; omega
  have hb1 : b1 < M31 := by show b1 < 2147483648; omega
  have hb2 : b2 < M31 := by show b2 < 2147483648; omega
  set vv := VCS V m V.length 0 with hvv
  have hrow : ∀ a, a ≤ V.length → vv (rowKey 0 a) = csRow V m V.length 0 a := by
    intro a ha
    rw [rowKey_eq_rk, hvv, VCS_cs V m V.length 0 a (by omega)]
  have hxe : ∀ a b, a ≤ V.length → b ≤ m → (csRow V m V.length 0 a)[b]? = some (P2 V a b) := by
    intro a b ha hb
    rw [csRow_final V m V.length a ha, List.getElem?_map, List.getElem?_range (by omega)]; rfl
  have hcl : ∀ a, (csRow V m V.length 0 a).length < 2147483648 := by
    intro a; rw [csRow_length]; exact hm2
  -- check 0 <= a1
  have e1 := env_nat mv P [ci a1, ci b1, ci a2, ci b2] 0 1 a1 (by omega) rfl ha1
  have c1 := pstmtM_check_ok mv (gS P [ci a1, ci b1, ci a2, ci b2]) vv _ _ (chk_le0 mv vv _ 1 a1 e1) (by decide)
  have q1 := (pexecM_prim mv fu _ _ _).trans c1
  -- check a1 <= a2
  have e3 := env_nat mv P [ci a1, ci b1, ci a2, ci b2] 2 3 a2 (by omega) rfl ha2
  have c2 := pstmtM_check_ok mv (gS P [ci a1, ci b1, ci a2, ci b2]) vv _ _ (chk_leV mv vv _ 1 3 a1 a2 e1 e3 h1) (by decide)
  have q2 := (pexecM_prim mv fu _ _ _).trans c2
  -- declare n
  have d3 := gSM_decl mv P [ci a1, ci b1, ci a2, ci b2] vv i32 nS ((V.length + 1 : Nat) : Int) ((V.length + 1 : Nat) : Int)
    (nS_val mv hnv hf0 hty0 V.length hwr0 vv _ hn2) (conv_signed i32 rfl rfl _ (validN _ hn2))
  have q3 := (pexecM_prim mv fu _ _ _).trans d3
  have hq3 : ([ci a1, ci b1, ci a2, ci b2] ++ [(⟨i32, ((V.length + 1 : Nat) : Int)⟩ : Cell)]) = [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1)] := rfl
  rw [hq3] at q3
  -- check a2 < n
  have e3' := env_nat mv P [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1)] 2 3 a2 (by omega) rfl ha2
  have e5 := env_nat mv P [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1)] 4 5 (V.length + 1) (by omega) rfl hn'
  have c4 := pstmtM_check_ok mv (gS P [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1)]) vv _ _ (chk_lt mv vv _ 3 5 a2 (V.length + 1) e3' e5 (by omega)) (by decide)
  have q4 := (pexecM_prim mv fu _ _ _).trans c4
  -- check 0 <= b1
  have e2 := env_nat mv P [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1)] 1 2 b1 (by omega) rfl hb1
  have c5 := pstmtM_check_ok mv (gS P [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1)]) vv _ _ (chk_le0 mv vv _ 2 b1 e2) (by decide)
  have q5 := (pexecM_prim mv fu _ _ _).trans c5
  -- check b1 <= b2
  have e4 := env_nat mv P [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1)] 3 4 b2 (by omega) rfl hb2
  have c6 := pstmtM_check_ok mv (gS P [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1)]) vv _ _ (chk_leV mv vv _ 2 4 b1 b2 e2 e4 h3) (by decide)
  have q6 := (pexecM_prim mv fu _ _ _).trans c6
  -- declare cols
  have i3 : (ixE 3).denote (penvN mv.nv (gS P [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1)])) = some (a2 : Int) := aIx_den _ 3 a2 e3' ha2
  have d7 := gSM_decl mv P [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1)] vv i32 (szE 3) ((m + 1 : Nat) : Int) ((m + 1 : Nat) : Int)
    (by
      have := szE_val mv hnv hf0 hty0 V.length hwr0 vv (gS P [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1)]) 3 a2 (csRow V m V.length 0 a2) i3
        (by omega) (hrow a2 h2) (hcl a2)
      rw [csRow_length] at this
      exact this)
    (conv_signed i32 rfl rfl _ (validN _ hm2))
  have q7 := (pexecM_prim mv fu _ _ _).trans d7
  have hq7 : ([ci a1, ci b1, ci a2, ci b2, ci (V.length + 1)] ++ [(⟨i32, ((m + 1 : Nat) : Int)⟩ : Cell)]) = [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1), ci (m + 1)] := rfl
  rw [hq7] at q7
  -- check b2 < cols
  have e4' := env_nat mv P [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1), ci (m + 1)] 3 4 b2 (by omega) rfl hb2
  have e6 := env_nat mv P [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1), ci (m + 1)] 5 6 (m + 1) (by omega) rfl hM
  have c8 := pstmtM_check_ok mv (gS P [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1), ci (m + 1)]) vv _ _ (chk_lt mv vv _ 4 6 b2 (m + 1) e4' e6 (by omega)) (by decide)
  have q8 := (pexecM_prim mv fu _ _ _).trans c8
  -- index denotations in the later states
  have idx : ∀ (cells : List Cell) (k x a : Nat), x = mv.nv + k → cells[k]? = some (ci a) → a < M31 →
      (ixE x).denote (penvN mv.nv (gS P cells)) = some (a : Int) :=
    fun cells k x a hx hk ha => aIx_den _ x a (env_nat mv P cells k x a hx hk ha) ha
  -- declare p = cs[a2][b2]
  have d9 := gSM_decl mv P [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1), ci (m + 1)] vv s64 (rdE 3 4) (P2 V a2 b2) (P2 V a2 b2)
    (rdE_val mv hnv hf0 hty0 V.length hwr0 vv _ 3 4 a2 b2 (csRow V m V.length 0 a2) (P2 V a2 b2)
      (idx _ 2 3 a2 (by omega) rfl ha2) (idx _ 3 4 b2 (by omega) rfl hb2) (by omega) (hrow a2 h2) (hxe a2 b2 h2 h4) hp)
    (conv_signed s64 rfl rfl _ hp)
  have q9 := (pexecM_prim mv fu _ _ _).trans d9
  have hq9 : ([ci a1, ci b1, ci a2, ci b2, ci (V.length + 1), ci (m + 1)] ++ [(⟨s64, P2 V a2 b2⟩ : Cell)]) = [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1), ci (m + 1), cs64 (P2 V a2 b2)] := rfl
  rw [hq9] at q9
  -- declare q = cs[a1][b2]
  have d10 := gSM_decl mv P [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1), ci (m + 1), cs64 (P2 V a2 b2)] vv s64 (rdE 1 4) (P2 V a1 b2) (P2 V a1 b2)
    (rdE_val mv hnv hf0 hty0 V.length hwr0 vv _ 1 4 a1 b2 (csRow V m V.length 0 a1) (P2 V a1 b2)
      (idx _ 0 1 a1 (by omega) rfl ha1) (idx _ 3 4 b2 (by omega) rfl hb2) (by omega) (hrow a1 (by omega)) (hxe a1 b2 (by omega) h4) hq)
    (conv_signed s64 rfl rfl _ hq)
  have q10 := (pexecM_prim mv fu _ _ _).trans d10
  have hq10 : ([ci a1, ci b1, ci a2, ci b2, ci (V.length + 1), ci (m + 1), cs64 (P2 V a2 b2)] ++ [(⟨s64, P2 V a1 b2⟩ : Cell)]) = [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1), ci (m + 1), cs64 (P2 V a2 b2), cs64 (P2 V a1 b2)] := rfl
  rw [hq10] at q10
  -- declare r = cs[a2][b1]
  have d11 := gSM_decl mv P [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1), ci (m + 1), cs64 (P2 V a2 b2), cs64 (P2 V a1 b2)] vv s64 (rdE 3 2) (P2 V a2 b1) (P2 V a2 b1)
    (rdE_val mv hnv hf0 hty0 V.length hwr0 vv _ 3 2 a2 b1 (csRow V m V.length 0 a2) (P2 V a2 b1)
      (idx _ 2 3 a2 (by omega) rfl ha2) (idx _ 1 2 b1 (by omega) rfl hb1) (by omega) (hrow a2 h2) (hxe a2 b1 h2 (by omega)) hr)
    (conv_signed s64 rfl rfl _ hr)
  have q11 := (pexecM_prim mv fu _ _ _).trans d11
  have hq11 : ([ci a1, ci b1, ci a2, ci b2, ci (V.length + 1), ci (m + 1), cs64 (P2 V a2 b2), cs64 (P2 V a1 b2)] ++ [(⟨s64, P2 V a2 b1⟩ : Cell)]) = [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1), ci (m + 1), cs64 (P2 V a2 b2), cs64 (P2 V a1 b2), cs64 (P2 V a2 b1)] := rfl
  rw [hq11] at q11
  -- declare s = cs[a1][b1]
  have d12 := gSM_decl mv P [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1), ci (m + 1), cs64 (P2 V a2 b2), cs64 (P2 V a1 b2), cs64 (P2 V a2 b1)] vv s64 (rdE 1 2) (P2 V a1 b1) (P2 V a1 b1)
    (rdE_val mv hnv hf0 hty0 V.length hwr0 vv _ 1 2 a1 b1 (csRow V m V.length 0 a1) (P2 V a1 b1)
      (idx _ 0 1 a1 (by omega) rfl ha1) (idx _ 1 2 b1 (by omega) rfl hb1) (by omega) (hrow a1 (by omega)) (hxe a1 b1 (by omega) (by omega)) hs)
    (conv_signed s64 rfl rfl _ hs)
  have q12 := (pexecM_prim mv fu _ _ _).trans d12
  have hq12 : ([ci a1, ci b1, ci a2, ci b2, ci (V.length + 1), ci (m + 1), cs64 (P2 V a2 b2), cs64 (P2 V a1 b2), cs64 (P2 V a2 b1)] ++ [(⟨s64, P2 V a1 b1⟩ : Cell)]) = [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1), ci (m + 1), cs64 (P2 V a2 b2), cs64 (P2 V a1 b2), cs64 (P2 V a2 b1), cs64 (P2 V a1 b1)] := rfl
  rw [hq12] at q12
  -- ret
  have v7 := gSM_env mv.nv P [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1), ci (m + 1), cs64 (P2 V a2 b2), cs64 (P2 V a1 b2), cs64 (P2 V a2 b1), cs64 (P2 V a1 b1)] 6 (cs64 (P2 V a2 b2)) rfl hp
  have v8 := gSM_env mv.nv P [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1), ci (m + 1), cs64 (P2 V a2 b2), cs64 (P2 V a1 b2), cs64 (P2 V a2 b1), cs64 (P2 V a1 b1)] 7 (cs64 (P2 V a1 b2)) rfl hq
  have v9 := gSM_env mv.nv P [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1), ci (m + 1), cs64 (P2 V a2 b2), cs64 (P2 V a1 b2), cs64 (P2 V a2 b1), cs64 (P2 V a1 b1)] 8 (cs64 (P2 V a2 b1)) rfl hr
  have v10 := gSM_env mv.nv P [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1), ci (m + 1), cs64 (P2 V a2 b2), cs64 (P2 V a1 b2), cs64 (P2 V a2 b1), cs64 (P2 V a1 b1)] 9 (cs64 (P2 V a1 b1)) rfl hs
  rw [show mv.nv + 6 = 7 by omega] at v7
  rw [show mv.nv + 7 = 8 by omega] at v8
  rw [show mv.nv + 8 = 9 by omega] at v9
  rw [show mv.nv + 9 = 10 by omega] at v10
  have x7 : (NExpr.variable s64 7).denote (penvN mv.nv (gS P [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1), ci (m + 1), cs64 (P2 V a2 b2), cs64 (P2 V a1 b2), cs64 (P2 V a2 b1), cs64 (P2 V a1 b1)])) = some (P2 V a2 b2) := by rw [den_variable]; exact v7
  have x8 : (NExpr.variable s64 8).denote (penvN mv.nv (gS P [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1), ci (m + 1), cs64 (P2 V a2 b2), cs64 (P2 V a1 b2), cs64 (P2 V a2 b1), cs64 (P2 V a1 b1)])) = some (P2 V a1 b2) := by rw [den_variable]; exact v8
  have x9 : (NExpr.variable s64 9).denote (penvN mv.nv (gS P [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1), ci (m + 1), cs64 (P2 V a2 b2), cs64 (P2 V a1 b2), cs64 (P2 V a2 b1), cs64 (P2 V a1 b1)])) = some (P2 V a2 b1) := by rw [den_variable]; exact v9
  have x10 : (NExpr.variable s64 10).denote (penvN mv.nv (gS P [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1), ci (m + 1), cs64 (P2 V a2 b2), cs64 (P2 V a1 b2), cs64 (P2 V a2 b1), cs64 (P2 V a1 b1)])) = some (P2 V a1 b1) := by rw [den_variable]; exact v10
  have y1 := bin_den _ .sub _ _ _ _ x7 x8 (by simpa [binaryValue] using hv1)
  have y2 := bin_den _ .sub _ _ _ _ y1 x9 (by simpa [binaryValue] using hv2)
  have y3 := bin_den _ .add _ _ _ _ y2 x10 (by simpa [binaryValue] using hv3)
  simp only [binaryValue] at y3
  have hret : vdenM mv vv (penvN mv.nv (gS P [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1), ci (m + 1), cs64 (P2 V a2 b2), cs64 (P2 V a1 b2), cs64 (P2 V a2 b1), cs64 (P2 V a1 b1)]))
      (.binary s64 .add (.binary s64 .sub (.binary s64 .sub (.variable s64 7) (.variable s64 8)) (.variable s64 9)) (.variable s64 10)) =
      some (P2 V a2 b2 - P2 V a1 b2 - P2 V a2 b1 + P2 V a1 b1) := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact y3
  have r13 := pstmtM_ret_ok mv (gS P [ci a1, ci b1, ci a2, ci b2, ci (V.length + 1), ci (m + 1), cs64 (P2 V a2 b2), cs64 (P2 V a1 b2), cs64 (P2 V a2 b1), cs64 (P2 V a1 b1)]) vv _ _ hret
  have q13 := seqM_ret (mv := mv) (fu := fu) (b := Sk) (a := .primitive (.ret (.binary s64 .add (.binary s64 .sub
    (.binary s64 .sub (.variable s64 7) (.variable s64 8)) (.variable s64 9)) (.variable s64 10)))) (by rw [pexecM_prim, r13]) rfl
  have s12 := seqM_some q12 rfl q13
  have s11 := seqM_some q11 rfl s12
  have s10 := seqM_some q10 rfl s11
  have s9 := seqM_some q9 rfl s10
  have s8 := seqM_some q8 rfl s9
  have s7 := seqM_some q7 rfl s8
  have s6 := seqM_some q6 rfl s7
  have s5 := seqM_some q5 rfl s6
  have s4 := seqM_some q4 rfl s5
  have s3 := seqM_some q3 rfl s4
  have s2 := seqM_some q2 rfl s3
  have s1 := seqM_some q1 rfl s2
  refine ⟨_, s1, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp_nS, vwp_szE, vwp_rdE, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [vwp_nS, vwp_szE, vwp_rdE, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
  · simp

end Proofs.CumulativeSum2DExec
