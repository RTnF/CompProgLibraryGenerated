import Proofs.CumulativeSum2DExec
import Proofs.FloydWarshallCall
import Proofs.Generated.FloydWarshall

namespace Proofs.FloydNestedExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVecN Proofs.MultiKitN Proofs.ForLoopMN Proofs.ForLoopCN
open Proofs.ForLoopBN Proofs.VecStmtX
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested
open Proofs.PowModStep (Sk)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.PrefixSumsCall (bT)
open Proofs.BellmanFordExec (cidx_den M31 i32_valid_nat s64_valid_of)
open Proofs.CumulativeSum2DMath (rk)
open Proofs.CumulativeSum2DExec (rdE ixE rdE_val env_nat aIx_den nS nS_val vwp_nS vwp_rdE lt_conv bin_den)
open Proofs.FloydWarshallCall (Dm Em Dm_le Em_col Em_row Em_here Em_next Em_other Em_row_end Em_start Em_end)

theorem pexecM_branch_true (mv : MV) (fu : Nat) (c : NExpr) (y n : Command) (ps : PS) (vv : Nat → List Int) (v : Int)
    (hv : vdenM mv vv (penvN mv.nv ps) c = some v) (hne : v ≠ 0) (r : PRM) (hr : pexecM mv fu y ps vv = some r) :
    pexecM mv fu (.branch c y n) ps vv =
      some ⟨r.ps,r.vv,r.ret,r.cost+(vwp c).1+1,max (ps.mem.length+ps.bs.length+(vwp c).2+2) r.need,r.wk⟩ := by
  rw [pexecM]
  simp [hv, hne, hr]

theorem pexecM_branch_false (mv : MV) (fu : Nat) (c : NExpr) (y n : Command) (ps : PS) (vv : Nat → List Int)
    (hv : vdenM mv vv (penvN mv.nv ps) c = some 0) (r : PRM) (hr : pexecM mv fu n ps vv = some r) :
    pexecM mv fu (.branch c y n) ps vv =
      some ⟨r.ps,r.vv,r.ret,r.cost+(vwp c).1+1,max (ps.mem.length+ps.bs.length+(vwp c).2+2) r.need,r.wk⟩ := by
  rw [pexecM]
  simp [hv, hr]

abbrev cs64 (x : Int) : Cell := ⟨s64, x⟩
abbrev condFW : NExpr := .binary bT .lt (.variable s64 7) (.variable s64 8)
abbrev thenW : Command :=
  .sequence (.scope (.sequence (.primitive (.write (.row (.local 0) (.integer s64) (ixE 3)) s64 (ixE 4) (.variable s64 7))) Sk)) Sk
abbrev bodyJ : Command :=
  .sequence (.primitive (.declare s64 true (rdE 3 2)))
    (.sequence (.primitive (.declare s64 true (rdE 2 4)))
      (.sequence (.primitive (.declare s64 true (.binary s64 .add (.variable s64 5) (.variable s64 6))))
        (.sequence (.primitive (.declare s64 true (rdE 3 4))) (.sequence (.branch condFW thenW Sk) Sk))))
abbrev bodyI (nv : Nat) : Command := .sequence (forStmtB nv 3 0 bodyJ) Sk
abbrev bodyK (nv : Nat) : Command := .sequence (forStmtB nv 2 0 (bodyI nv)) Sk
abbrev progFW (nv : Nat) : Command := .sequence (.primitive (.declare i32 true nS)) (.sequence (forStmtB nv 1 0 (bodyK nv)) Sk)

theorem body_eqN : Proofs.FloydWarshallInstance.floyd_warshall_std_vector_std_vector_long_long.body = progFW 1 := rfl

/-- The rows of the matrix `Em W k i j` (`n` rows of `n` entries) as the contents of the nested root (row `p` is `rowKey 0 p`). -/
def FV (W : Nat → Nat → Nat) (n k i j : Nat) : Nat → List Int := fun key =>
  if key / 4294967296 = 1 ∧ key % 4294967296 < n then
    (List.range n).map (fun q => (Em W k i j (key % 4294967296) q : Int))
  else []

theorem FV_row (W : Nat → Nat → Nat) (n k i j p : Nat) (hn : n < 4294967296) (hp : p < n) :
    FV W n k i j (rowKey 0 p) = (List.range n).map (fun q => (Em W k i j p q : Int)) := by
  unfold FV rowKey
  have e1 : (4294967296 * (0 + 1) + p) / 4294967296 = 1 := by omega
  have e2 : (4294967296 * (0 + 1) + p) % 4294967296 = p := by omega
  simp [e1, e2, hp]

theorem FV_get (W : Nat → Nat → Nat) (n k i j p q : Nat) (hn : n < 4294967296) (hp : p < n) (hq : q < n) :
    (FV W n k i j (rowKey 0 p))[q]? = some (Em W k i j p q : Int) := by
  rw [FV_row W n k i j p hn hp, List.getElem?_map, List.getElem?_range hq]
  rfl

theorem FV_len (W : Nat → Nat → Nat) (n k i j p : Nat) (hn : n < 4294967296) (hp : p < n) :
    (FV W n k i j (rowKey 0 p)).length = n := by
  rw [FV_row W n k i j p hn hp]; simp

theorem FV_upd (W : Nat → Nat → Nat) (n k i j : Nat) (hn : n < 4294967296) (hi : i < n) (hj : j < n) :
    upd (FV W n k i j) (rowKey 0 i)
      (((FV W n k i j) (rowKey 0 i)).set j ((Dm W (k + 1) i j : Nat) : Int)) = FV W n k i (j + 1) := by
  funext key
  unfold upd
  by_cases hk : key = rowKey 0 i
  · subst hk
    simp only [if_true]
    rw [FV_row W n k i j i hn hi, FV_row W n k i (j + 1) i hn hi]
    apply List.ext_getElem?
    intro q
    rw [List.getElem?_set, List.getElem?_map, List.getElem?_map]
    by_cases hq : j = q
    · subst hq
      simp [hj, Em_next]
    · simp only [hq, if_false]
      by_cases hqn : q < n
      · rw [List.getElem?_range hqn]
        simp [Em_other W k i j i q (fun h => hq h.2.symm)]
      · rw [List.getElem?_eq_none (by simp; omega)]
        rfl
  · simp only [hk, if_false]
    unfold FV
    by_cases hc : key / 4294967296 = 1 ∧ key % 4294967296 < n
    · simp only [hc, and_self, if_true]
      apply List.map_congr_left
      intro q _
      have hne : key % 4294967296 ≠ i := by
        intro h
        apply hk
        unfold rowKey
        omega
      rw [Em_other W k i j _ q (fun h => hne h.1)]
    · simp [hc]

theorem FV_same (W : Nat → Nat → Nat) (n k i j : Nat)
    (h : Dm W (k + 1) i j = Dm W k i j) : FV W n k i (j + 1) = FV W n k i j := by
  funext key
  unfold FV
  by_cases hc : key / 4294967296 = 1 ∧ key % 4294967296 < n
  · simp only [hc, and_self, if_true]
    apply List.map_congr_left
    intro q _
    by_cases hpq : key % 4294967296 = i ∧ q = j
    · obtain ⟨h1, h2⟩ := hpq
      rw [h1, h2, Em_next, Em_here, h]
    · rw [Em_other W k i j _ q hpq]
  · simp [hc]

theorem FV_rowend (W : Nat → Nat → Nat) (n k i : Nat) : FV W n k i n = FV W n k (i + 1) 0 := by
  funext key
  unfold FV
  by_cases hc : key / 4294967296 = 1 ∧ key % 4294967296 < n
  · simp only [hc, and_self, if_true]
    apply List.map_congr_left
    intro q hq
    rw [Em_row_end W k i n _ q (by simpa using hq)]
  · simp [hc]

theorem FV_roundend (W : Nat → Nat → Nat) (n k : Nat) : FV W n k n 0 = FV W n (k + 1) 0 0 := by
  funext key
  unfold FV
  by_cases hc : key / 4294967296 = 1 ∧ key % 4294967296 < n
  · simp only [hc, and_self, if_true]
    apply List.map_congr_left
    intro q _
    rw [Em_end W k n _ q hc.2, Em_start]
  · simp [hc]

theorem vwp_cond : vwp condFW = (3, 3) := by simp [condFW, vwp, NExpr.nodes, NExpr.scalarOnly]
theorem vwp_add56 : vwp (.binary s64 .add (.variable s64 5) (.variable s64 6)) = (3, 3) := by
  simp [vwp, NExpr.nodes, NExpr.scalarOnly]

theorem jbody_exec (mv : MV) (hnv : mv.nv = 1) (hf0 : mv.flat 0 = false) (hty0 : mv.ty 0 = s64) (hw0 : mv.wN 0 = true)
    (W : Nat → Nat → Nat) (n k i j : Nat) (hwr0 : mv.wrows 0 = n) (fu : Nat) (P : List Cell) (hk : k < n) (hi : i < n)
    (hj : j < n) (hn : n < M31) (hW : ∀ p q, W p q < 4611686018427387904) :
    ∃ res : PRM, pexecM mv fu bodyJ (gS P ([ci n, ci k, ci i] ++ [ci j])) (FV W n k i j) = some res ∧ res.ret = none ∧
      ∃ cs', res.ps = gS P ([ci n, ci k, ci i] ++ [ci j] ++ cs') ∧ res.vv = FV W n k i (j + 1) ∧
        res.cost ≤ 200 ∧ res.need ≤ P.length + 100 ∧ res.wk ≤ 1 := by
  obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hn2 : n < 2147483648 := hn
  have hn32 : n < 4294967296 := by omega
  have hkM : k < M31 := by show k < 2147483648; omega
  have hiM : i < M31 := by show i < 2147483648; omega
  have hjM : j < M31 := by show j < 2147483648; omega
  have hDm : ∀ k' p q, (Dm W k' p q : Int) < 4611686018427387904 := by
    intro k' p q
    have := Nat.lt_of_le_of_lt (Dm_le W k' p q) (hW p q)
    omega
  have hs : ∀ x : Nat, x < 9223372036854775808 → s64.valid (x : Int) = true := fun x h =>
    Proofs.FloydWarshallCall.s64v x h
  set vv := FV W n k i j with hvv
  have idxD : ∀ (cells : List Cell) (kk x a : Nat), x = mv.nv + kk → cells[kk]? = some (ci a) → a < M31 →
      (ixE x).denote (penvN mv.nv (gS P cells)) = some (a : Int) :=
    fun cells kk x a hx hc ha => aIx_den _ x a (env_nat mv P cells kk x a hx hc ha) ha
  have rd : ∀ (cells : List Cell) (x y kx ky p q : Nat) (v : Int), x = mv.nv + kx → y = mv.nv + ky →
      cells[kx]? = some (ci p) → cells[ky]? = some (ci q) → p < n → q < n → (vv (rowKey 0 p))[q]? = some v →
      s64.valid v = true → vdenN mv vv (penvN mv.nv (gS P cells)) (rdE x y) = some v := by
    intro cells x y kx ky p q v hx hy hcx hcy hp hq hv hvv'
    exact rdE_val mv hnv hf0 hty0 n' (by omega) vv _ x y p q (vv (rowKey 0 p)) v
      (idxD cells kx x p hx hcx (by omega)) (idxD cells ky y q hy hcy (by omega)) (by omega) rfl hv hvv'
  have hrowget : ∀ p q, p < n → q < n → (vv (rowKey 0 p))[q]? = some (Em W k i j p q : Int) :=
    fun p q hp hq => FV_get W n k i j p q hn32 hp hq
  have ha : (Dm W k i k : Int) < 4611686018427387904 := hDm k i k
  have hb : (Dm W k k j : Int) < 4611686018427387904 := hDm k k j
  have hc : (Dm W k i j : Int) < 4611686018427387904 := hDm k i j
  have hsa : s64.valid (Dm W k i k : Int) = true := hs _ (by omega)
  have hsb : s64.valid (Dm W k k j : Int) = true := hs _ (by omega)
  have hsc : s64.valid (Dm W k i j : Int) = true := hs _ (by omega)
  have hsab : s64.valid ((Dm W k i k : Int) + (Dm W k k j : Int)) = true := by
    have := hs (Dm W k i k + Dm W k k j) (by omega)
    simpa using this
  -- dik = d[i][k]
  have d1 := gSM_decl mv P ([ci n, ci k, ci i] ++ [ci j]) vv s64 (rdE 3 2) (Dm W k i k : Int) (Dm W k i k : Int)
    (rd _ 3 2 2 1 i k _ (by omega) (by omega) rfl rfl hi hk (by rw [hrowget i k hi hk, Em_col]) hsa)
    (conv_signed s64 rfl rfl _ hsa)
  have q1 := (pexecM_prim mv fu _ _ _).trans d1
  -- dkj = d[k][j]
  have d2 := gSM_decl mv P ([ci n, ci k, ci i] ++ [ci j] ++ [cs64 (Dm W k i k : Int)]) vv s64 (rdE 2 4) (Dm W k k j : Int)
    (Dm W k k j : Int)
    (rd _ 2 4 1 3 k j _ (by omega) (by omega) rfl rfl hk hj (by rw [hrowget k j hk hj, Em_row]) hsb)
    (conv_signed s64 rfl rfl _ hsb)
  have q2 := (pexecM_prim mv fu _ _ _).trans d2
  -- via = dik + dkj
  have e5 := gSM_env mv.nv P ([ci n, ci k, ci i] ++ [ci j] ++ [cs64 (Dm W k i k : Int)] ++ [cs64 (Dm W k k j : Int)]) 4
    (cs64 (Dm W k i k : Int)) rfl hsa
  have e6 := gSM_env mv.nv P ([ci n, ci k, ci i] ++ [ci j] ++ [cs64 (Dm W k i k : Int)] ++ [cs64 (Dm W k k j : Int)]) 5
    (cs64 (Dm W k k j : Int)) rfl hsb
  rw [show mv.nv + 4 = 5 by omega] at e5
  rw [show mv.nv + 5 = 6 by omega] at e6
  have hviaE : vdenN mv vv (penvN mv.nv (gS P ([ci n, ci k, ci i] ++ [ci j] ++ [cs64 (Dm W k i k : Int)] ++
      [cs64 (Dm W k k j : Int)]))) (.binary s64 .add (.variable s64 5) (.variable s64 6)) =
      some ((Dm W k i k : Int) + (Dm W k k j : Int)) := by
    rw [vdenN_scalar _ _ _ _ rfl]
    exact bin_den _ .add _ _ _ _ (by rw [den_variable]; exact e5) (by rw [den_variable]; exact e6) (by simpa [binaryValue] using hsab)
  have d3 := gSM_decl mv P ([ci n, ci k, ci i] ++ [ci j] ++ [cs64 (Dm W k i k : Int)] ++ [cs64 (Dm W k k j : Int)]) vv s64
    (.binary s64 .add (.variable s64 5) (.variable s64 6)) ((Dm W k i k : Int) + (Dm W k k j : Int))
    ((Dm W k i k : Int) + (Dm W k k j : Int)) (by simpa [binaryValue] using hviaE) (conv_signed s64 rfl rfl _ hsab)
  have q3 := (pexecM_prim mv fu _ _ _).trans d3
  -- dij = d[i][j]
  have d4 := gSM_decl mv P ([ci n, ci k, ci i] ++ [ci j] ++ [cs64 (Dm W k i k : Int)] ++ [cs64 (Dm W k k j : Int)] ++
      [cs64 ((Dm W k i k : Int) + (Dm W k k j : Int))]) vv s64 (rdE 3 4) (Dm W k i j : Int) (Dm W k i j : Int)
    (rd _ 3 4 2 3 i j _ (by omega) (by omega) rfl rfl hi hj (by rw [hrowget i j hi hj, Em_here]) hsc)
    (conv_signed s64 rfl rfl _ hsc)
  have q4 := (pexecM_prim mv fu _ _ _).trans d4
  -- the condition via < dij
  have e7 := gSM_env mv.nv P ([ci n, ci k, ci i] ++ [ci j] ++ [cs64 (Dm W k i k : Int)] ++ [cs64 (Dm W k k j : Int)] ++ [cs64 ((Dm W k i k : Int) + (Dm W k k j : Int))] ++ [cs64 (Dm W k i j : Int)]) 6 (cs64 ((Dm W k i k : Int) + (Dm W k k j : Int))) rfl hsab
  have e8 := gSM_env mv.nv P ([ci n, ci k, ci i] ++ [ci j] ++ [cs64 (Dm W k i k : Int)] ++ [cs64 (Dm W k k j : Int)] ++ [cs64 ((Dm W k i k : Int) + (Dm W k k j : Int))] ++ [cs64 (Dm W k i j : Int)]) 7 (cs64 (Dm W k i j : Int)) rfl hsc
  rw [show mv.nv + 6 = 7 by omega] at e7
  rw [show mv.nv + 7 = 8 by omega] at e8
  have hcond : vdenM mv vv (penvN mv.nv (gS P ([ci n, ci k, ci i] ++ [ci j] ++ [cs64 (Dm W k i k : Int)] ++ [cs64 (Dm W k k j : Int)] ++ [cs64 ((Dm W k i k : Int) + (Dm W k k j : Int))] ++ [cs64 (Dm W k i j : Int)]))) condFW =
      some (if (Dm W k i k : Int) + (Dm W k k j : Int) < (Dm W k i j : Int) then 1 else 0) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, e7, Option.bind_some, den_variable, e8, Option.bind_some]
    exact lt_conv _ _
  obtain ⟨rb, hrb, hrbret, hrbps, hrbvv, hrbc, hrbn, hrbw⟩ : ∃ rb : PRM,
      pexecM mv fu (.sequence (.branch condFW thenW Sk) Sk) (gS P ([ci n, ci k, ci i] ++ [ci j] ++ [cs64 (Dm W k i k : Int)] ++ [cs64 (Dm W k k j : Int)] ++ [cs64 ((Dm W k i k : Int) + (Dm W k k j : Int))] ++ [cs64 (Dm W k i j : Int)])) vv = some rb ∧ rb.ret = none ∧
      rb.ps = gS P ([ci n, ci k, ci i] ++ [ci j] ++ [cs64 (Dm W k i k : Int)] ++ [cs64 (Dm W k k j : Int)] ++ [cs64 ((Dm W k i k : Int) + (Dm W k k j : Int))] ++ [cs64 (Dm W k i j : Int)]) ∧ rb.vv = FV W n k i (j + 1) ∧ rb.cost ≤ 150 ∧ rb.need ≤ P.length + 100 ∧ rb.wk ≤ 1 := by
    by_cases hlt : Dm W k i k + Dm W k k j < Dm W k i j
    · have hlt' : (Dm W k i k : Int) + (Dm W k k j : Int) < (Dm W k i j : Int) := by omega
      rw [if_pos hlt'] at hcond
      have hDm1 : Dm W (k + 1) i j = Dm W k i k + Dm W k k j := by
        show min (Dm W k i j) (Dm W k i k + Dm W k k j) = _
        omega
      have e3' := idxD ([ci n, ci k, ci i] ++ [ci j] ++ [cs64 (Dm W k i k : Int)] ++ [cs64 (Dm W k k j : Int)] ++ [cs64 ((Dm W k i k : Int) + (Dm W k k j : Int))] ++ [cs64 (Dm W k i j : Int)]) 2 3 i (by omega) rfl hiM
      have e4' := idxD ([ci n, ci k, ci i] ++ [ci j] ++ [cs64 (Dm W k i k : Int)] ++ [cs64 (Dm W k k j : Int)] ++ [cs64 ((Dm W k i k : Int) + (Dm W k k j : Int))] ++ [cs64 (Dm W k i j : Int)]) 3 4 j (by omega) rfl hjM
      have w := pstmtM_writeRow_ok mv (gS P ([ci n, ci k, ci i] ++ [ci j] ++ [cs64 (Dm W k i k : Int)] ++ [cs64 (Dm W k k j : Int)] ++ [cs64 ((Dm W k i k : Int) + (Dm W k k j : Int))] ++ [cs64 (Dm W k i j : Int)])) vv 0 (by omega) hf0 hw0 (ixE 3) (ixE 4) (.variable s64 7)
        ((Dm W k i k : Int) + (Dm W k k j : Int)) i j rfl rfl rfl
        (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact e7)
        (by rw [vdenM_scalar _ _ _ _ rfl]; exact e3') (by rw [vdenM_scalar _ _ _ _ rfl]; exact e4')
        (by rw [hwr0]; exact hi) (by rw [hvv, FV_len W n k i j i hn32 hi]; exact hj) (by rw [hty0]; exact hsab)
      have hupd : upd vv (rowKey 0 i) ((vv (rowKey 0 i)).set j ((Dm W k i k : Int) + (Dm W k k j : Int))) =
          FV W n k i (j + 1) := by
        have := FV_upd W n k i j hn32 hi hj
        rw [hDm1, Nat.cast_add] at this
        exact this
      rw [hupd, hty0] at w
      have w1 := (pexecM_prim mv fu _ _ _).trans w
      have w2 := seqM_some w1 rfl (pexecM_skip mv fu _ _)
      have w3 := pexecM_scope mv fu _ _ _ _ w2
      have w4 := seqM_some w3 rfl (pexecM_skip mv fu _ _)
      have b1 := pexecM_branch_true mv fu condFW thenW Sk _ _ 1 hcond (by decide) _ w4
      have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
      refine ⟨_, b2, rfl, ?_, rfl, ?_, ?_, ?_⟩
      · simp
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
      · simp
    · have hlt' : ¬ ((Dm W k i k : Int) + (Dm W k k j : Int) < (Dm W k i j : Int)) := by omega
      rw [if_neg hlt'] at hcond
      have hDm1 : Dm W (k + 1) i j = Dm W k i j := by
        show min (Dm W k i j) (Dm W k i k + Dm W k k j) = _
        omega
      have b1 := pexecM_branch_false mv fu condFW thenW Sk _ _ hcond _ (pexecM_skip mv fu _ _)
      have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
      refine ⟨_, b2, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · exact (FV_same W n k i j hDm1).symm
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
      · simp
  have s4 := seqM_some q4 rfl hrb
  have s3 := seqM_some q3 rfl s4
  have s2 := seqM_some q2 rfl s3
  have s1 := seqM_some q1 rfl s2
  refine ⟨_, s1, by simp [hrbret], [cs64 (Dm W k i k : Int), cs64 (Dm W k k j : Int), cs64 ((Dm W k i k : Int) + (Dm W k k j : Int)), cs64 (Dm W k i j : Int)], ?_, hrbvv, ?_, ?_, ?_⟩
  · rw [hrbps]; simp
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at *; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at *; omega
  · simp at *; omega

def costL (c n : Nat) : Nat := (c + 20) * n + 30
def cI (n : Nat) : Nat := costL 200 n + 10
def cK (n : Nat) : Nat := costL (cI n) n + 10

theorem jloop_exec (mv : MV) (hnv : mv.nv = 1) (hf0 : mv.flat 0 = false) (hty0 : mv.ty 0 = s64) (hw0 : mv.wN 0 = true)
    (W : Nat → Nat → Nat) (n k i : Nat) (hwr0 : mv.wrows 0 = n) (fu : Nat) (P : List Cell) (hk : k < n) (hi : i < n)
    (hn : n + 1 < M31) (hW : ∀ p q, W p q < 4611686018427387904) (hfu : n + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (forStmtB mv.nv 3 0 bodyJ) (gS P [ci n, ci k, ci i]) (FV W n k i 0) = some res ∧
      res.ret = none ∧ res.ps = gS P [ci n, ci k, ci i] ∧ res.vv = FV W n k (i + 1) 0 ∧
      res.cost ≤ costL 200 n ∧ res.need ≤ P.length + 100 ∧ res.wk ≤ n := by
  have hn2 : n < 2147483647 := by have : n + 1 < 2147483648 := hn; omega
  have hnM : n < M31 := by show n < 2147483648; omega
  obtain ⟨res, C2, hr', hps, hC2, hI, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 3 0 n (by omega) hn2 bodyJ
    (fun j vv' C => vv' = FV W n k i j ∧ C = [ci n, ci k, ci i]) 200 100 1 0 (by omega)
    (by
      intro j vv' C fu' hj hCl hC1 hIv hfu'
      obtain ⟨hvvE, hCe⟩ := hIv
      subst hCe
      subst hvvE
      obtain ⟨r, hr, hret, cs', hps, hvv, hc, hn, hw⟩ := jbody_exec mv hnv hf0 hty0 hw0 W n k i j hwr0 fu' P hk hi hj
        hnM hW
      exact ⟨r, cs', [ci n, ci k, ci i], hr, hret, hps, rfl, rfl, ⟨hvv, rfl⟩, hc, hn, hw⟩)
    (FV W n k i 0) [ci n, ci k, ci i] rfl rfl ⟨rfl, rfl⟩ fu (by omega)
  obtain ⟨hvv, hCe⟩ := hI
  subst hCe
  rw [FV_rowend] at hvv
  refine ⟨res, hr', hret, hps, hvv, ?_, hnd, by omega⟩
  unfold costL; omega

theorem bodyI_exec (mv : MV) (hnv : mv.nv = 1) (hf0 : mv.flat 0 = false) (hty0 : mv.ty 0 = s64) (hw0 : mv.wN 0 = true)
    (W : Nat → Nat → Nat) (n k i : Nat) (hwr0 : mv.wrows 0 = n) (fu : Nat) (P : List Cell) (hk : k < n) (hi : i < n)
    (hn : n + 1 < M31) (hW : ∀ p q, W p q < 4611686018427387904) (hfu : n + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (bodyI mv.nv) (gS P ([ci n, ci k] ++ [ci i])) (FV W n k i 0) = some res ∧
      res.ret = none ∧ res.ps = gS P ([ci n, ci k] ++ [ci i]) ∧ res.vv = FV W n k (i + 1) 0 ∧
      res.cost ≤ cI n ∧ res.need ≤ P.length + 100 ∧ res.wk ≤ n := by
  obtain ⟨r, hr, hret, hps, hvv, hc, hn', hw⟩ := jloop_exec mv hnv hf0 hty0 hw0 W n k i hwr0 fu P hk hi hn hW hfu
  have q := seqM_some hr hret (pexecM_skip mv fu r.ps r.vv)
  rw [hps, hvv] at q
  refine ⟨_, q, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · show r.cost + 0 ≤ cI n
    unfold cI; omega
  · simp [gS_size]; omega
  · simp; omega

theorem iloop_exec (mv : MV) (hnv : mv.nv = 1) (hf0 : mv.flat 0 = false) (hty0 : mv.ty 0 = s64) (hw0 : mv.wN 0 = true)
    (W : Nat → Nat → Nat) (n k : Nat) (hwr0 : mv.wrows 0 = n) (fu : Nat) (P : List Cell) (hk : k < n)
    (hn : n + 1 < M31) (hW : ∀ p q, W p q < 4611686018427387904) (hfu : n + 1 + n + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (forStmtB mv.nv 2 0 (bodyI mv.nv)) (gS P [ci n, ci k]) (FV W n k 0 0) = some res ∧
      res.ret = none ∧ res.ps = gS P [ci n, ci k] ∧ res.vv = FV W n (k + 1) 0 0 ∧
      res.cost ≤ costL (cI n) n ∧ res.need ≤ P.length + 100 ∧ res.wk ≤ n * n := by
  have hn2 : n < 2147483647 := by have : n + 1 < 2147483648 := hn; omega
  have hnM : n < M31 := by show n < 2147483648; omega
  obtain ⟨res, C2, hr', hps, hC2, hI, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 2 0 n (by omega) hn2 (bodyI mv.nv)
    (fun i vv' C => vv' = FV W n k i 0 ∧ C = [ci n, ci k]) (cI n) 100 n (n + 1) (by omega)
    (by
      intro i vv' C fu' hi hCl hC1 hIv hfu'
      obtain ⟨hvvE, hCe⟩ := hIv
      subst hCe
      subst hvvE
      obtain ⟨r, hr, hret, hps, hvv, hc, hn', hw⟩ := bodyI_exec mv hnv hf0 hty0 hw0 W n k i hwr0 fu' P hk hi hn hW (by omega)
      exact ⟨r, [], [ci n, ci k], hr, hret, by rw [hps]; rfl, rfl, rfl, ⟨hvv, rfl⟩, hc, hn', hw⟩)
    (FV W n k 0 0) [ci n, ci k] rfl rfl ⟨rfl, rfl⟩ fu (by omega)
  obtain ⟨hvv, hCe⟩ := hI
  subst hCe
  rw [FV_roundend] at hvv
  exact ⟨res, hr', hret, hps, hvv, hc, hnd, hw⟩

theorem bodyK_exec (mv : MV) (hnv : mv.nv = 1) (hf0 : mv.flat 0 = false) (hty0 : mv.ty 0 = s64) (hw0 : mv.wN 0 = true)
    (W : Nat → Nat → Nat) (n k : Nat) (hwr0 : mv.wrows 0 = n) (fu : Nat) (P : List Cell) (hk : k < n)
    (hn : n + 1 < M31) (hW : ∀ p q, W p q < 4611686018427387904) (hfu : n + 1 + n + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (bodyK mv.nv) (gS P ([ci n] ++ [ci k])) (FV W n k 0 0) = some res ∧
      res.ret = none ∧ res.ps = gS P ([ci n] ++ [ci k]) ∧ res.vv = FV W n (k + 1) 0 0 ∧
      res.cost ≤ cK n ∧ res.need ≤ P.length + 100 ∧ res.wk ≤ n * n := by
  obtain ⟨r, hr, hret, hps, hvv, hc, hn', hw⟩ := iloop_exec mv hnv hf0 hty0 hw0 W n k hwr0 fu P hk hn hW hfu
  have q := seqM_some hr hret (pexecM_skip mv fu r.ps r.vv)
  rw [hps, hvv] at q
  refine ⟨_, q, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · show r.cost + 0 ≤ cK n
    unfold cK; omega
  · simp [gS_size]; omega
  · simp; omega

theorem nF_val (mv : MV) (hnv : mv.nv = 1) (hf0 : mv.flat 0 = false) (hty0 : mv.ty 0 = s64) (n : Nat)
    (hwr0 : mv.wrows 0 = n) (vv : Nat → List Int) (ps : PS) (hn : n < 2147483648) :
    vdenN mv vv (penvN mv.nv ps) nS = some (n : Int) := by
  have hsz : vdenN mv vv (penvN mv.nv ps) (.size (.vector (.integer s64)) (.local 0)) = some (n : Int) := by
    simp only [vdenN]
    rw [if_pos ⟨by omega, hf0, hty0.symm⟩, hwr0]
  have hcast : vdenN mv vv (penvN mv.nv ps) nS =
      (vdenN mv vv (penvN mv.nv ps) (.size (.vector (.integer s64)) (.local 0))).bind i32.convert := by
    simp only [Proofs.CumulativeSum2DExec.nS]; rw [vdenN]
  rw [hcast, hsz, Option.bind_some]
  exact conv_signed i32 rfl rfl _ (validN _ hn)

theorem prog_exec (mv : MV) (hnv : mv.nv = 1) (hf0 : mv.flat 0 = false) (hty0 : mv.ty 0 = s64) (hw0 : mv.wN 0 = true)
    (W : Nat → Nat → Nat) (n : Nat) (hwr0 : mv.wrows 0 = n) (fu : Nat) (P : List Cell) (hn : n + 1 < M31)
    (hW : ∀ p q, W p q < 4611686018427387904) (hfu : 3 * n + 3 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (progFW mv.nv) (gS P []) (FV W n 0 0 0) = some res ∧ res.ret = none ∧
      res.ps = gS P [ci n] ∧ res.vv = FV W n n 0 0 ∧ res.cost ≤ costL (cK n) n + 40 ∧
      res.need ≤ P.length + 100 ∧ res.wk ≤ n * n * n := by
  have hn2 : n < 2147483647 := by have : n + 1 < 2147483648 := hn; omega
  have d1 := gSM_decl mv P [] (FV W n 0 0 0) i32 nS (n : Int) (n : Int) (nF_val mv hnv hf0 hty0 n hwr0 _ _ (by omega))
    (conv_signed i32 rfl rfl _ (validN _ (by omega)))
  have q1 := (pexecM_prim mv fu _ _ _).trans d1
  have hq1 : ([] ++ [(⟨i32, (n : Int)⟩ : Cell)]) = [ci n] := rfl
  rw [hq1] at q1
  obtain ⟨res, C2, hr', hps, hC2, hI, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 1 0 n (by omega) hn2 (bodyK mv.nv)
    (fun k vv' C => vv' = FV W n k 0 0 ∧ C = [ci n]) (cK n) 100 (n * n) (2 * n + 2) (by omega)
    (by
      intro k vv' C fu' hk hCl hC1 hIv hfu'
      obtain ⟨hvvE, hCe⟩ := hIv
      subst hCe
      subst hvvE
      obtain ⟨r, hr, hret, hps, hvv, hc, hn', hw⟩ := bodyK_exec mv hnv hf0 hty0 hw0 W n k hwr0 fu' P hk hn hW (by omega)
      exact ⟨r, [], [ci n], hr, hret, by rw [hps]; rfl, rfl, rfl, ⟨hvv, rfl⟩, hc, hn', hw⟩)
    (FV W n 0 0 0) [ci n] rfl rfl ⟨rfl, rfl⟩ fu (by omega)
  obtain ⟨hvv, hCe⟩ := hI
  subst hCe
  have q2 := seqM_some hr' hret (pexecM_skip mv fu res.ps res.vv)
  rw [hps] at q2
  have q3 := seqM_some q1 rfl q2
  refine ⟨_, q3, rfl, rfl, hvv, ?_, ?_, ?_⟩
  · simp [vwp_nS]
    unfold costL
    omega
  · simp [vwp_nS, gS_size]
    omega
  · simp
    omega

end Proofs.FloydNestedExec
