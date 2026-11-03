import Proofs.MatMulExec
import Proofs.ForLoopB
import Proofs.BellmanFordExec

namespace Proofs.MatMulGen
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.MatMulExec (M64 cu term dsum u64v idx_lt u64_conv_nat step_lt n_small dsum_lt zero_u64 rowC matC rowC_length matC_length vec_getM)

/-! ### `mat_mul` inlined into a larger function: the cells `[n', i, j, s, k]` start at the cell `nb`, the vectors are the
slots `ia`, `ib`, `ic`. -/

abbrev mIdxG (nv nb x y : Nat) : NExpr :=
  .cast u64 (.binary i32 .add (.binary i32 .mul (.variable i32 (nv + x)) (.variable i32 (nv + nb))) (.variable i32 (nv + y)))
abbrev rdAG (nv nb ia : Nat) : NExpr := .read u64 (.local ia) (mIdxG nv nb (nb + 1) (nb + 4))
abbrev rdBG (nv nb ib : Nat) : NExpr := .read u64 (.local ib) (mIdxG nv nb (nb + 4) (nb + 2))
abbrev accSG (nv nb ia ib : Nat) : NStmt :=
  .assign (nv + (nb + 3)) u64 (.binary u64 .add (.variable u64 (nv + (nb + 3))) (.binary u64 .mul (rdAG nv nb ia) (rdBG nv nb ib)))
abbrev BkG (nv nb ia ib : Nat) : Command := .sequence (.primitive (accSG nv nb ia ib)) (.primitive .skip)
abbrev declSG : NStmt := .declare u64 true (.cast u64 (.literal i32 0))
abbrev wrSG (nv nb ic : Nat) : NStmt :=
  .write (.local ic) u64 (mIdxG nv nb (nb + 1) (nb + 2)) (.variable u64 (nv + (nb + 3)))
abbrev BjG (nv nb ia ib ic : Nat) : Command :=
  .sequence (.primitive declSG) (.sequence (forStmtB nv (nb + 4) nb (BkG nv nb ia ib))
    (.sequence (.primitive (wrSG nv nb ic)) (.primitive .skip)))
abbrev BiG (nv nb ia ib ic : Nat) : Command :=
  .sequence (forStmtB nv (nb + 2) nb (BjG nv nb ia ib ic)) (.primitive .skip)

theorem getq (C0 L : List Cell) (nb c : Nat) (h : C0.length = nb) : (C0 ++ L)[nb + c]? = L[c]? := by
  subst h
  rw [List.getElem?_append_right (by omega)]
  simp

theorem mIdxG_den (env : Nat → Ty → Option Int) (nv nb x y na nbb n : Nat) (h1 : env (nv + nb) i32 = some (n : Int))
    (ha : env (nv + x) i32 = some (na : Int)) (hb : env (nv + y) i32 = some (nbb : Int)) (hlt : na * n + nbb < 2147483648) :
    (mIdxG nv nb x y).denote env = some ((na * n + nbb : Nat) : Int) := by
  have hm : na * n < 2147483648 := by omega
  rw [den_cast, den_binary, den_binary, den_variable, ha, Option.bind_some, den_variable, h1, Option.bind_some]
  have e1 : binaryValue .mul (na : Int) (n : Int) = ((na * n : Nat) : Int) := by
    show (na : Int) * (n : Int) = _; push_cast; rfl
  rw [e1, conv_signed i32 rfl rfl _ (validN _ hm), Option.bind_some, den_variable, hb, Option.bind_some]
  have e2 : binaryValue .add ((na * n : Nat) : Int) (nbb : Int) = ((na * n + nbb : Nat) : Int) := by
    show ((na * n : Nat) : Int) + (nbb : Int) = _; push_cast; rfl
  rw [e2, conv_signed i32 rfl rfl _ (validN _ hlt), Option.bind_some, convert_u64]
  congr 1
  exact Int.emod_eq_of_lt (by omega) (by omega)

/-- The environment of the cells `[n, i, j, s, k]` placed after `C0`. -/
theorem envKG (mv : MV) (P C0 : List Cell) (nb : Nat) (hC : C0.length = nb) (n i j s k : Nat) (hn : n < 2147483648)
    (hi : i < 2147483648) (hj : j < 2147483648) (hs : s < M64) (hk : k < 2147483648) :
    penvN mv.nv (gS P (C0 ++ [ci n, ci i, ci j, cu s, ci k])) (mv.nv + nb) i32 = some (n : Int) ∧
    penvN mv.nv (gS P (C0 ++ [ci n, ci i, ci j, cu s, ci k])) (mv.nv + (nb + 1)) i32 = some (i : Int) ∧
    penvN mv.nv (gS P (C0 ++ [ci n, ci i, ci j, cu s, ci k])) (mv.nv + (nb + 2)) i32 = some (j : Int) ∧
    penvN mv.nv (gS P (C0 ++ [ci n, ci i, ci j, cu s, ci k])) (mv.nv + (nb + 3)) u64 = some (s : Int) ∧
    penvN mv.nv (gS P (C0 ++ [ci n, ci i, ci j, cu s, ci k])) (mv.nv + (nb + 4)) i32 = some (k : Int) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact gSM_env mv.nv P _ nb (ci n) (by have := getq C0 [ci n, ci i, ci j, cu s, ci k] nb 0 hC; simpa using this) (validN n hn)
  · exact gSM_env mv.nv P _ (nb + 1) (ci i) (by have := getq C0 [ci n, ci i, ci j, cu s, ci k] nb 1 hC; simpa using this) (validN i hi)
  · exact gSM_env mv.nv P _ (nb + 2) (ci j) (by have := getq C0 [ci n, ci i, ci j, cu s, ci k] nb 2 hC; simpa using this) (validN j hj)
  · exact gSM_env mv.nv P _ (nb + 3) (cu s) (by have := getq C0 [ci n, ci i, ci j, cu s, ci k] nb 3 hC; simpa using this) (u64v s hs)
  · exact gSM_env mv.nv P _ (nb + 4) (ci k) (by have := getq C0 [ci n, ci i, ci j, cu s, ci k] nb 4 hC; simpa using this) (validN k hk)

theorem mulEG_val (mv : MV) (hty : ∀ k, mv.ty k = u64) (vv : Nat → List Int) (ia ib : Nat) (hia : ia < mv.nv) (hib : ib < mv.nv)
    (a b : List Nat) (hva : vv ia = a.map (fun x : Nat => (x : Int))) (hvb : vv ib = b.map (fun x : Nat => (x : Int)))
    (haM : ∀ x ∈ a, x < M64) (hbM : ∀ x ∈ b, x < M64) (P C0 : List Cell) (nb : Nat) (hC : C0.length = nb)
    (n i j s k : Nat) (hi : i < n) (hj : j < n) (hk : k < n) (hnn : n * n < 2147483648) (hla : a.length = n * n)
    (hlb : b.length = n * n) (hs : s < M64) :
    vdenM mv vv (penvN mv.nv (gS P (C0 ++ [ci n, ci i, ci j, cu s, ci k])))
      (.binary u64 .add (.variable u64 (mv.nv + (nb + 3))) (.binary u64 .mul (rdAG mv.nv nb ia) (rdBG mv.nv nb ib))) =
      some (((s + term a b n i j k % M64) % M64 : Nat) : Int) := by
  have hn32 : n < 2147483648 := by
    have : n ≤ n * n := Nat.le_mul_self n
    omega
  obtain ⟨E0, E1, E2, E3, E4⟩ := envKG mv P C0 nb hC n i j s k hn32 (by omega) (by omega) hs (by omega)
  have l1 := idx_lt n i k hi hk
  have l2 := idx_lt n k j hk hj
  have ga : ∀ idx, idx < n * n → a.getD idx 0 < M64 := by
    intro idx hidx
    have : a.getD idx 0 = a[idx]'(by omega) := by simp [List.getD_eq_getElem?_getD, hla, hidx]
    rw [this]; exact haM _ (List.getElem_mem _)
  have gb : ∀ idx, idx < n * n → b.getD idx 0 < M64 := by
    intro idx hidx
    have : b.getD idx 0 = b[idx]'(by omega) := by simp [List.getD_eq_getElem?_getD, hlb, hidx]
    rw [this]; exact hbM _ (List.getElem_mem _)
  have dA := mIdxG_den (penvN mv.nv (gS P (C0 ++ [ci n, ci i, ci j, cu s, ci k]))) mv.nv nb (nb + 1) (nb + 4) i k n E0 E1 E4 (by omega)
  have dB := mIdxG_den (penvN mv.nv (gS P (C0 ++ [ci n, ci i, ci j, cu s, ci k]))) mv.nv nb (nb + 4) (nb + 2) k j n E0 E4 E2 (by omega)
  have rA := Proofs.MatMulExec.rdM_val mv vv (penvN mv.nv (gS P (C0 ++ [ci n, ci i, ci j, cu s, ci k]))) ia hia u64 (hty ia).symm
    (mIdxG mv.nv nb (nb + 1) (nb + 4)) rfl rfl (i * n + k) dA (a.getD (i * n + k) 0) (by rw [hva]; exact vec_getM a _ (by omega))
    (by rw [hty]; exact u64v _ (ga _ l1))
  have rB := Proofs.MatMulExec.rdM_val mv vv (penvN mv.nv (gS P (C0 ++ [ci n, ci i, ci j, cu s, ci k]))) ib hib u64 (hty ib).symm
    (mIdxG mv.nv nb (nb + 4) (nb + 2)) rfl rfl (k * n + j) dB (b.getD (k * n + j) 0) (by rw [hvb]; exact vec_getM b _ (by omega))
    (by rw [hty]; exact u64v _ (gb _ l2))
  have hmul : vdenM mv vv (penvN mv.nv (gS P (C0 ++ [ci n, ci i, ci j, cu s, ci k])))
      (.binary u64 .mul (rdAG mv.nv nb ia) (rdBG mv.nv nb ib)) = some ((term a b n i j k % M64 : Nat) : Int) := by
    have hb : (NExpr.binary u64 .mul (rdAG mv.nv nb ia) (rdBG mv.nv nb ib)).scalarOnly = false := rfl
    rw [Proofs.MatMulExec.vdenM_binary _ _ _ _ _ _ _ hb, rA, rB, Option.bind_some, Option.bind_some]
    have : binaryValue .mul ((a.getD (i * n + k) 0 : Nat) : Int) ((b.getD (k * n + j) 0 : Nat) : Int) =
        ((term a b n i j k : Nat) : Int) := by
      show _ * _ = _; unfold term; push_cast; rfl
    rw [this, convert_u64]
    congr 1
  have hb : (NExpr.binary u64 .add (.variable u64 (mv.nv + (nb + 3))) (.binary u64 .mul (rdAG mv.nv nb ia) (rdBG mv.nv nb ib))).scalarOnly = false := rfl
  have hv : vdenM mv vv (penvN mv.nv (gS P (C0 ++ [ci n, ci i, ci j, cu s, ci k]))) (NExpr.variable u64 (mv.nv + (nb + 3))) =
      some (s : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E3
  rw [Proofs.MatMulExec.vdenM_binary _ _ _ _ _ _ _ hb, hv, hmul, Option.bind_some, Option.bind_some]
  have : binaryValue .add (s : Int) ((term a b n i j k % M64 : Nat) : Int) = ((s + term a b n i j k % M64 : Nat) : Int) := by
    show (s : Int) + _ = _; push_cast; rfl
  rw [this, convert_u64]
  congr 1

/-- One iteration of the innermost loop: `s += a[i*n+k] * b[k*n+j]`. -/
theorem k_bodyG (mv : MV) (hty : ∀ k, mv.ty k = u64) (vv : Nat → List Int) (ia ib : Nat) (hia : ia < mv.nv) (hib : ib < mv.nv)
    (a b : List Nat) (hva : vv ia = a.map (fun x : Nat => (x : Int))) (hvb : vv ib = b.map (fun x : Nat => (x : Int)))
    (haM : ∀ x ∈ a, x < M64) (hbM : ∀ x ∈ b, x < M64) (P C0 : List Cell) (nb : Nat) (hC : C0.length = nb)
    (n i j s k : Nat) (hi : i < n) (hj : j < n) (hk : k < n) (hnn : n * n < 2147483648) (hla : a.length = n * n)
    (hlb : b.length = n * n) (hs : s < M64) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (BkG mv.nv nb ia ib) (gS P (C0 ++ [ci n, ci i, ci j, cu s] ++ [ci k])) vv = some r ∧ r.ret = none ∧
      r.ps = gS P (C0 ++ [ci n, ci i, ci j, cu ((s + term a b n i j k % M64) % M64)] ++ [ci k]) ∧ r.vv = vv ∧
      r.cost ≤ 400 ∧ r.need ≤ P.length + 2 * nb + 100 ∧ r.wk = 0 := by
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hv := mulEG_val mv hty vv ia ib hia hib a b hva hvb haM hbM P C0 nb hC n i j s k hi hj hk hnn hla hlb hs
  have asg := gSM_assign mv P (C0 ++ [ci n, ci i, ci j, cu s, ci k]) vv (nb + 3) (by simp [hC]) u64 _ _ _ hv (cu s)
    (by have := getq C0 [ci n, ci i, ci j, cu s, ci k] nb 3 hC; simpa using this) rfl (u64v s hs)
    (u64_conv_nat _ (step_lt s _ hs))
  have q1 := (pexecM_prim mv fu (accSG mv.nv nb ia ib) _ _).trans asg
  have q2 := seqM_some q1 rfl (pexecM_skip mv fu _ _)
  have hset : (C0 ++ [ci n, ci i, ci j, cu s, ci k]).set (nb + 3) ⟨u64, (((s + term a b n i j k % M64) % M64 : Nat) : Int)⟩ =
      C0 ++ [ci n, ci i, ci j, cu ((s + term a b n i j k % M64) % M64), ci k] := by
    rw [List.set_append_right _ _ (by omega)]
    simp [hC, List.set_cons_succ]
  refine ⟨_, q2, rfl, ?_, rfl, ?_, ?_, rfl⟩
  · show gS P ((C0 ++ [ci n, ci i, ci j, cu s, ci k]).set (nb + 3) ⟨u64, (((s + term a b n i j k % M64) % M64 : Nat) : Int)⟩) = _
    rw [hset]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, hC]; omega

theorem k_loopG (mv : MV) (hty : ∀ k, mv.ty k = u64) (vv : Nat → List Int) (ia ib : Nat) (hia : ia < mv.nv) (hib : ib < mv.nv)
    (a b : List Nat) (hva : vv ia = a.map (fun x : Nat => (x : Int))) (hvb : vv ib = b.map (fun x : Nat => (x : Int)))
    (haM : ∀ x ∈ a, x < M64) (hbM : ∀ x ∈ b, x < M64) (P C0 : List Cell) (nb : Nat) (hC : C0.length = nb)
    (n i j : Nat) (hi : i < n) (hj : j < n) (hnn : n * n < 2147483648) (hla : a.length = n * n) (hlb : b.length = n * n)
    (fu : Nat) (hfu : n + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (forStmtB mv.nv (nb + 4) nb (BkG mv.nv nb ia ib)) (gS P (C0 ++ [ci n, ci i, ci j, cu 0])) vv = some res ∧
      res.ps = gS P (C0 ++ [ci n, ci i, ci j, cu (dsum a b n i j n % M64)]) ∧ res.vv = vv ∧ res.ret = none ∧
      res.cost ≤ 420 * n + 30 ∧ res.need ≤ P.length + 2 * nb + 100 ∧ res.wk = 0 := by
  have hn32 : n < 2147483647 := n_small n hnn
  obtain ⟨res, C2, hr, hps, hC2, hI, hret, hc, hnd, hw⟩ := for_stmt_runB mv P (nb + 4) nb n (by omega) hn32 (BkG mv.nv nb ia ib)
    (fun t vv' C => vv' = vv ∧ C = C0 ++ [ci n, ci i, ci j, cu (dsum a b n i j t % M64)]) 400 (2 * nb + 100) 0 0 (by omega)
    (by
      intro t vv' C fu ht hCl hC0 ⟨hvv, hC'⟩ _
      subst hvv; subst hC'
      have hk := k_bodyG mv hty vv' ia ib hia hib a b hva hvb haM hbM P C0 nb hC n i j (dsum a b n i j t % M64) t hi hj ht hnn hla hlb
        (dsum_lt a b n i j t) fu
      obtain ⟨r, hr, hret, hps, hvv, hc, hnd, hwk⟩ := hk
      refine ⟨r, [], C0 ++ [ci n, ci i, ci j, cu ((dsum a b n i j t % M64 + term a b n i j t % M64) % M64)], hr, hret, ?_, ?_, ?_, ?_, hc, hnd, ?_⟩
      · simpa using hps
      · simp [hC]
      · have := getq C0 [ci n, ci i, ci j, cu ((dsum a b n i j t % M64 + term a b n i j t % M64) % M64)] nb 0 hC
        simpa using this
      · refine ⟨hvv, ?_⟩
        show _ = C0 ++ [ci n, ci i, ci j, cu ((dsum a b n i j t + term a b n i j t) % M64)]
        rw [← Nat.add_mod]
      · omega)
    vv (C0 ++ [ci n, ci i, ci j, cu 0]) (by simp [hC]) (by have := getq C0 [ci n, ci i, ci j, cu 0] nb 0 hC; simpa using this)
    ⟨rfl, by simp [dsum]⟩ fu (by omega)
  obtain ⟨hvv, hC'⟩ := hI
  subst hC'
  refine ⟨res, hr, hps, hvv, hret, ?_, hnd, ?_⟩
  · omega
  · omega

theorem envWG (mv : MV) (P C0 : List Cell) (nb : Nat) (hC : C0.length = nb) (n i j s : Nat) (hn : n < 2147483648)
    (hi : i < 2147483648) (hj : j < 2147483648) (hs : s < M64) :
    penvN mv.nv (gS P (C0 ++ [ci n, ci i, ci j, cu s])) (mv.nv + nb) i32 = some (n : Int) ∧
    penvN mv.nv (gS P (C0 ++ [ci n, ci i, ci j, cu s])) (mv.nv + (nb + 1)) i32 = some (i : Int) ∧
    penvN mv.nv (gS P (C0 ++ [ci n, ci i, ci j, cu s])) (mv.nv + (nb + 2)) i32 = some (j : Int) ∧
    penvN mv.nv (gS P (C0 ++ [ci n, ci i, ci j, cu s])) (mv.nv + (nb + 3)) u64 = some (s : Int) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact gSM_env mv.nv P _ nb (ci n) (by have := getq C0 [ci n, ci i, ci j, cu s] nb 0 hC; simpa using this) (validN n hn)
  · exact gSM_env mv.nv P _ (nb + 1) (ci i) (by have := getq C0 [ci n, ci i, ci j, cu s] nb 1 hC; simpa using this) (validN i hi)
  · exact gSM_env mv.nv P _ (nb + 2) (ci j) (by have := getq C0 [ci n, ci i, ci j, cu s] nb 2 hC; simpa using this) (validN j hj)
  · exact gSM_env mv.nv P _ (nb + 3) (cu s) (by have := getq C0 [ci n, ci i, ci j, cu s] nb 3 hC; simpa using this) (u64v s hs)

theorem upd_upd_same {α : Type} (f : Nat → α) (k : Nat) (x y : α) : upd (upd f k x) k y = upd f k y := by
  funext j; unfold upd; split <;> rfl

/-- One iteration of the middle loop: `c[i*n+j] = sum_k a[i*n+k] * b[k*n+j]`. -/
theorem j_bodyG (mv : MV) (hty : ∀ k, mv.ty k = u64) (vv : Nat → List Int) (ia ib ic : Nat) (hia : ia < mv.nv)
    (hib : ib < mv.nv) (hic : ic < mv.nv) (a b c : List Nat)
    (hva : vv ia = a.map (fun x : Nat => (x : Int))) (hvb : vv ib = b.map (fun x : Nat => (x : Int)))
    (hvc : vv ic = c.map (fun x : Nat => (x : Int))) (haM : ∀ x ∈ a, x < M64) (hbM : ∀ x ∈ b, x < M64)
    (P C0 : List Cell) (nb : Nat) (hC : C0.length = nb) (n i j : Nat) (hi : i < n) (hj : j < n)
    (hnn : n * n < 2147483648) (hla : a.length = n * n) (hlb : b.length = n * n) (hlc : c.length = n * n)
    (fu : Nat) (hfu : n + 1 ≤ fu) :
    ∃ r : PRM, pexecM mv fu (BjG mv.nv nb ia ib ic) (gS P (C0 ++ [ci n, ci i] ++ [ci j])) vv = some r ∧ r.ret = none ∧
      r.ps = gS P (C0 ++ [ci n, ci i] ++ [ci j] ++ [cu (dsum a b n i j n % M64)]) ∧
      r.vv = upd vv ic ((c.set (i * n + j) (dsum a b n i j n % M64)).map (fun x : Nat => (x : Int))) ∧
      r.cost ≤ 420 * n + 200 ∧ r.need ≤ P.length + 2 * nb + 100 ∧ r.wk = 1 := by
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hn32 : n < 2147483647 := n_small n hnn
  have d := gSM_decl mv P (C0 ++ [ci n, ci i, ci j]) vv u64 _ 0 0 (zero_u64 mv _ _) (u64_conv_nat 0 (by decide))
  have q1 := (pexecM_prim mv fu declSG _ _).trans d
  have e1 : C0 ++ [ci n, ci i, ci j] ++ [(⟨u64, 0⟩ : Cell)] = C0 ++ [ci n, ci i, ci j, cu 0] := by simp [cu]
  rw [e1] at q1
  obtain ⟨⟨kps, kvv, kret, kcost, kneed, kwk⟩, hkr, hkps, hkvv, hkret, hkc, hknd, hkwk⟩ :=
    k_loopG mv hty vv ia ib hia hib a b hva hvb haM hbM P C0 nb hC n i j hi hj hnn hla hlb fu hfu
  simp only at hkps hkvv hkret hkc hknd hkwk
  subst kps kvv kret kwk
  obtain ⟨E0, E1, E2, E3⟩ := envWG mv P C0 nb hC n i j (dsum a b n i j n % M64) (by omega) (by omega) (by omega) (dsum_lt a b n i j n)
  have hx : vdenM mv vv (penvN mv.nv (gS P (C0 ++ [ci n, ci i, ci j, cu (dsum a b n i j n % M64)])))
      (NExpr.variable u64 (mv.nv + (nb + 3))) = some ((dsum a b n i j n % M64 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E3
  have hp : vdenM mv vv (penvN mv.nv (gS P (C0 ++ [ci n, ci i, ci j, cu (dsum a b n i j n % M64)])))
      (mIdxG mv.nv nb (nb + 1) (nb + 2)) = some ((i * n + j : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    exact mIdxG_den _ mv.nv nb (nb + 1) (nb + 2) i j n E0 E1 E2 (by have := idx_lt n i j hi hj; omega)
  have w := pstmtM_write_ok mv (gS P (C0 ++ [ci n, ci i, ci j, cu (dsum a b n i j n % M64)])) vv ic hic
    (mIdxG mv.nv nb (nb + 1) (nb + 2)) (.variable u64 (mv.nv + (nb + 3))) _ (i * n + j) hx hp
    (by rw [hvc]; simp [hlc]; exact idx_lt n i j hi hj) (by rw [hty]; exact u64v _ (dsum_lt a b n i j n))
  rw [hty ic] at w
  have a1 := (pexecM_prim mv fu (wrSG mv.nv nb ic) _ _).trans w
  have a2 := seqM_some a1 rfl (pexecM_skip mv fu (gS P (C0 ++ [ci n, ci i, ci j, cu (dsum a b n i j n % M64)]))
    (upd vv ic ((vv ic).set (i * n + j) ((dsum a b n i j n % M64 : Nat) : Int))))
  have b1 := seqM_some hkr rfl a2
  have b2 := seqM_some q1 rfl b1
  refine ⟨_, b2, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [List.append_assoc]
  · rw [hvc, List.map_set]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at *
    omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, hC] at *
    omega
  · simp

theorem j_loopG (mv : MV) (hty : ∀ k, mv.ty k = u64) (vv : Nat → List Int) (ia ib ic : Nat) (hia : ia < mv.nv)
    (hib : ib < mv.nv) (hic : ic < mv.nv) (hca : ic ≠ ia) (hcb : ic ≠ ib) (a b c : List Nat)
    (hva : vv ia = a.map (fun x : Nat => (x : Int))) (hvb : vv ib = b.map (fun x : Nat => (x : Int)))
    (hvc : vv ic = c.map (fun x : Nat => (x : Int))) (haM : ∀ x ∈ a, x < M64) (hbM : ∀ x ∈ b, x < M64)
    (P C0 : List Cell) (nb : Nat) (hC : C0.length = nb) (n i : Nat) (hi : i < n)
    (hnn : n * n < 2147483648) (hla : a.length = n * n) (hlb : b.length = n * n) (hlc : c.length = n * n)
    (fu : Nat) (hfu : 2 * n + 2 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (forStmtB mv.nv (nb + 2) nb (BjG mv.nv nb ia ib ic)) (gS P (C0 ++ [ci n, ci i])) vv = some res ∧
      res.ps = gS P (C0 ++ [ci n, ci i]) ∧ res.vv = upd vv ic ((rowC a b n i c n).map (fun x : Nat => (x : Int))) ∧
      res.ret = none ∧ res.cost ≤ (420 * n + 220) * n + 30 ∧ res.need ≤ P.length + 2 * nb + 100 ∧ res.wk ≤ n := by
  have hn32 : n < 2147483647 := n_small n hnn
  obtain ⟨res, C2, hr, hps, hC2, hI, hret, hc, hnd, hw⟩ := for_stmt_runB mv P (nb + 2) nb n (by omega) hn32 (BjG mv.nv nb ia ib ic)
    (fun t vv' C => vv' = upd vv ic ((rowC a b n i c t).map (fun x : Nat => (x : Int))) ∧ C = C0 ++ [ci n, ci i])
    (420 * n + 200) (2 * nb + 100) 1 (n + 1) (by omega)
    (by
      intro t vv' C fu ht hCl hC0 ⟨hvv, hC'⟩ hfu'
      subst hvv; subst hC'
      have hk := j_bodyG mv hty (upd vv ic ((rowC a b n i c t).map (fun x : Nat => (x : Int)))) ia ib ic hia hib hic a b (rowC a b n i c t)
        (by rw [upd_other _ _ _ _ (Ne.symm hca)]; exact hva) (by rw [upd_other _ _ _ _ (Ne.symm hcb)]; exact hvb)
        (by rw [upd_self]) haM hbM P C0 nb hC n i t hi ht hnn hla hlb (by rw [rowC_length]; exact hlc) fu hfu'
      obtain ⟨r, hr, hret, hps, hvv, hc, hnd, hwk⟩ := hk
      refine ⟨r, [cu (dsum a b n i t n % M64)], C0 ++ [ci n, ci i], hr, hret, ?_, ?_, ?_, ⟨?_, rfl⟩, hc, hnd, by omega⟩
      · simpa using hps
      · simp [hC]
      · have := getq C0 [ci n, ci i] nb 0 hC
        simpa using this
      · rw [hvv, upd_upd_same]; rfl)
    vv (C0 ++ [ci n, ci i]) (by simp [hC]) (by have := getq C0 [ci n, ci i] nb 0 hC; simpa using this)
    ⟨by funext k; unfold upd; split <;> simp_all [rowC], rfl⟩ fu (by omega)
  obtain ⟨hvv, hC'⟩ := hI
  subst hC'
  exact ⟨res, hr, hps, hvv, hret, by omega, hnd, by omega⟩

def cjG (n : Nat) : Nat := (420 * n + 220) * n + 30
def cIG (n : Nat) : Nat := (cjG n + 20) * n + 30

theorem i_bodyG (mv : MV) (hty : ∀ k, mv.ty k = u64) (vv : Nat → List Int) (ia ib ic : Nat) (hia : ia < mv.nv)
    (hib : ib < mv.nv) (hic : ic < mv.nv) (hca : ic ≠ ia) (hcb : ic ≠ ib) (a b c : List Nat)
    (hva : vv ia = a.map (fun x : Nat => (x : Int))) (hvb : vv ib = b.map (fun x : Nat => (x : Int)))
    (hvc : vv ic = c.map (fun x : Nat => (x : Int))) (haM : ∀ x ∈ a, x < M64) (hbM : ∀ x ∈ b, x < M64)
    (P C0 : List Cell) (nb : Nat) (hC : C0.length = nb) (n i : Nat) (hi : i < n)
    (hnn : n * n < 2147483648) (hla : a.length = n * n) (hlb : b.length = n * n) (hlc : c.length = n * n)
    (fu : Nat) (hfu : 2 * n + 2 ≤ fu) :
    ∃ r : PRM, pexecM mv fu (BiG mv.nv nb ia ib ic) (gS P (C0 ++ [ci n] ++ [ci i])) vv = some r ∧ r.ret = none ∧
      r.ps = gS P (C0 ++ [ci n] ++ [ci i] ++ []) ∧ r.vv = upd vv ic ((rowC a b n i c n).map (fun x : Nat => (x : Int))) ∧
      r.cost ≤ cjG n ∧ r.need ≤ P.length + 2 * nb + 100 ∧ r.wk ≤ n := by
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  obtain ⟨⟨jps, jvv, jret, jcost, jneed, jwk⟩, hj, hps, hvv, hret, hc, hnd, hw⟩ :=
    j_loopG mv hty vv ia ib ic hia hib hic hca hcb a b c hva hvb hvc haM hbM P C0 nb hC n i hi hnn hla hlb hlc fu hfu
  simp only at hps hvv hret hc hnd hw
  subst hps hvv hret
  have b1 := seqM_some hj rfl (pexecM_skip mv fu (gS P (C0 ++ [ci n, ci i])) (upd vv ic ((rowC a b n i c n).map (fun x : Nat => (x : Int)))))
  refine ⟨_, b1, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simpa [cjG] using hc
  · simp [gS_size]; omega
  · simpa using hw

theorem i_loopG (mv : MV) (hty : ∀ k, mv.ty k = u64) (vv : Nat → List Int) (ia ib ic : Nat) (hia : ia < mv.nv)
    (hib : ib < mv.nv) (hic : ic < mv.nv) (hca : ic ≠ ia) (hcb : ic ≠ ib) (a b c : List Nat)
    (hva : vv ia = a.map (fun x : Nat => (x : Int))) (hvb : vv ib = b.map (fun x : Nat => (x : Int)))
    (hvc : vv ic = c.map (fun x : Nat => (x : Int))) (haM : ∀ x ∈ a, x < M64) (hbM : ∀ x ∈ b, x < M64)
    (P C0 : List Cell) (nb : Nat) (hC : C0.length = nb) (n : Nat)
    (hnn : n * n < 2147483648) (hla : a.length = n * n) (hlb : b.length = n * n) (hlc : c.length = n * n)
    (fu : Nat) (hfu : 3 * n + 4 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (forStmtB mv.nv (nb + 1) nb (BiG mv.nv nb ia ib ic)) (gS P (C0 ++ [ci n])) vv = some res ∧
      res.ps = gS P (C0 ++ [ci n]) ∧ res.vv = upd vv ic ((matC a b n c n).map (fun x : Nat => (x : Int))) ∧ res.ret = none ∧
      res.cost ≤ cIG n ∧ res.need ≤ P.length + 2 * nb + 100 ∧ res.wk ≤ n * n := by
  have hn32 : n < 2147483647 := n_small n hnn
  obtain ⟨res, C2, hr, hps, hC2, hI, hret, hc, hnd, hw⟩ := for_stmt_runB mv P (nb + 1) nb n (by omega) hn32 (BiG mv.nv nb ia ib ic)
    (fun t vv' C => vv' = upd vv ic ((matC a b n c t).map (fun x : Nat => (x : Int))) ∧ C = C0 ++ [ci n])
    (cjG n) (2 * nb + 100) n (2 * n + 2) (by omega)
    (by
      intro t vv' C fu ht hCl hC0 ⟨hvv, hC'⟩ hfu'
      subst hvv; subst hC'
      have hk := i_bodyG mv hty (upd vv ic ((matC a b n c t).map (fun x : Nat => (x : Int)))) ia ib ic hia hib hic hca hcb a b (matC a b n c t)
        (by rw [upd_other _ _ _ _ (Ne.symm hca)]; exact hva) (by rw [upd_other _ _ _ _ (Ne.symm hcb)]; exact hvb)
        (by rw [upd_self]) haM hbM P C0 nb hC n t ht hnn hla hlb (by rw [matC_length]; exact hlc) fu hfu'
      obtain ⟨r, hr, hret, hps, hvv, hc, hnd, hwk⟩ := hk
      refine ⟨r, [], C0 ++ [ci n], hr, hret, ?_, ?_, ?_, ⟨?_, rfl⟩, hc, hnd, hwk⟩
      · simpa using hps
      · simp [hC]
      · have := getq C0 [ci n] nb 0 hC
        simpa using this
      · rw [hvv, upd_upd_same]; rfl)
    vv (C0 ++ [ci n]) (by simp [hC]) (by have := getq C0 [ci n] nb 0 hC; simpa using this)
    ⟨by funext k; unfold upd; split <;> simp_all [matC], rfl⟩ fu (by omega)
  obtain ⟨hvv, hC'⟩ := hI
  subst hC'
  exact ⟨res, hr, hps, hvv, hret, hc, hnd, hw⟩

end Proofs.MatMulGen





