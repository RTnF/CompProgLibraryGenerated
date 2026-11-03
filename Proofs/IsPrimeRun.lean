import Proofs.IsPrimeTop

namespace Proofs.IsPrimeRun
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.BellmanFordExec (envs pexecM_branch_true pexecM_branch_false lt_conv ne_conv)
open Proofs.IsPrimeBody Proofs.IsPrimeExec Proofs.IsPrimeWit Proofs.IsPrimeTop

/-- The tail of the inlined `mr_witness`: copy the result twice and clear `result` when it is a witness. -/
theorem witR_exec (mv : MV) (P cl : List Cell) (W f : Bool) (vv : Nat → List Int) (fu : Nat)
    (hl : cl.length = 22) (h13 : cl[13]? = some (cb W)) (h1 : cl[1]? = some (cb f)) :
    ∃ res : PRM, pexecM mv fu (witR mv.nv) (gS P cl) vv = some res ∧ res.ret = none ∧
      res.ps = gS P ((if W then cl.set 1 (cb false) else cl) ++ [cb W, cb W]) ∧ res.vv = vv ∧
      res.cost ≤ 100 ∧ res.need ≤ P.length + 2 * 22 + 100 ∧ res.wk = 0 := by
  have v1 := varb_den mv P cl 13 W h13
  have d1 := gSM_decl mv P cl vv bT (bV mv.nv 13) (if W then 1 else 0) (if W then 1 else 0)
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact v1) (by cases W <;> rfl)
  have a1 := (pexecM_prim mv fu (.declare bT true (bV mv.nv 13)) _ _).trans d1
  have h13' : (cl ++ [cb W])[13]? = some (cb W) := by
    rw [List.getElem?_append_left (by simp [hl])]; exact h13
  have h22 : (cl ++ [cb W])[22]? = some (cb W) := by simp [List.getElem?_append_right, hl]
  have v2 := varb_den mv P (cl ++ [cb W]) 22 W h22
  have d2 := gSM_decl mv P (cl ++ [cb W]) vv bT (bV mv.nv 22) (if W then 1 else 0) (if W then 1 else 0)
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact v2) (by cases W <;> rfl)
  have a2 := (pexecM_prim mv fu (.declare bT true (bV mv.nv 22)) _ _).trans d2
  have h23 : (cl ++ [cb W] ++ [cb W])[23]? = some (cb W) := by simp [List.getElem?_append_right, hl]
  have v3 := varb_den mv P (cl ++ [cb W] ++ [cb W]) 23 W h23
  have hcv : vdenM mv vv (penvN mv.nv (gS P (cl ++ [cb W] ++ [cb W]))) (bV mv.nv 23) = some (if W then 1 else 0) := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact v3
  have hlen2 : (cl ++ [cb W] ++ [cb W]).length = 24 := by simp [hl]
  have br : ∃ rb : PRM, pexecM mv fu (.sequence (.branch (bV mv.nv 23) (assign1 mv.nv 0) Sk) Sk)
      (gS P (cl ++ [cb W] ++ [cb W])) vv = some rb ∧ rb.ret = none ∧
      rb.ps = gS P ((if W then cl.set 1 (cb false) else cl) ++ [cb W, cb W]) ∧ rb.vv = vv ∧ rb.cost ≤ 60 ∧
      rb.need ≤ P.length + 2 * 24 + 60 ∧ rb.wk = 0 := by
    cases W
    · simp only [Bool.false_eq_true, if_false] at hcv ⊢
      have hbr := pexecM_branch_false mv fu _ (assign1 mv.nv 0) Sk _ _ hcv _ (pexecM_skip mv fu _ _)
      have hs := seqM_some hbr (by simp) (pexecM_skip mv fu _ _)
      refine ⟨_, hs, rfl, by simp, rfl, ?_, ?_, rfl⟩
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
      · simp [gS_mem_len, gS_bs_len, hl, vwp, NExpr.nodes, NExpr.scalarOnly]
    · simp only [if_true] at hcv ⊢
      have hv0 : vdenM mv vv (penvN mv.nv (gS P (cl ++ [cb true] ++ [cb true]))) (.literal bT 0) = some 0 := by
        rw [vdenM_scalar mv vv _ _ rfl, den_literal, if_pos (show bT.valid 0 = true from rfl)]
      have g1 : (cl ++ [cb true] ++ [cb true])[1]? = some (cb f) := by
        rw [List.getElem?_append_left (by simp [hl]), List.getElem?_append_left (by simp [hl])]; exact h1
      have hs := gSM_assign mv P (cl ++ [cb true] ++ [cb true]) vv 1 (by simp [hl]) bT (.literal bT 0) 0 0 hv0 (cb f) g1 rfl
        (by cases f <;> decide) (by decide)
      have ha := (pexecM_prim mv fu _ _ _).trans hs
      have hb := seqM_some ha rfl (pexecM_skip mv fu _ _)
      have hsc := pexecM_scope mv fu _ _ _ _ hb
      have hset : (cl ++ [cb true] ++ [cb true]).set 1 ⟨bT, 0⟩ = cl.set 1 (cb false) ++ [cb true, cb true] := by
        rw [List.set_append_left _ _ (by simp [hl]), List.set_append_left _ _ (by simp [hl])]
        simp; rfl
      rw [hset, scope_same P _ _ (by simp [hl])] at hsc
      have hb2 := seqM_some hsc (by simp) (pexecM_skip mv fu _ _)
      have hbr := pexecM_branch_true mv fu _ _ Sk _ _ 1 hcv (by decide) _ hb2
      have hs2 := seqM_some hbr (by simp) (pexecM_skip mv fu _ _)
      refine ⟨_, hs2, rfl, by simp, rfl, ?_, ?_, rfl⟩
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
      · simp [gS_mem_len, gS_bs_len, hl, vwp, NExpr.nodes, NExpr.scalarOnly]
  obtain ⟨rb, hb, retb, psb, vvb, cb_, nb, wb⟩ := br
  have s3 := seqM_some a2 rfl (by exact hb)
  have s2 := seqM_some a1 rfl (by exact s3)
  refine ⟨_, s2, by simp [retb], by simp [psb], by simp [vvb], ?_, ?_, by simp [wb]⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at cb_ ⊢; omega
  · simp [gS_mem_len, gS_bs_len, hl, vwp, NExpr.nodes, NExpr.scalarOnly] at nb ⊢; omega


abbrev C9 (n : Nat) (f : Bool) (r d bi p : Nat) : List Cell :=
  [cu n, cb f, cI r, cu d, cI bi, cI bi, cu p, cu p, cu p]

set_option maxHeartbeats 64000000 in
theorem witInl_exec (mv : MV) (P : List Cell) (n r d bi p : Nat) (f : Bool) (hn : 2 ≤ n) (hnm : n < M64)
    (hr : r < 2147483640) (hp : p < n) (hd : d < M64) (vv : Nat → List Int) (fu : Nat) (hfu : r + 200 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (blk (witInl mv.nv)) (gS P (C9 n f r d bi p)) vv = some res ∧ res.ret = none ∧
      res.ps = gS P (if mrwx n r (p ^ d % n) then (C9 n f r d bi p).set 1 (cb false) else C9 n f r d bi p) ∧
      res.vv = vv ∧ res.cost ≤ 64 * CPW 0 + CWr r + 3000 ∧ res.need ≤ P.length + 2 * 50 + 900 ∧ res.wk = 0 := by
  have hn64 : n < M64 := hnm
  have hp64 : p < M64 := by omega
  have e0 : (C9 n f r d bi p)[0]? = some (cu n) := by simp
  have e3 : (C9 n f r d bi p)[3]? = some (cu d) := by simp
  have e2 : (C9 n f r d bi p)[2]? = some (cI r) := by simp
  have e8 : (C9 n f r d bi p)[8]? = some (cu p) := by simp
  have d1 := gSM_decl mv P (C9 n f r d bi p) vv u64 (vU mv.nv 0) n n
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact var_den mv P _ 0 n e0 hn64) (Ty.convert_of_valid _ _ (u64v n hn64))
  have a1 := (pexecM_prim mv fu (.declare u64 true (vU mv.nv 0)) _ _).trans d1
  have e3' : (C9 n f r d bi p ++ [cu n])[3]? = some (cu d) := by rw [List.getElem?_append_left (by simp)]; exact e3
  have d2 := gSM_decl mv P (C9 n f r d bi p ++ [cu n]) vv u64 (vU mv.nv 3) d d
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact var_den mv P _ 3 d e3' hd) (Ty.convert_of_valid _ _ (u64v d hd))
  have a2 := (pexecM_prim mv fu (.declare u64 true (vU mv.nv 3)) _ _).trans d2
  have e2' : (C9 n f r d bi p ++ [cu n] ++ [cu d])[2]? = some (cI r) := by
    rw [List.getElem?_append_left (by simp), List.getElem?_append_left (by simp)]; exact e2
  have d3 := gSM_decl mv P (C9 n f r d bi p ++ [cu n] ++ [cu d]) vv i32 (iV mv.nv 2) r r
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact vari_den mv P _ 2 r e2' (by omega)) (conv_signed i32 rfl rfl _ (i32vn r (by omega)))
  have a3 := (pexecM_prim mv fu (.declare i32 true (iV mv.nv 2)) _ _).trans d3
  have e8' : (C9 n f r d bi p ++ [cu n] ++ [cu d] ++ [cI r])[8]? = some (cu p) := by
    rw [List.getElem?_append_left (by simp), List.getElem?_append_left (by simp), List.getElem?_append_left (by simp)]; exact e8
  have d4 := gSM_decl mv P (C9 n f r d bi p ++ [cu n] ++ [cu d] ++ [cI r]) vv u64 (vU mv.nv 8) p p
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact var_den mv P _ 8 p e8' hp64) (Ty.convert_of_valid _ _ (u64v p hp64))
  have a4 := (pexecM_prim mv fu (.declare u64 true (vU mv.nv 8)) _ _).trans d4
  have hC : (C9 n f r d bi p).length = 9 := rfl
  have hl22 : (WSd (C9 n f r d bi p) n d r p (p ^ d % n) ((prun n 64 (1, p, d)).2.1) (mrX n r (p ^ d % n)) (mrwx n r (p ^ d % n))).length = 22 := by
    simp [WSd, WS]
  have c13 : (WSd (C9 n f r d bi p) n d r p (p ^ d % n) ((prun n 64 (1, p, d)).2.1) (mrX n r (p ^ d % n)) (mrwx n r (p ^ d % n)))[13]? = some (cb (mrwx n r (p ^ d % n))) := by
    simp [WSd, WS]
  have c1 : (WSd (C9 n f r d bi p) n d r p (p ^ d % n) ((prun n 64 (1, p, d)).2.1) (mrX n r (p ^ d % n)) (mrwx n r (p ^ d % n)))[1]? = some (cb f) := by
    simp [WSd, WS]
  obtain ⟨rR, hR1, retR, psR, vvR, cR, nR, wR⟩ := witR_exec mv P _ (mrwx n r (p ^ d % n)) f vv fu hl22 c13 c1
  obtain ⟨rp, hp1, retp, psp, vvp, cp, np, wp⟩ := wit_pre_exec mv P (C9 n f r d bi p) 9 hC n d r p hn hnm hr hp hd vv fu hfu
    (witR mv.nv) rR hR1
  have hst : C9 n f r d bi p ++ [cu n] ++ [cu d] ++ [cI r] ++ [cu p] = C9 n f r d bi p ++ [cu n, cu d, cI r, cu p] := by simp
  rw [hst] at a4
  have s4 := seqM_some a4 rfl hp1
  have s3 := seqM_some a3 rfl (by exact s4)
  have s2 := seqM_some a2 rfl (by exact s3)
  have s1 := seqM_some a1 rfl (by exact s2)
  have hsc := pexecM_scope mv fu _ _ _ _ s1
  have hlenC : (if mrwx n r (p ^ d % n) then (C9 n f r d bi p).set 1 (cb false) else C9 n f r d bi p).length =
      (C9 n f r d bi p).length := by
    cases mrwx n r (p ^ d % n) <;> simp
  have hps : rp.ps = gS P ((if mrwx n r (p ^ d % n) then (C9 n f r d bi p).set 1 (cb false) else C9 n f r d bi p) ++
      (WS n d r p (p ^ d % n) ((prun n 64 (1, p, d)).2.1) (mrX n r (p ^ d % n)) (mrwx n r (p ^ d % n)) ++
        [cb (mrwx n r (p ^ d % n)), cb (mrwx n r (p ^ d % n))])) := by
    rw [psp, psR]
    congr 1
    cases h : mrwx n r (p ^ d % n)
    · simp [WSd]
    · simp [WSd, List.set_append_left]
  have tk := gS_takeC P (C9 n f r d bi p) (if mrwx n r (p ^ d % n) then (C9 n f r d bi p).set 1 (cb false) else C9 n f r d bi p)
    (WS n d r p (p ^ d % n) ((prun n 64 (1, p, d)).2.1) (mrX n r (p ^ d % n)) (mrwx n r (p ^ d % n)) ++
        [cb (mrwx n r (p ^ d % n)), cb (mrwx n r (p ^ d % n))]) hlenC.symm
  have s0 := seqM_some hsc (by simp [retp, retR]) (pexecM_skip mv fu _ _)
  refine ⟨_, s0, by simp, ?_, by simp [vvp, vvR], ?_, ?_, by simp [wp, wR]⟩
  · simp only [hps]; exact tk
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at cp cR ⊢
    omega
  · simp [gS_mem_len, gS_bs_len, vwp, NExpr.nodes, NExpr.scalarOnly] at np nR ⊢
    omega


theorem eq_conv (x y : Int) : bT.convert (binaryValue .eq x y) = some (if x = y then 1 else 0) := by
  by_cases h : x = y
  · subst h; simp [binaryValue, Ty.convert, bT, Ty.valid]
  · have : (x == y) = false := by simp [h]
    simp [binaryValue, this, h, Ty.convert, bT, Ty.valid]

theorem cU_den (env : Nat → Ty → Option Int) (v : Int) (h0 : 0 ≤ v) (h1 : v < 2147483648) :
    (cU v).denote env = some v := by
  have hv : i32.valid v = true := by
    show Ty.valid ⟨32, true, false⟩ v = true
    simp [Ty.valid]; omega
  rw [den_cast, den_literal, if_pos hv, Option.bind_some, convert_u64]
  congr 1
  exact Int.emod_eq_of_lt h0 (by omega)

def chainRes (i : Nat) : Nat → List (Int × Int) → Nat
  | p, [] => p
  | p, (k, v) :: l => chainRes i (if (i : Int) = k then v.toNat else p) l

set_option maxHeartbeats 64000000 in
theorem chain_exec (mv : MV) (P : List Cell) (ci cp i : Nat) (hne : cp ≠ ci) (hi : i < 2147483648) (vv : Nat → List Int)
    (fu : Nat) :
    ∀ (l : List (Int × Int)) (cl : List Cell) (p0 : Nat), cl[ci]? = some (cI i) → cl[cp]? = some (cu p0) → p0 < M64 →
      (∀ kv ∈ l, 0 ≤ kv.1 ∧ kv.1 < 2147483648 ∧ 0 ≤ kv.2 ∧ kv.2 < 2147483648) →
      ∀ (K : Command) (rK : PRM), pexecM mv fu K (gS P (cl.set cp (cu (chainRes i p0 l)))) vv = some rK →
      ∃ res : PRM, pexecM mv fu (l.foldr (fun kv acc => baseIf mv.nv ci cp kv.1 kv.2 acc) K) (gS P cl) vv = some res ∧
        res.ret = rK.ret ∧ res.ps = rK.ps ∧ res.vv = rK.vv ∧ res.cost ≤ rK.cost + 60 * l.length ∧
        res.need ≤ max rK.need (P.length + 2 * cl.length + 60) ∧ res.wk = rK.wk := by
  intro l
  induction l with
  | nil =>
    intro cl p0 hci hcp hp hl K rK hK
    have hb : cp < cl.length := (List.getElem?_eq_some_iff.mp hcp).1
    have hg : cl[cp] = cu p0 := (List.getElem?_eq_some_iff.mp hcp).2
    have hcl : cl.set cp (cu p0) = cl := by
      calc cl.set cp (cu p0) = cl.set cp cl[cp] := by rw [hg]
        _ = cl := List.set_getElem_self hb
    simp only [chainRes, hcl] at hK
    refine ⟨rK, by simpa using hK, rfl, rfl, rfl, by simp, ?_, rfl⟩
    exact le_max_left _ _
  | cons kv l ih =>
    intro cl p0 hci hcp hp hl K rK hK
    obtain ⟨k, v⟩ := kv
    have hkv := hl (k, v) (by simp)
    have hl' : ∀ kv ∈ l, 0 ≤ kv.1 ∧ kv.1 < 2147483648 ∧ 0 ≤ kv.2 ∧ kv.2 < 2147483648 := fun kv h => hl kv (by simp [h])
    simp only at hkv
    have hM : (2147483648 : Nat) < M64 := by decide
    have hb : cp < cl.length := (List.getElem?_eq_some_iff.mp hcp).1
    have hcond : vdenM mv vv (penvN mv.nv (gS P cl)) (.binary bT .eq (.variable i32 (mv.nv + ci)) (.literal i32 k)) =
        some (if (i : Int) = k then 1 else 0) := by
      rw [vdenM_scalar _ _ _ _ rfl, den_binary]
      have hk : i32.valid k = true := by
        show Ty.valid ⟨32, true, false⟩ k = true
        simp [Ty.valid]; omega
      rw [vari_den mv P cl ci i hci hi, Option.bind_some, den_literal, if_pos hk, Option.bind_some]
      exact eq_conv _ _
    by_cases hik : (i : Int) = k
    · -- the branch is taken: p := v
      rw [if_pos hik] at hcond
      have hv : vdenM mv vv (penvN mv.nv (gS P cl)) (cU v) = some v := by
        rw [vdenM_scalar _ _ _ _ rfl]; exact cU_den _ v hkv.2.2.1 hkv.2.2.2
      have hs := gSM_assign mv P cl vv cp hb u64 (cU v) v v hv (cu p0) hcp rfl (u64v p0 hp)
        (Ty.convert_of_valid _ _ (u64v v.toNat (by omega)) |> fun h => by simpa [Int.toNat_of_nonneg hkv.2.2.1] using h)
      have hcell : (⟨u64, v⟩ : Cell) = cu v.toNat := by simp [cu, Int.toNat_of_nonneg hkv.2.2.1]
      rw [hcell] at hs
      have ha := (pexecM_prim mv fu _ _ _).trans hs
      have hb1 := seqM_some ha rfl (pexecM_skip mv fu _ _)
      have hsc := pexecM_scope mv fu _ _ _ _ hb1
      rw [scope_same P _ _ (by simp)] at hsc
      have hb2 := seqM_some hsc (by simp) (pexecM_skip mv fu _ _)
      have hbr := pexecM_branch_true mv fu _ _ Sk _ _ 1 hcond (by decide) _ hb2
      have hci' : (cl.set cp (cu v.toNat))[ci]? = some (cI i) := by
        rw [List.getElem?_set_ne (by omega)]; exact hci
      have hcp' : (cl.set cp (cu v.toNat))[cp]? = some (cu v.toNat) := by
        rw [List.getElem?_set_self hb]
      have hK' : pexecM mv fu K (gS P ((cl.set cp (cu v.toNat)).set cp (cu (chainRes i v.toNat l)))) vv = some rK := by
        rw [List.set_set]
        have : chainRes i p0 ((k, v) :: l) = chainRes i v.toNat l := by simp [chainRes, hik]
        rw [this] at hK; exact hK
      obtain ⟨r2, h2, ret2, ps2, vv2, c2, n2, w2⟩ := ih (cl.set cp (cu v.toNat)) v.toNat hci' hcp' (by omega) hl' K rK hK'
      have hseq := seqM_some hbr (by simp) h2
      refine ⟨_, hseq, by simpa using ret2, by simpa using ps2, by simpa using vv2, ?_, ?_, by simpa using w2⟩
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at c2 ⊢; omega
      · simp [gS_mem_len, gS_bs_len, vwp, NExpr.nodes, NExpr.scalarOnly] at n2 ⊢; omega
    · rw [if_neg hik] at hcond
      have hbr := pexecM_branch_false mv fu _ (assignP mv.nv cp v) Sk _ _ hcond _ (pexecM_skip mv fu _ _)
      have hK' : pexecM mv fu K (gS P (cl.set cp (cu (chainRes i p0 l)))) vv = some rK := by
        have : chainRes i p0 ((k, v) :: l) = chainRes i p0 l := by simp [chainRes, hik]
        rw [this] at hK; exact hK
      obtain ⟨r2, h2, ret2, ps2, vv2, c2, n2, w2⟩ := ih cl p0 hci hcp hp hl' K rK hK'
      have hseq := seqM_some hbr (by simp) h2
      refine ⟨_, hseq, by simpa using ret2, by simpa using ps2, by simpa using vv2, ?_, ?_, by simpa using w2⟩
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at c2 ⊢; omega
      · simp [gS_mem_len, gS_bs_len, vwp, NExpr.nodes, NExpr.scalarOnly] at n2 ⊢; omega


def mrb (i : Nat) : Nat :=
  if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 5 else if i = 3 then 7 else if i = 4 then 11
  else if i = 5 then 13 else if i = 6 then 17 else if i = 7 then 19 else if i = 8 then 23 else if i = 9 then 29
  else if i = 10 then 31 else 37

theorem chainRes_base (i : Nat) : chainRes i 37 baseTbl = mrb i := by
  by_cases h : i ≤ 10
  · obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega
    all_goals rfl
  · have : ∀ k : Int, (k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10) → (i : Int) ≠ k := by
      intro k hk; omega
    simp only [baseTbl, chainRes]
    rw [if_neg (this 0 (by simp)), if_neg (this 1 (by simp)), if_neg (this 2 (by simp)), if_neg (this 3 (by simp)),
      if_neg (this 4 (by simp)), if_neg (this 5 (by simp)), if_neg (this 6 (by simp)), if_neg (this 7 (by simp)),
      if_neg (this 8 (by simp)), if_neg (this 9 (by simp)), if_neg (this 10 (by simp))]
    unfold mrb
    simp [show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega, show i ≠ 3 by omega, show i ≠ 4 by omega,
      show i ≠ 5 by omega, show i ≠ 6 by omega, show i ≠ 7 by omega, show i ≠ 8 by omega, show i ≠ 9 by omega,
      show i ≠ 10 by omega, chainRes]

theorem base_chain_exec (mv : MV) (P : List Cell) (ci cp i : Nat) (hne : cp ≠ ci) (hi : i < 2147483648) (vv : Nat → List Int)
    (fu : Nat) (cl : List Cell) (hci : cl[ci]? = some (cI i)) (hcp : cl[cp]? = some (cu 37)) (K : Command) (rK : PRM)
    (hK : pexecM mv fu K (gS P (cl.set cp (cu (mrb i)))) vv = some rK) :
    ∃ res : PRM, pexecM mv fu (baseChain mv.nv ci cp K) (gS P cl) vv = some res ∧
      res.ret = rK.ret ∧ res.ps = rK.ps ∧ res.vv = rK.vv ∧ res.cost ≤ rK.cost + 700 ∧
      res.need ≤ max rK.need (P.length + 2 * cl.length + 60) ∧ res.wk = rK.wk := by
  rw [← chainRes_base] at hK
  obtain ⟨res, h1, h2, h3, h4, h5, h6, h7⟩ := chain_exec mv P ci cp i hne hi vv fu baseTbl cl 37 hci hcp (by decide)
    (by intro kv hkv; simp [baseTbl] at hkv; rcases hkv with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide) K rK hK
  exact ⟨res, h1, h2, h3, h4, by simp [baseTbl] at h5; omega, h6, h7⟩


theorem le_conv (x y : Int) : bT.convert (binaryValue .le x y) = some (if x ≤ y then 1 else 0) := by
  by_cases h : x ≤ y
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]

abbrev Lc (n : Nat) (f : Bool) (r d bi : Nat) : List Cell := [cu n, cb f, cI r, cu d, cI bi]

def stepF (n d r bi : Nat) (f : Bool) : Bool :=
  if mrb bi ≤ n - 2 ∧ mrwx n r (mrb bi ^ d % n) = true then false else f

set_option maxHeartbeats 64000000 in
theorem isp_tail (mv : MV) (P : List Cell) (n r d bi p : Nat) (f : Bool) (hn : 2 ≤ n) (hnm : n < M64)
    (hr : r < 2147483640) (hd : d < M64) (hp : p < M64) (vv : Nat → List Int) (fu : Nat) (hfu : r + 200 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (.sequence (.branch (.binary bT .le (vU mv.nv 8) (.binary u64 .sub (vU mv.nv 0) (cU 2)))
        (blk (witInl mv.nv)) Sk) Sk) (gS P (C9 n f r d bi p)) vv = some res ∧ res.ret = none ∧
      res.ps = gS P (if p ≤ n - 2 ∧ mrwx n r (p ^ d % n) = true then (C9 n f r d bi p).set 1 (cb false) else C9 n f r d bi p) ∧
      res.vv = vv ∧ res.cost ≤ 64 * CPW 0 + CWr r + 3500 ∧ res.need ≤ P.length + 2 * 50 + 1000 ∧ res.wk = 0 := by
  have hM : (2147483648 : Nat) < M64 := by decide
  have e8 : (C9 n f r d bi p)[8]? = some (cu p) := by simp
  have e0 : (C9 n f r d bi p)[0]? = some (cu n) := by simp
  have hsub : (NExpr.binary u64 .sub (vU mv.nv 0) (cU 2)).denote (penvN mv.nv (gS P (C9 n f r d bi p))) = some ((n - 2 : Nat) : Int) := by
    have h2 := sub_den (penvN mv.nv (gS P (C9 n f r d bi p))) (vU mv.nv 0) (cU 2) n 2 (var_den mv P _ 0 n e0 hnm)
      (by simpa using cU_den _ 2 (by decide) (by decide)) hn hnm
    exact h2
  have hcond : vdenM mv vv (penvN mv.nv (gS P (C9 n f r d bi p)))
      (.binary bT .le (vU mv.nv 8) (.binary u64 .sub (vU mv.nv 0) (cU 2))) = some (if p ≤ n - 2 then 1 else 0) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, var_den mv P _ 8 p e8 hp, Option.bind_some, hsub, Option.bind_some]
    have := le_conv (p : Int) ((n - 2 : Nat) : Int)
    simpa using this
  by_cases hle : p ≤ n - 2
  · rw [if_pos hle] at hcond
    obtain ⟨rw_, hw, hret, hps, hvv, hc, hn', hwk⟩ := witInl_exec mv P n r d bi p f hn hnm hr (by omega) hd vv fu hfu
    have hbr := pexecM_branch_true mv fu _ _ Sk _ _ 1 hcond (by decide) _ hw
    have hs := seqM_some hbr (by simp [hret]) (pexecM_skip mv fu _ _)
    refine ⟨_, hs, by simp [hret], ?_, by simp [hvv], ?_, ?_, by simp [hwk]⟩
    · simp [hps, hle]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at hc ⊢; omega
    · by_cases hW : mrwx n r (p ^ d % n) = true <;>
        simp [hW, hps, gS_mem_len, gS_bs_len, vwp, NExpr.nodes, NExpr.scalarOnly] at hn' ⊢ <;> omega
  · rw [if_neg hle] at hcond
    have hbr := pexecM_branch_false mv fu _ (blk (witInl mv.nv)) Sk _ _ hcond _ (pexecM_skip mv fu _ _)
    have hs := seqM_some hbr (by simp) (pexecM_skip mv fu _ _)
    refine ⟨_, hs, rfl, by simp [hle], rfl, ?_, ?_, rfl⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
    · simp [gS_mem_len, gS_bs_len, vwp, NExpr.nodes, NExpr.scalarOnly]



set_option maxHeartbeats 64000000 in
theorem isp_iter (mv : MV) (P : List Cell) (n r d bi : Nat) (f : Bool) (hn : 2 ≤ n) (hnm : n < M64)
    (hr : r < 2147483640) (hd : d < M64) (hbi : bi < 12) (vv : Nat → List Int) (fu : Nat) (hfu : r + 200 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (.sequence (.scope (iterStmts mv.nv)) (.sequence (incI mv.nv 4) Sk))
        (gS P (Lc n f r d bi)) vv = some res ∧ res.ret = none ∧
      res.ps = gS P (Lc n (stepF n d r bi f) r d (bi + 1)) ∧ res.vv = vv ∧
      res.cost ≤ 64 * CPW 0 + CWr r + 5000 ∧ res.need ≤ P.length + 2 * 60 + 1000 ∧ res.wk = 0 := by
  have hM : (2147483648 : Nat) < M64 := by decide
  have hb2 : bi < 2147483648 := by omega
  have e4 : (Lc n f r d bi)[4]? = some (cI bi) := by simp
  have d1 := gSM_decl mv P (Lc n f r d bi) vv i32 (iV mv.nv 4) bi bi
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact vari_den mv P _ 4 bi e4 hb2) (conv_signed i32 rfl rfl _ (i32vn bi hb2))
  have a1 := (pexecM_prim mv fu (.declare i32 true (iV mv.nv 4)) _ _).trans d1
  have d2 := gSM_decl mv P (Lc n f r d bi ++ [cI bi]) vv u64 (cU 37) 37 37
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact cU_den _ 37 (by decide) (by decide)) (Ty.convert_of_valid _ _ (u64v 37 (by omega)))
  have a2 := (pexecM_prim mv fu (.declare u64 true (cU 37)) _ _).trans d2
  have h37 : mrb bi ≤ 37 := by unfold mrb; repeat' (first | split | omega)
  have hpb : mrb bi < M64 := by omega
  set p := mrb bi with hpdef
  have hCL2 : (Lc n f r d bi ++ [cI bi] ++ [cu 37])[5]? = some (cI bi) := by simp
  have hCL2' : (Lc n f r d bi ++ [cI bi] ++ [cu 37])[6]? = some (cu 37) := by simp
  have h6 : (Lc n f r d bi ++ [cI bi] ++ [cu 37]).set 6 (cu p) = Lc n f r d bi ++ [cI bi, cu p] := by simp [List.set]
  have g6 : (Lc n f r d bi ++ [cI bi, cu p])[6]? = some (cu p) := by simp
  have dd1 := gSM_decl mv P (Lc n f r d bi ++ [cI bi, cu p]) vv u64 (vU mv.nv 6) p p
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact var_den mv P _ 6 p g6 hpb) (Ty.convert_of_valid _ _ (u64v p hpb))
  have b1 := (pexecM_prim mv fu (.declare u64 true (vU mv.nv 6)) _ _).trans dd1
  have g7 : (Lc n f r d bi ++ [cI bi, cu p] ++ [cu p])[7]? = some (cu p) := by simp
  have dd2 := gSM_decl mv P (Lc n f r d bi ++ [cI bi, cu p] ++ [cu p]) vv u64 (vU mv.nv 7) p p
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact var_den mv P _ 7 p g7 hpb) (Ty.convert_of_valid _ _ (u64v p hpb))
  have b2 := (pexecM_prim mv fu (.declare u64 true (vU mv.nv 7)) _ _).trans dd2
  have hC9 : Lc n f r d bi ++ [cI bi, cu p] ++ [cu p] ++ [cu p] = C9 n f r d bi p := by simp
  rw [hC9] at b2
  obtain ⟨rt, ht, rett, pst, vvt, ct, nt, wkt⟩ := isp_tail mv P n r d bi p f hn hnm hr hd hpb vv fu hfu
  have s2 := seqM_some b2 rfl ht
  have s1 := seqM_some b1 rfl (by simpa using s2)
  obtain ⟨rc, hc, retc, psc, vvc, cc, nc, wkc⟩ := base_chain_exec mv P 5 6 bi (by decide) hb2 vv fu _ hCL2 hCL2' _ _ (by rw [h6]; exact s1)
  have t2 := seqM_some a2 rfl hc
  have t1 := seqM_some a1 rfl (by simpa using t2)
  have hsc := pexecM_scope mv fu _ _ _ _ t1
  have tk := gS_takeC P (Lc n f r d bi) (Lc n (stepF n d r bi f) r d bi) [cI bi, cu p, cu p, cu p] (by simp)
  have hc9 : Lc n (stepF n d r bi f) r d bi ++ [cI bi, cu p, cu p, cu p] =
      (if p ≤ n - 2 ∧ mrwx n r (p ^ d % n) = true then (C9 n f r d bi p).set 1 (cb false) else C9 n f r d bi p) := by
    unfold stepF
    rw [← hpdef]
    by_cases hh : p ≤ n - 2 ∧ mrwx n r (p ^ d % n) = true
    · simp [hh, List.set]
    · simp [hh]
  rw [hc9] at tk
  have hsc' : ∃ rs : PRM, pexecM mv fu (.scope (iterStmts mv.nv)) (gS P (Lc n f r d bi)) vv = some rs ∧ rs.ret = none ∧
      rs.ps = gS P (Lc n (stepF n d r bi f) r d bi) ∧ rs.vv = vv ∧ rs.cost ≤ 64 * CPW 0 + CWr r + 4800 ∧
      rs.need ≤ P.length + 2 * 60 + 1000 ∧ rs.wk = 0 := by
    refine ⟨_, hsc, by simp [retc, rett], ?_, by simp [vvc, vvt], ?_, ?_, by simp [wkc, wkt]⟩
    · simp only [psc, pst]; exact tk
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at cc ct ⊢; omega
    · simp [gS_mem_len, gS_bs_len, vwp, NExpr.nodes, NExpr.scalarOnly] at nc nt ⊢; omega
  obtain ⟨rs, hs1, rets, pss, vvs, cs_, ns, wks⟩ := hsc'
  have e4' : (Lc n (stepF n d r bi f) r d bi)[4]? = some (cI bi) := by simp
  obtain ⟨ri, hi1, reti, psi, vvi, ci_, ni, wki⟩ := inc_exec mv P (Lc n (stepF n d r bi f) r d bi) 4 bi e4' (by omega) vv fu Sk _
    (pexecM_skip mv fu _ _)
  have hfin := seqM_some hs1 rets (by rw [pss, vvs]; exact hi1)
  refine ⟨_, hfin, by simp [reti], ?_, by simp [vvi], ?_, ?_, by simp [wki, wks]⟩
  · simp [psi, List.set]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at ci_ cs_ ⊢; omega
  · simp [gS_mem_len, gS_bs_len, vwp, NExpr.nodes, NExpr.scalarOnly] at ni ns ⊢; omega

def ispRun (n d r : Nat) : Nat → Nat → Bool → Bool
  | 0, _, f => f
  | k + 1, bi, f => ispRun n d r k (bi + 1) (stepF n d r bi f)

def CIT : Nat := 64 * CPW 0 + 5100

set_option maxHeartbeats 64000000 in
theorem isp_while (mv : MV) (P : List Cell) (n r d : Nat) (hn : 2 ≤ n) (hnm : n < M64)
    (hr : r < 2147483640) (hd : d < M64) (vv : Nat → List Int) :
    ∀ (k bi fu : Nat) (f : Bool), bi + k = 12 → k + r + 200 ≤ fu →
      ∃ res : PRM, pexecM mv fu (.whileLoop (.binary bT .lt (iV mv.nv 4) (.literal i32 12))
          (.sequence (.scope (iterStmts mv.nv)) (.sequence (incI mv.nv 4) Sk))) (gS P (Lc n f r d bi)) vv = some res ∧
        res.ret = none ∧ res.ps = gS P (Lc n (ispRun n d r k bi f) r d 12) ∧ res.vv = vv ∧
        res.cost ≤ k * (CIT + CWr r) + 100 ∧ res.need ≤ P.length + 2 * 60 + 1000 ∧ res.wk = 0 := by
  intro k
  induction k with
  | zero =>
    intro bi fu f hk hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have e4 : (Lc n f r d bi)[4]? = some (cI bi) := by simp
    have hc : vdenM mv vv (penvN mv.nv (gS P (Lc n f r d bi))) (.binary bT .lt (iV mv.nv 4) (.literal i32 12)) = some 0 := by
      rw [vdenM_scalar _ _ _ _ rfl, den_binary, vari_den mv P _ 4 bi e4 (by omega), Option.bind_some, den_literal,
        if_pos (show i32.valid 12 = true from rfl), Option.bind_some]
      have := lt_conv (bi : Int) 12
      rw [if_neg (by omega)] at this
      exact this
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    have hb : bi = 12 := by omega
    subst hb
    refine ⟨_, rfl, rfl, by simp [ispRun], rfl, ?_, ?_, rfl⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
    · simp [gS_mem_len, gS_bs_len, vwp, NExpr.nodes, NExpr.scalarOnly]
  | succ k ih =>
    intro bi fu f hk hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have e4 : (Lc n f r d bi)[4]? = some (cI bi) := by simp
    have hc : vdenM mv vv (penvN mv.nv (gS P (Lc n f r d bi))) (.binary bT .lt (iV mv.nv 4) (.literal i32 12)) = some 1 := by
      rw [vdenM_scalar _ _ _ _ rfl, den_binary, vari_den mv P _ 4 bi e4 (by omega), Option.bind_some, den_literal,
        if_pos (show i32.valid 12 = true from rfl), Option.bind_some]
      have := lt_conv (bi : Int) 12
      rw [if_pos (by omega)] at this
      exact this
    obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := isp_iter mv P n r d bi f hn hnm hr hd (by omega) vv (fu' + 1) (by omega)
    obtain ⟨r2, h2, ret2, ps2, vv2, c2, n2, w2⟩ := ih (bi + 1) fu' (stepF n d r bi f) (by omega) (by omega)
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, int_one_ne, ite_false]
    rw [h1]
    simp only [ret1, ps1, vv1]
    rw [h2]
    simp only
    refine ⟨_, rfl, ret2, ?_, vv2, ?_, ?_, ?_⟩
    · rw [ps2]; rfl
    · rw [Nat.succ_mul]
      have hCIT : CIT = 64 * CPW 0 + 5100 := rfl
      simp [vwp, NExpr.nodes, NExpr.scalarOnly] at c1 c2 ⊢; omega
    · simp [gS_mem_len, gS_bs_len, vwp, NExpr.nodes, NExpr.scalarOnly] at n1 n2 ⊢; omega
    · simp [w1, w2]


theorem den_or_b (env : Nat → Ty → Option Int) (l r : NExpr) :
    (NExpr.logical false l r).denote env = (l.denote env).bind fun a =>
      if a == 0 then (r.denote env).bind fun b => some (if b == 0 then 0 else 1) else some 1 := by
  simp [NExpr.denote]

theorem cond2_den (mv : MV) (vv : Nat → List Int) (P cl : List Cell) (n : Nat) (hn : n < M64) (h0 : cl[0]? = some (cu n)) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (.logical false (.binary bT .eq (.divrem u64 true (vU mv.nv 0) (cU 2)) (cU 0))
      (.binary bT .le (vU mv.nv 0) (cU 1))) = some (if n % 2 = 0 ∨ n ≤ 1 then 1 else 0) := by
  have hr : checkedDivRem u64 true (n : Int) 2 = some ((n % 2 : Nat) : Int) := Proofs.PowModStep.rem_value n 2 (by omega) hn
  have c2 : (cU 2).denote (penvN mv.nv (gS P cl)) = some (2 : Int) := cU_den _ 2 (by decide) (by decide)
  have c0 : (cU 0).denote (penvN mv.nv (gS P cl)) = some (0 : Int) := cU_den _ 0 (by decide) (by decide)
  have c1 : (cU 1).denote (penvN mv.nv (gS P cl)) = some (1 : Int) := cU_den _ 1 (by decide) (by decide)
  have e1 : (NExpr.binary bT .eq (.divrem u64 true (vU mv.nv 0) (cU 2)) (cU 0)).denote (penvN mv.nv (gS P cl)) =
      some (if n % 2 = 0 then 1 else 0) := by
    rw [den_binary, den_divrem, var_den mv P cl 0 n h0 hn, Option.bind_some, c2, Option.bind_some, hr, Option.bind_some, c0,
      Option.bind_some]
    rw [eq_conv]
    by_cases h : n % 2 = 0
    · rw [if_pos (show ((n % 2 : Nat) : Int) = 0 by omega), if_pos h]
    · rw [if_neg (show ¬ ((n % 2 : Nat) : Int) = 0 by omega), if_neg h]
  have e2 : (NExpr.binary bT .le (vU mv.nv 0) (cU 1)).denote (penvN mv.nv (gS P cl)) = some (if n ≤ 1 then 1 else 0) := by
    rw [den_binary, var_den mv P cl 0 n h0 hn, Option.bind_some, c1, Option.bind_some]
    have := le_conv (n : Int) 1
    simpa using this
  rw [vdenM_scalar _ _ _ _ rfl, den_or_b, e1]
  by_cases h : n % 2 = 0
  · simp [h]
  · rw [e2]
    by_cases h1 : n ≤ 1 <;> simp [h, h1]

theorem eq2_den (mv : MV) (vv : Nat → List Int) (P cl : List Cell) (n : Nat) (hn : n < M64) (h0 : cl[0]? = some (cu n)) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (.binary bT .eq (vU mv.nv 0) (cU 2)) = some (if n = 2 then 1 else 0) := by
  have c2 : (cU 2).denote (penvN mv.nv (gS P cl)) = some (2 : Int) := cU_den _ 2 (by decide) (by decide)
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, var_den mv P cl 0 n h0 hn, Option.bind_some, c2, Option.bind_some]
  rw [eq_conv]
  by_cases h : n = 2
  · rw [if_pos (show (n : Int) = 2 by omega), if_pos h]
  · rw [if_neg (show ¬ (n : Int) = 2 by omega), if_neg h]


def dloop : Nat → Nat → Nat → Nat × Nat
  | 0, d, r => (d, r)
  | k + 1, d, r => if d % 2 = 0 then dloop k (d / 2) (r + 1) else (d, r)

theorem dloop_spec : ∀ (k d r : Nat), 0 < d → d < 2 ^ k →
    (dloop k d r).1 % 2 = 1 ∧ (dloop k d r).1 * 2 ^ ((dloop k d r).2 - r) = d ∧ r ≤ (dloop k d r).2 ∧
      (dloop k d r).2 ≤ r + k
  | 0, d, r, h0, hk => by simp at hk; omega
  | k + 1, d, r, h0, hk => by
    by_cases h : d % 2 = 0
    · have e : dloop (k + 1) d r = dloop k (d / 2) (r + 1) := by simp [dloop, h]
      rw [e]
      have hd2 : 0 < d / 2 := by omega
      have hk2 : d / 2 < 2 ^ k := by rw [Nat.pow_succ] at hk; omega
      obtain ⟨a1, a2, a3, a4⟩ := dloop_spec k (d / 2) (r + 1) hd2 hk2
      refine ⟨a1, ?_, by omega, by omega⟩
      have : (dloop k (d / 2) (r + 1)).2 - r = ((dloop k (d / 2) (r + 1)).2 - (r + 1)) + 1 := by omega
      rw [this, Nat.pow_succ, ← Nat.mul_assoc, a2]
      omega
    · have e : dloop (k + 1) d r = (d, r) := by simp [dloop, h]
      rw [e]
      simp
      omega

abbrev Dc (n : Nat) (f : Bool) (r d : Nat) : List Cell := [cu n, cb f, cI r, cu d]

theorem mod2_den (mv : MV) (vv : Nat → List Int) (P cl : List Cell) (c y : Nat) (hy : y < M64) (h0 : cl[c]? = some (cu y)) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (.binary bT .eq (.divrem u64 true (vU mv.nv c) (cU 2)) (cU 0)) =
      some (if y % 2 = 0 then 1 else 0) := by
  have hr : checkedDivRem u64 true (y : Int) 2 = some ((y % 2 : Nat) : Int) := Proofs.PowModStep.rem_value y 2 (by omega) hy
  have c2 : (cU 2).denote (penvN mv.nv (gS P cl)) = some (2 : Int) := cU_den _ 2 (by decide) (by decide)
  have c0 : (cU 0).denote (penvN mv.nv (gS P cl)) = some (0 : Int) := cU_den _ 0 (by decide) (by decide)
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_divrem, var_den mv P cl c y h0 hy, Option.bind_some, c2, Option.bind_some, hr,
    Option.bind_some, c0, Option.bind_some, eq_conv]
  by_cases h : y % 2 = 0
  · rw [if_pos (show ((y % 2 : Nat) : Int) = 0 by omega), if_pos h]
  · rw [if_neg (show ¬ ((y % 2 : Nat) : Int) = 0 by omega), if_neg h]

set_option maxHeartbeats 64000000 in
theorem dec_iter (mv : MV) (P : List Cell) (n r d : Nat) (f : Bool) (hd : d < M64) (hr : r + 1 < 2147483648) (hd2 : d % 2 = 0)
    (vv : Nat → List Int) (fu : Nat) :
    ∃ res : PRM, pexecM mv fu (blk (.sequence (.primitive (.assign (mv.nv + 3) u64 (.divrem u64 false (vU mv.nv 3) (cU 2))))
        (.sequence (incI mv.nv 2) Sk))) (gS P (Dc n f r d)) vv = some res ∧ res.ret = none ∧
      res.ps = gS P (Dc n f (r + 1) (d / 2)) ∧ res.vv = vv ∧ res.cost ≤ 200 ∧ res.need ≤ P.length + 2 * 4 + 100 ∧ res.wk = 0 := by
  have e2 : (Dc n f r d |>.set 3 (cu (d / 2)))[2]? = some (cI r) := by simp [List.set]
  obtain ⟨ri, hi1, reti, psi, vvi, ci_, ni, wki⟩ := inc_exec mv P (Dc n f r d |>.set 3 (cu (d / 2))) 2 r e2 hr vv fu Sk _
    (pexecM_skip mv fu _ _)
  have e3 : (Dc n f r d)[3]? = some (cu d) := by simp
  obtain ⟨rh, hh1, reth, psh, vvh, ch, nh, wkh⟩ := halve_exec mv P (Dc n f r d) 3 d e3 hd vv fu _ _ hi1
  have hsc := pexecM_scope mv fu _ _ _ _ hh1
  have hps : rh.ps = gS P (Dc n f (r + 1) (d / 2)) := by
    rw [psh, psi]; simp [List.set]
  rw [hps, scope_same P _ _ (by simp)] at hsc
  have hfin := seqM_some hsc (by simp [reth, reti]) (pexecM_skip mv fu _ _)
  refine ⟨_, hfin, by simp, by simp, by simp [vvh, vvi], ?_, ?_, by simp [wkh, wki]⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at ch ci_ ⊢; omega
  · simp [gS_mem_len, gS_bs_len, vwp, NExpr.nodes, NExpr.scalarOnly] at nh ni ⊢; omega


set_option maxHeartbeats 64000000 in
theorem dec_while (mv : MV) (P : List Cell) (n : Nat) (hn : n < M64) (vv : Nat → List Int) :
    ∀ (k d r fu : Nat) (f : Bool), 0 < d → d < 2 ^ k → d < M64 → r + k < 2147483640 → k + 10 ≤ fu →
      ∃ res : PRM, pexecM mv fu (decLoop mv.nv) (gS P (Dc n f r d)) vv = some res ∧ res.ret = none ∧
        res.ps = gS P (Dc n f (dloop k d r).2 (dloop k d r).1) ∧ res.vv = vv ∧ res.cost ≤ k * 300 + 100 ∧
        res.need ≤ P.length + 2 * 4 + 100 ∧ res.wk = 0 := by
  intro k
  induction k with
  | zero => intro d r fu f h0 hk; simp at hk; omega
  | succ k ih =>
    intro d r fu f h0 hk hd hr hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have e3 : (Dc n f r d)[3]? = some (cu d) := by simp
    have hc := mod2_den mv vv P (Dc n f r d) 3 d hd e3
    by_cases h2 : d % 2 = 0
    · rw [if_pos h2] at hc
      obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := dec_iter mv P n r d f hd (by omega) h2 vv (fu' + 1)
      have hd2 : 0 < d / 2 := by omega
      have hk2 : d / 2 < 2 ^ k := by rw [Nat.pow_succ] at hk; omega
      obtain ⟨r2, h2', ret2, ps2, vv2, c2, n2, w2⟩ := ih (d / 2) (r + 1) fu' f hd2 hk2 (by omega) (by omega) (by omega)
      rw [pexecM_while, hc]
      simp only [Bind.bind, Option.bind, int_one_ne, ite_false]
      rw [h1]
      simp only [ret1, ps1, vv1]
      rw [h2']
      simp only
      refine ⟨_, rfl, ret2, ?_, vv2, ?_, ?_, ?_⟩
      · rw [ps2]
        have e : dloop (k + 1) d r = dloop k (d / 2) (r + 1) := by simp [dloop, h2]
        rw [e]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at c1 c2 ⊢; omega
      · simp [gS_mem_len, gS_bs_len, vwp, NExpr.nodes, NExpr.scalarOnly] at n1 n2 ⊢; omega
      · simp [w1, w2]
    · rw [if_neg h2] at hc
      rw [pexecM_while, hc]
      simp only [Bind.bind, Option.bind, ite_true]
      refine ⟨_, rfl, rfl, ?_, rfl, ?_, ?_, rfl⟩
      · have e : dloop (k + 1) d r = (d, r) := by simp [dloop, h2]
        rw [e]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
      · simp [gS_mem_len, gS_bs_len, vwp, NExpr.nodes, NExpr.scalarOnly]


def ispF (n : Nat) : Bool := ispRun n (dloop 64 (n - 1) 0).1 (dloop 64 (n - 1) 0).2 12 0 true

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem else2_exec (mv : MV) (P : List Cell) (n : Nat) (h3 : 3 ≤ n) (hnm : n < M64) (vv : Nat → List Int) (fu : Nat)
    (hfu : 400 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (else2 mv.nv) (gS P [cu n, cb true]) vv = some res ∧ res.ret = none ∧
      res.ps = gS P (Dc n (ispF n) (dloop 64 (n - 1) 0).2 (dloop 64 (n - 1) 0).1) ∧ res.vv = vv ∧
      res.cost ≤ 12 * (CIT + 64 * CWL) + 64 * 300 + 1000 ∧ res.need ≤ P.length + 2 * 60 + 1000 ∧ res.wk = 0 := by
  have hM : (2147483648 : Nat) < M64 := by decide
  have hM2 : M64 = 2 ^ 64 := by decide
  -- declare i32 r = 0
  have d1 := gSM_decl mv P [cu n, cb true] vv i32 (.literal i32 0) 0 0
    (by rw [vdenM_scalar _ _ _ _ rfl]; rw [den_literal, if_pos (show i32.valid 0 = true from rfl)])
    (conv_signed i32 rfl rfl _ (show i32.valid 0 = true from rfl))
  have a1 := (pexecM_prim mv fu (.declare i32 true (.literal i32 0)) _ _).trans d1
  -- declare u64 d = n - 1
  have e0 : ([cu n, cb true] ++ [(⟨i32, 0⟩ : Cell)])[0]? = some (cu n) := by simp
  have hsub : (NExpr.binary u64 .sub (vU mv.nv 0) (cU 1)).denote (penvN mv.nv (gS P ([cu n, cb true] ++ [(⟨i32, 0⟩ : Cell)]))) =
      some ((n - 1 : Nat) : Int) :=
    sub_den _ _ _ n 1 (var_den mv P _ 0 n e0 hnm) (by simpa using cU_den _ 1 (by decide) (by decide)) (by omega) hnm
  have d2 := gSM_decl mv P ([cu n, cb true] ++ [(⟨i32, 0⟩ : Cell)]) vv u64 (.binary u64 .sub (vU mv.nv 0) (cU 1)) ((n - 1 : Nat) : Int) ((n - 1 : Nat) : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact hsub) (Ty.convert_of_valid _ _ (u64v (n - 1) (by omega)))
  have a2 := (pexecM_prim mv fu (.declare u64 true (.binary u64 .sub (vU mv.nv 0) (cU 1))) _ _).trans d2
  have hDc : [cu n, cb true] ++ [(⟨i32, 0⟩ : Cell)] ++ [cu (n - 1)] = Dc n true 0 (n - 1) := by simp [cI]
  rw [hDc] at a2
  -- the halving loop
  have hd0 : 0 < n - 1 := by omega
  have hd64 : n - 1 < 2 ^ 64 := by omega
  obtain ⟨rl, hl1, retl, psl, vvl, cl_, nl, wkl⟩ := dec_while mv P n hnm vv 64 (n - 1) 0 fu true hd0 hd64 (by omega) (by omega) (by omega)
  obtain ⟨sp1, sp2, sp3, sp4⟩ := dloop_spec 64 (n - 1) 0 hd0 hd64
  obtain ⟨r', hr'⟩ : ∃ r', (dloop 64 (n - 1) 0).2 = r' := ⟨_, rfl⟩
  obtain ⟨d', hd'⟩ : ∃ d', (dloop 64 (n - 1) 0).1 = d' := ⟨_, rfl⟩
  simp only [hr', hd'] at psl sp1 sp2 sp3 sp4
  unfold ispF
  rw [hr', hd']
  have hispF : ispRun n d' r' 12 0 true = ispF n := by unfold ispF; rw [hr', hd']
  have hdle : d' ≤ n - 1 := by
    have h1 : d' ≤ d' * 2 ^ (r' - 0) := Nat.le_mul_of_pos_right d' (Nat.two_pow_pos _)
    omega
  have hdm : d' < M64 := by omega
  have hr64 : r' ≤ 64 := by omega
  -- the for loop over the 12 bases
  have d3 := gSM_decl mv P (Dc n true r' d') vv i32 (.literal i32 0) 0 0
    (by rw [vdenM_scalar _ _ _ _ rfl]; rw [den_literal, if_pos (show i32.valid 0 = true from rfl)])
    (conv_signed i32 rfl rfl _ (show i32.valid 0 = true from rfl))
  have a3 := (pexecM_prim mv fu (.declare i32 true (.literal i32 0)) _ _).trans d3
  have hLc : Dc n true r' d' ++ [(⟨i32, 0⟩ : Cell)] = Lc n true r' d' 0 := by simp [cI]
  rw [hLc] at a3
  obtain ⟨rw_, hw, hret, hps, hvv, hc, hn', hwk⟩ := isp_while mv P n r' d' (by omega) hnm (by omega) hdm vv 12 0 fu true (by omega) (by omega)
  have s3 := seqM_some hw hret (pexecM_skip mv fu _ _)
  have s2 := seqM_some a3 rfl (by exact s3)
  have hfor := pexecM_scope mv fu _ _ _ _ s2
  have tk := gS_takeC P (Dc n true r' d') (Dc n (ispRun n d' r' 12 0 true) r' d') [cI 12] (by simp)
  have hLc2 : Dc n (ispRun n d' r' 12 0 true) r' d' ++ [cI 12] = Lc n (ispRun n d' r' 12 0 true) r' d' 12 := by simp
  rw [hLc2] at tk
  have hcost : 12 * (CIT + CWr r') ≤ 12 * (CIT + 64 * CWL) :=
    Nat.mul_le_mul_left 12 (Nat.add_le_add_left (Nat.mul_le_mul_right _ hr64) _)
  have hfor2 : ∃ rf : PRM, pexecM mv fu (forLoop mv.nv) (gS P (Dc n true r' d')) vv = some rf ∧ rf.ret = none ∧
      rf.ps = gS P (Dc n (ispRun n d' r' 12 0 true) r' d') ∧ rf.vv = vv ∧ rf.cost ≤ 12 * (CIT + 64 * CWL) + 300 ∧
      rf.need ≤ P.length + 2 * 60 + 1000 ∧ rf.wk = 0 := by
    refine ⟨_, hfor, by simp [hret], ?_, by simp [hvv], ?_, ?_, by simp [hwk]⟩
    · simp only [hps]; exact tk
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at hc ⊢; omega
    · simp [hps, gS_mem_len, gS_bs_len, vwp, NExpr.nodes, NExpr.scalarOnly] at hn' ⊢; omega
  obtain ⟨rf, hf1, retf, psf, vvf, cf_, nf, wkf⟩ := hfor2
  have sf := seqM_some hf1 retf (pexecM_skip mv fu _ _)
  have s4 := seqM_some hl1 retl (by rw [psl, vvl]; exact sf)
  have s5 := seqM_some a2 rfl (by exact s4)
  have s6 := seqM_some a1 rfl (by exact s5)
  refine ⟨_, s6, by simp [retf], by simp [psf], by simp [vvf], ?_, ?_, by simp [wkf, wkl]⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at cl_ cf_ ⊢; omega
  · simp [psl, psf, gS_mem_len, gS_bs_len, vwp, NExpr.nodes, NExpr.scalarOnly] at nl nf ⊢; omega


theorem assign1_exec (mv : MV) (P : List Cell) (n : Nat) (f0 g : Bool) (vv : Nat → List Int) (fu : Nat) :
    ∃ res : PRM, pexecM mv fu (assign1 mv.nv (if g then 1 else 0)) (gS P [cu n, cb f0]) vv = some res ∧ res.ret = none ∧
      res.ps = gS P [cu n, cb g] ∧ res.vv = vv ∧ res.cost ≤ 50 ∧ res.need ≤ P.length + 2 * 2 + 50 ∧ res.wk = 0 := by
  have hv : vdenM mv vv (penvN mv.nv (gS P [cu n, cb f0])) (.literal bT (if g then 1 else 0)) = some (if g then 1 else 0) := by
    rw [vdenM_scalar mv vv _ _ rfl, den_literal, if_pos (by cases g <;> decide)]
  have hs := gSM_assign mv P [cu n, cb f0] vv 1 (by simp) bT (.literal bT (if g then 1 else 0)) (if g then 1 else 0) (if g then 1 else 0)
    hv (cb f0) (by simp) rfl (by cases f0 <;> decide) (by cases g <;> decide)
  have ha := (pexecM_prim mv fu _ _ _).trans hs
  have hb := seqM_some ha rfl (pexecM_skip mv fu _ _)
  have hsc := pexecM_scope mv fu _ _ _ _ hb
  have hset : ([cu n, cb f0] : List Cell).set 1 ⟨bT, if g then 1 else 0⟩ = [cu n, cb g] := by simp [List.set, cb]
  rw [hset, scope_same P _ _ (by simp)] at hsc
  have hfin := seqM_some hsc (by simp) (pexecM_skip mv fu _ _)
  refine ⟨_, hfin, by simp, by simp, by simp, ?_, ?_, by simp⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
  · simp [gS_mem_len, gS_bs_len, vwp, NExpr.nodes, NExpr.scalarOnly]


def ispSpec (n : Nat) : Bool :=
  if n = 2 then true else if n % 2 = 0 ∨ n ≤ 1 then false else ispF n

def TOPC : Nat := 12 * (CIT + 64 * CWL) + 64 * 300 + 3000

abbrev cond2E (nv : Nat) : NExpr :=
  .logical false (.binary bT .eq (.divrem u64 true (vU nv 0) (cU 2)) (cU 0)) (.binary bT .le (vU nv 0) (cU 1))

abbrev topElse (nv : Nat) : Command :=
  blk (.sequence (.branch (cond2E nv) (assign1 nv 0) (blk (else2 nv))) Sk)

abbrev topBR (nv : Nat) : Command := .branch (.binary bT .eq (vU nv 0) (cU 2)) (assign1 nv 1) (topElse nv)

theorem isBodyT_eq (nv : Nat) : isBodyT nv = .sequence (.primitive (.declare bT true (.literal bT 1)))
    (.sequence (topBR nv) (.sequence (.primitive (.ret (bV nv 1))) Sk)) := rfl

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem top_mid (mv : MV) (P : List Cell) (n : Nat) (hnm : n < M64) (vv : Nat → List Int) (fu : Nat) (hfu : 400 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (topBR mv.nv) (gS P [cu n, cb true]) vv = some res ∧ res.ret = none ∧
      res.ps = gS P [cu n, cb (ispSpec n)] ∧ res.vv = vv ∧
      res.cost ≤ TOPC ∧ res.need ≤ P.length + 2 * 60 + 1000 ∧ res.wk = 0 := by
  have hT : TOPC = 12 * (CIT + 64 * CWL) + 64 * 300 + 3000 := rfl
  have e0 : ([cu n, cb true] : List Cell)[0]? = some (cu n) := by simp
  have c1 := eq2_den mv vv P [cu n, cb true] n hnm e0
  by_cases h2 : n = 2
  · rw [if_pos h2] at c1
    obtain ⟨ra, ha1, reta, psa, vva, ca, na, wka⟩ := assign1_exec mv P n true true vv fu
    have hbr := pexecM_branch_true mv fu _ (assign1 mv.nv 1) (topElse mv.nv) _ _ 1 c1 (by decide) _ ha1
    refine ⟨_, hbr, by simp [reta], by simp [psa, ispSpec, h2], by simp [vva], ?_, ?_, by simp [wka]⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at ca ⊢; omega
    · simp [gS_mem_len, gS_bs_len, vwp, NExpr.nodes, NExpr.scalarOnly] at na ⊢; omega
  · rw [if_neg h2] at c1
    have c2 := cond2_den mv vv P [cu n, cb true] n hnm e0
    have inner : ∃ ri : PRM, pexecM mv fu (.branch (cond2E mv.nv) (assign1 mv.nv 0) (blk (else2 mv.nv))) (gS P [cu n, cb true]) vv = some ri ∧
        ri.ret = none ∧ ri.ps = gS P [cu n, cb (ispSpec n)] ∧ ri.vv = vv ∧ ri.cost ≤ TOPC - 100 ∧ ri.need ≤ P.length + 2 * 60 + 1000 ∧
        ri.wk = 0 := by
      by_cases h3 : n % 2 = 0 ∨ n ≤ 1
      · rw [if_pos h3] at c2
        obtain ⟨ra, ha1, reta, psa, vva, ca, na, wka⟩ := assign1_exec mv P n true false vv fu
        have hbr := pexecM_branch_true mv fu _ (assign1 mv.nv 0) (blk (else2 mv.nv)) _ _ 1 c2 (by decide) _ ha1
        refine ⟨_, hbr, by simp [reta], by simp [psa, ispSpec, h2, h3], by simp [vva], ?_, ?_, by simp [wka]⟩
        · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at ca ⊢; omega
        · simp [gS_mem_len, gS_bs_len, vwp, NExpr.nodes, NExpr.scalarOnly] at na ⊢; omega
      · rw [if_neg h3] at c2
        have h3n : 3 ≤ n := by omega
        obtain ⟨re, he1, rete, pse, vve, ce, ne_, wke⟩ := else2_exec mv P n h3n hnm vv fu hfu
        have hsc := pexecM_scope mv fu _ _ _ _ he1
        have tk := gS_takeC P [cu n, cb true] [cu n, cb (ispF n)] [cI (dloop 64 (n - 1) 0).2, cu (dloop 64 (n - 1) 0).1] (by simp)
        have hD : ([cu n, cb (ispF n)] ++ [cI (dloop 64 (n - 1) 0).2, cu (dloop 64 (n - 1) 0).1] : List Cell) =
            Dc n (ispF n) (dloop 64 (n - 1) 0).2 (dloop 64 (n - 1) 0).1 := by simp
        rw [hD] at tk
        have hb := seqM_some hsc (by simp [rete]) (pexecM_skip mv fu _ _)
        have hbr := pexecM_branch_false mv fu _ (assign1 mv.nv 0) (blk (else2 mv.nv)) _ _ c2 _ hb
        refine ⟨_, hbr, by simp [rete], ?_, by simp [vve], ?_, ?_, by simp [wke]⟩
        · simp only [pse]; rw [tk]; simp [ispSpec, h2, h3]
        · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at ce ⊢
          omega
        · simp [pse, gS_mem_len, gS_bs_len, vwp, NExpr.nodes, NExpr.scalarOnly] at ne_ ⊢; omega
    obtain ⟨ri, hi1, reti, psi, vvi, ci_, ni, wki⟩ := inner
    have hb := seqM_some hi1 reti (pexecM_skip mv fu _ _)
    have hsc := pexecM_scope mv fu _ _ _ _ hb
    rw [psi, scope_same P _ _ (by simp)] at hsc
    have hfin := seqM_some hsc (by simp) (pexecM_skip mv fu _ _)
    have hbr := pexecM_branch_false mv fu _ (assign1 mv.nv 1) (topElse mv.nv) _ _ c1 _ hfin
    refine ⟨_, hbr, by simp [reti], by simp [psi], by simp [vvi], ?_, ?_, by simp [wki]⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at ci_ ⊢
      omega
    · simp [gS_mem_len, gS_bs_len, vwp, NExpr.nodes, NExpr.scalarOnly] at ni ⊢; omega


set_option maxHeartbeats 64000000 in
theorem top_exec (mv : MV) (P : List Cell) (n : Nat) (hnm : n < M64) (vv : Nat → List Int) (fu : Nat) (hfu : 400 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (isBodyT mv.nv) (gS P [cu n]) vv = some res ∧
      res.ret = some (if ispSpec n then 1 else 0) ∧ res.vv = vv ∧ (∃ cl : List Cell, res.ps = gS P cl) ∧
      res.cost ≤ TOPC + 200 ∧ res.need ≤ P.length + 2 * 60 + 1000 ∧ res.wk = 0 := by
  have d1 := gSM_decl mv P [cu n] vv bT (.literal bT 1) 1 1
    (by rw [vdenM_scalar _ _ _ _ rfl]; rw [den_literal, if_pos (show bT.valid 1 = true from rfl)])
    (show bT.convert 1 = some 1 from rfl)
  have a1 := (pexecM_prim mv fu (.declare bT true (.literal bT 1)) _ _).trans d1
  have hcl : [cu n] ++ [(⟨bT, 1⟩ : Cell)] = [cu n, cb true] := by simp [cb]
  rw [hcl] at a1
  obtain ⟨rm, hm, retm, psm, vvm, cm, nm, wkm⟩ := top_mid mv P n hnm vv fu hfu
  have g1 : ([cu n, cb (ispSpec n)] : List Cell)[1]? = some (cb (ispSpec n)) := by simp
  have rv := varb_den mv P [cu n, cb (ispSpec n)] 1 (ispSpec n) g1
  have rr := pstmtM_ret_ok mv (gS P [cu n, cb (ispSpec n)]) vv (bV mv.nv 1) (if ispSpec n then 1 else 0)
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact rv)
  have e3 := seqM_ret (b := Sk) ((pexecM_prim mv fu _ _ _).trans rr) rfl
  have s2 := seqM_some hm retm (by rw [psm, vvm]; exact e3)
  have s1 := seqM_some a1 rfl (by exact s2)
  refine ⟨_, s1, by simp, by simp, ⟨[cu n, cb (ispSpec n)], by simp⟩, ?_, ?_, by simp [wkm]⟩
  · simp [vwp, NExpr.nodes] at cm ⊢
    have hT : TOPC = TOPC := rfl
    omega
  · simp [gS_mem_len, gS_bs_len, vwp, NExpr.nodes] at nm ⊢; omega

end Proofs.IsPrimeRun
