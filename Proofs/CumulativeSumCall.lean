import Proofs.FenwickRangeCall
import Proofs.CumulativeSumExec
import Proofs.FenwickTreeVecCall
import Proofs.Generated.CumulativeSum

namespace Proofs.CumulativeSumCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.StraightLine Proofs.Mod61Body Proofs.VecExpr Proofs.VecStraight Proofs.VecCall Proofs.VecKit
open Proofs.CppNestedFacts Proofs.IntSim Proofs.ScalarCall Proofs.VecWrite Proofs.VecWriteCall Proofs.VecKitW
open Proofs.QuotientSearch Proofs.VectorFillCall Proofs.PrefixSumsCall Proofs.FenwickMath
open Proofs.VectorSumCall (conv_signed i32_valid)
open Proofs.CppState (Cell)
open Proofs.PowModStep (Sk)
open Proofs.FenwickRangeCall (R0 LocT envT R0_loc0 R0_loc1)

-- Sum of the elements [a, b) from the prefix sums.
theorem pre_diff (A : List Int) (a b : Nat) (hab : a ≤ b) : pre A b - pre A a = ((A.drop a).take (b - a)).sum := by
  unfold pre
  have : b = a + (b - a) := by omega
  conv_lhs => rw [this, List.take_add, List.sum_append]
  omega


abbrev ck1 : NExpr := .binary bT .le (.literal i32 0) (.variable i32 1)
abbrev ck2 : NExpr := .binary bT .le (.variable i32 1) (.variable i32 2)
abbrev ckSz (k : Nat) : NExpr := .binary bT .lt (.variable i32 k) (.cast i32 (.size (.integer s64) (.local 0)))
abbrev retR : NExpr := .binary s64 .sub (.read s64 (.local 0) (.cast u64 (.variable i32 2)))
  (.read s64 (.local 0) (.cast u64 (.variable i32 1)))
abbrev retP : NExpr := .read s64 (.local 0) (.cast u64 (.variable i32 1))
abbrev bodyR : Command := .sequence (.primitive (.check ck1)) (.sequence (.primitive (.check ck2))
  (.sequence (.primitive (.check (ckSz 2))) (.sequence (.primitive (.ret retR)) Sk)))
abbrev bodyP : Command := .sequence (.primitive (.check ck1)) (.sequence (.primitive (.check (ckSz 1)))
  (.sequence (.primitive (.ret retP)) Sk))

theorem body_eqR : Proofs.CumulativeSumInstance.CumulativeSum_long_long_sum_2.body = bodyR := rfl
theorem body_eqP : Proofs.CumulativeSumInstance.CumulativeSum_long_long_sum_1.body = bodyP := rfl

theorem bool_one : bT.convert 1 = some 1 := by simp only [bT]; unfold Ty.convert; simp [Ty.valid]

theorem ck1_val (vec : List Int) (env : Nat → Ty → Option Int) (a : Nat) (e1 : env 1 i32 = some (a : Int)) :
    vdenL s64 vec env ck1 = some 1 := by
  rw [vdenL_scalar _ _ _ _ rfl, den_binary, den_literal, if_pos (show i32.valid 0 = true from rfl), den_variable, e1]
  simp only [Option.bind_some]
  have : binaryValue .le (0 : Int) (a : Int) = 1 := by simp [binaryValue]
  rw [this]; exact bool_one

theorem ck2_val (vec : List Int) (env : Nat → Ty → Option Int) (a b : Nat) (e1 : env 1 i32 = some (a : Int))
    (e2 : env 2 i32 = some (b : Int)) (hab : a ≤ b) : vdenL s64 vec env ck2 = some 1 := by
  rw [vdenL_scalar _ _ _ _ rfl, den_binary, den_variable, den_variable, e1, e2]
  simp only [Option.bind_some]
  have : binaryValue .le (a : Int) (b : Int) = 1 := by simp [binaryValue]; omega
  rw [this]; exact bool_one

theorem ckSz_val (vec : List Int) (env : Nat → Ty → Option Int) (k b : Nat) (hn : vec.length < 2147483648)
    (e : env k i32 = some (b : Int)) (hb : b < vec.length) : vdenL s64 vec env (ckSz k) = some 1 := by
  have hc : (ckSz k).scalarOnly = false := rfl
  have hr2 : (NExpr.cast i32 (.size (.integer s64) (.local 0))).scalarOnly = false := rfl
  have hn' : i32.convert (vec.length : Int) = some (vec.length : Int) :=
    conv_signed i32 rfl rfl _ (i32_valid _ (by omega) (by omega))
  have hr : (NExpr.size (.integer s64) (.local 0)).scalarOnly = false := rfl
  have hsz : vdenL s64 vec env (.size (.integer s64) (.local 0)) = some (vec.length : Int) := by
    simp [vdenL, hr]
  rw [vdenL_binary s64 vec env bT .lt (.variable i32 k) _ hc, vdenL_cast s64 vec _ _ _ hr2, hsz, Option.bind_some, hn',
    vdenL_scalar _ _ _ _ rfl, den_variable, e, Option.bind_some, Option.bind_some]
  have : binaryValue .lt (b : Int) (vec.length : Int) = 1 := by simp [binaryValue]; omega
  rw [this]; exact bool_one


theorem R0_envs (P : List Cell) (a b : Nat) (ha : a < 2147483648) (hb : b < 2147483648) :
    penv1 (R0 P a b) 1 i32 = some (a : Int) ∧ penv1 (R0 P a b) 2 i32 = some (b : Int) :=
  ⟨envT _ 0 _ i32 _ (R0_loc0 P a b) (i32_valid a (by omega) (by omega)),
   envT _ 1 _ i32 _ (R0_loc1 P a b) (i32_valid b (by omega) (by omega))⟩

theorem body_exec_range (P : List Cell) (vec : List Int) (a b : Nat) (hn : vec.length < 2147483648)
    (hab : a ≤ b) (hb : b < vec.length) (hel : ∀ y ∈ vec, s64.valid y = true)
    (hd : s64.valid (vec.getD b 0 - vec.getD a 0) = true) (fu : Nat) :
    ∃ r, pexecW s64 fu bodyR (R0 P a b) vec = some r ∧ r.ret = some (vec.getD b 0 - vec.getD a 0) ∧ r.vec = vec ∧
      r.cost ≤ 60 ∧ r.need ≤ P.length + 60 ∧ r.wk = 0 ∧ r.ps = R0 P a b := by
  have hA : a < vec.length := by omega
  obtain ⟨e1, e2⟩ := R0_envs P a b (by omega) (by omega)
  have c1 := pstmtW_check_ok s64 (R0 P a b) vec ck1 1 (ck1_val vec _ a e1) (by decide)
  have c2 := pstmtW_check_ok s64 (R0 P a b) vec ck2 1 (ck2_val vec _ a b e1 e2 hab) (by decide)
  have c3 := pstmtW_check_ok s64 (R0 P a b) vec (ckSz 2) 1 (ckSz_val vec _ 2 b hn e2 hb) (by decide)
  obtain ⟨xa, hxa⟩ : ∃ x, vec[a]? = some x := ⟨vec[a], by simp [hA]⟩
  obtain ⟨xb, hxb⟩ : ∃ x, vec[b]? = some x := ⟨vec[b], by simp [hb]⟩
  have ga := hel xa (List.mem_of_getElem? hxa)
  have gb := hel xb (List.mem_of_getElem? hxb)
  have hga : vec.getD a 0 = xa := by simp [List.getD_eq_getElem?_getD, hxa]
  have hgb : vec.getD b 0 = xb := by simp [List.getD_eq_getElem?_getD, hxb]
  rw [hga, hgb] at hd
  have ia := Proofs.FenwickRangeCall.envT (R0 P a b) 0 P.length i32 (a : Int) (R0_loc0 P a b)
    (i32_valid a (by omega) (by omega))
  have idxa : (NExpr.cast u64 (.variable i32 1)).denote (penv1 (R0 P a b)) = some (a : Int) := by
    rw [den_cast]
    show ((penv1 (R0 P a b)) 1 i32).bind u64.convert = _
    rw [e1, Option.bind_some, convert_u64]
    simp; exact Int.emod_eq_of_lt (by omega) (by omega)
  have idxb : (NExpr.cast u64 (.variable i32 2)).denote (penv1 (R0 P a b)) = some (b : Int) := by
    rw [den_cast]
    show ((penv1 (R0 P a b)) 2 i32).bind u64.convert = _
    rw [e2, Option.bind_some, convert_u64]
    simp; exact Int.emod_eq_of_lt (by omega) (by omega)
  have hbn : retR.scalarOnly = false := rfl
  have rda : vdenL s64 vec (penv1 (R0 P a b)) (.read s64 (.local 0) (.cast u64 (.variable i32 1))) = some xa := by
    rw [vdenL_read _ _ _ _ _ rfl, if_pos ⟨rfl, rfl⟩, idxa, Option.bind_some]
    simp [elemAtL, hxa, ga]
  have rdb : vdenL s64 vec (penv1 (R0 P a b)) (.read s64 (.local 0) (.cast u64 (.variable i32 2))) = some xb := by
    rw [vdenL_read _ _ _ _ _ rfl, if_pos ⟨rfl, rfl⟩, idxb, Option.bind_some]
    simp [elemAtL, hxb, gb]
  have rv : vdenL s64 vec (penv1 (R0 P a b)) retR = some (xb - xa) := by
    rw [vdenL_binary _ _ _ _ _ _ _ hbn, rdb, rda, Option.bind_some, Option.bind_some]
    have : binaryValue .sub xb xa = xb - xa := rfl
    rw [this]; exact convS _ hd
  have rs := pstmtW_ret_ok s64 (R0 P a b) vec retR (xb - xa) rv
  have t4 := seqW_ret (b := Sk) ((pexecW_prim s64 fu (.ret retR) _ _).trans rs) rfl
  have t3 := seqW_some ((pexecW_prim s64 fu _ _ _).trans c3) rfl t4
  have t2 := seqW_some ((pexecW_prim s64 fu _ _ _).trans c2) rfl t3
  have t1 := seqW_some ((pexecW_prim s64 fu _ _ _).trans c1) rfl t2
  refine ⟨_, t1, ?_, rfl, ?_, ?_, rfl, rfl⟩
  · rw [hga, hgb]
  · simp [vwp, NExpr.nodes, Container.nodes]
  · simp [vwp, NExpr.nodes, Container.nodes, R0]


theorem body_exec_prefix (P : List Cell) (vec : List Int) (a : Nat) (hn : vec.length < 2147483648)
    (ha : a < vec.length) (hel : ∀ y ∈ vec, s64.valid y = true) (fu : Nat) :
    ∃ r, pexecW s64 fu bodyP (stI P a) vec = some r ∧ r.ret = some (vec.getD a 0) ∧ r.vec = vec ∧
      r.cost ≤ 60 ∧ r.need ≤ P.length + 60 ∧ r.wk = 0 ∧ r.ps = stI P a := by
  have e1 := env_i1 P a (i32_valid a (by omega) (by omega))
  have c1 := pstmtW_check_ok s64 (stI P a) vec ck1 1 (ck1_val vec _ a e1) (by decide)
  have c2 := pstmtW_check_ok s64 (stI P a) vec (ckSz 1) 1 (ckSz_val vec _ 1 a hn e1 ha) (by decide)
  obtain ⟨xa, hxa⟩ : ∃ x, vec[a]? = some x := ⟨vec[a], by simp [ha]⟩
  have ga := hel xa (List.mem_of_getElem? hxa)
  have hga : vec.getD a 0 = xa := by simp [List.getD_eq_getElem?_getD, hxa]
  have rda : vdenL s64 vec (penv1 (stI P a)) retP = some xa := by
    rw [vdenL_read _ _ _ _ _ rfl, if_pos ⟨rfl, rfl⟩, idxcur vec P a (by omega), Option.bind_some]
    simp [elemAtL, hxa, ga]
  have rs := pstmtW_ret_ok s64 (stI P a) vec retP xa rda
  have t3 := seqW_ret (b := Sk) ((pexecW_prim s64 fu (.ret retP) _ _).trans rs) rfl
  have t2 := seqW_some ((pexecW_prim s64 fu _ _ _).trans c2) rfl t3
  have t1 := seqW_some ((pexecW_prim s64 fu _ _ _).trans c1) rfl t2
  refine ⟨_, t1, ?_, rfl, ?_, ?_, rfl, rfl⟩
  · rw [hga]
  · simp [vwp, NExpr.nodes, Container.nodes]
  · simp [vwp, NExpr.nodes, Container.nodes, stI]


set_option maxHeartbeats 4000000 in
theorem cum_sum_range_correct (caller : NState) {vslot vb V vsc : Nat} {m : Bool} {vbuf : Buffer Value}
    (ok : Proofs.VectorSumCall.VOK caller vslot vb V vsc m vbuf) (vec : List Int)
    (hitems : vbuf.items = vec.map Value.integer) (hn : vec.length < 2147483648)
    (hbvalid : vbuf.Valid (accepts (.integer s64))) (hlimit : vbuf.limit = CppVectorBindings.sizeLimit s64)
    (howner : vbuf.owner = V)
    (e1 e2 : NExpr) (a b : Nat) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ht1 : e1.resultType = i32) (ht2 : e2.resultType = i32)
    (value1 : e1.denote (envOf caller) = some (a : Int)) (value2 : e2.denote (envOf caller) = some (b : Int))
    (hab : a ≤ b) (hb : b < vec.length) (hel : ∀ y ∈ vec, s64.valid y = true)
    (hd : s64.valid (vec.getD b 0 - vec.getD a 0) = true) :
    ∃ Sinit fuel res, prepare caller Proofs.CumulativeSumInstance.CumulativeSum_long_long_sum_2.parameters
        [.vectorReference vslot,.value e1,.value e2] = some Sinit ∧
      Proofs.CumulativeSumInstance.CumulativeSum_long_long_sum_2.callFuel fuel caller [.vectorReference vslot,.value e1,.value e2] =
        .finished (res,.scalar (vec.getD b 0 - vec.getD a 0)) ∧
      ScalarPost3 caller Sinit res (e1.nodes+e2.nodes) 120 caller.scalars.memory 0 V vec := by
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    Proofs.FenwickRangeCall.prepare_frr caller ok e1 e2 (a : Int) (b : Int) hs1 hs2 ht1 ht2 value1 value2
      (i32_valid a (by omega) (by omega)) (i32_valid b (by omega) (by omega))
  let vc : VCtx := ⟨s64,false,m,V,vsc,vbuf,vec,hitems,fun h => absurd h (by decide),by omega,
    caller.frame.state.liveSpace,caller.frame.state.storage.work,caller.scope+1,
    caller.frame.state.storage.objects.length⟩
  have fwS : FW vc vec vbuf 0 Sinit.frame := by
    rw [sFrame]
    refine ⟨ok.valid,ok.lengths,rfl,rfl,?_,rfl,rfl,ok.vtag,ok.vfound,ok.flag,hitems,hbvalid,hlimit,howner,by omega⟩
    intro owner k h
    have := ok.strict owner k h
    show k < caller.scope+1
    omega
  obtain ⟨rr,hexec,hret,hrvec,hcost,hneed,hwk,hps⟩ := body_exec_range (callerP caller) vec a b hn hab hb hel hd 1
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have gw1 := good.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1
  have hpost := call_vecw vc false (fun h => absurd h (by decide)) caller Proofs.CumulativeSumInstance.CumulativeSum_long_long_sum_2
    [.vectorReference vslot,.value e1,.value e2] Sinit
    (callerP caller ++ [(⟨i32,(a : Int)⟩ : Cell),⟨i32,(b : Int)⟩])
    [(⟨(callerP caller).length,true⟩ : CppState.Binding),⟨(callerP caller).length+1,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [VectorFillCall.take_P caller]) ok.base (by decide) 1 rr
    (by rw [body_eqR]; exact hexec) _ hret s64 rfl hd (by omega) (by simp) (e1.nodes+e2.nodes) 120 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hps]; exact VectorFillCall.take_P caller _
  rw [hs', hrvec, hwk] at post
  exact post

set_option maxHeartbeats 4000000 in
theorem cum_sum_prefix_correct (caller : NState) {vslot vb V vsc : Nat} {m : Bool} {vbuf : Buffer Value}
    (ok : Proofs.VectorSumCall.VOK caller vslot vb V vsc m vbuf) (vec : List Int)
    (hitems : vbuf.items = vec.map Value.integer) (hn : vec.length < 2147483648)
    (hbvalid : vbuf.Valid (accepts (.integer s64))) (hlimit : vbuf.limit = CppVectorBindings.sizeLimit s64)
    (howner : vbuf.owner = V)
    (e : NExpr) (a : Nat) (hs : e.scalarOnly = true) (ht : e.resultType = i32)
    (value : e.denote (envOf caller) = some (a : Int)) (ha : a < vec.length)
    (hel : ∀ y ∈ vec, s64.valid y = true) :
    ∃ Sinit fuel res, prepare caller Proofs.CumulativeSumInstance.CumulativeSum_long_long_sum_1.parameters
        [.vectorReference vslot,.value e] = some Sinit ∧
      Proofs.CumulativeSumInstance.CumulativeSum_long_long_sum_1.callFuel fuel caller [.vectorReference vslot,.value e] =
        .finished (res,.scalar (vec.getD a 0)) ∧
      ScalarPost3 caller Sinit res e.nodes 120 caller.scalars.memory 0 V vec := by
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    Proofs.FenwickCall.prepare_fs caller ok e (a : Int) hs ht value (i32_valid a (by omega) (by omega))
  let vc : VCtx := ⟨s64,false,m,V,vsc,vbuf,vec,hitems,fun h => absurd h (by decide),by omega,
    caller.frame.state.liveSpace,caller.frame.state.storage.work,caller.scope+1,
    caller.frame.state.storage.objects.length⟩
  have fwS : FW vc vec vbuf 0 Sinit.frame := by
    rw [sFrame]
    refine ⟨ok.valid,ok.lengths,rfl,rfl,?_,rfl,rfl,ok.vtag,ok.vfound,ok.flag,hitems,hbvalid,hlimit,howner,by omega⟩
    intro owner k h
    have := ok.strict owner k h
    show k < caller.scope+1
    omega
  obtain ⟨rr,hexec,hret,hrvec,hcost,hneed,hwk,hps⟩ := body_exec_prefix (callerP caller) vec a hn ha hel 1
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have gw1 := good.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1
  obtain ⟨xa, hxa⟩ : ∃ x, vec[a]? = some x := ⟨vec[a], by simp [ha]⟩
  have hga : vec.getD a 0 = xa := by simp [List.getD_eq_getElem?_getD, hxa]
  have hres : s64.valid (vec.getD a 0) = true := by rw [hga]; exact hel xa (List.mem_of_getElem? hxa)
  have hpost := call_vecw vc false (fun h => absurd h (by decide)) caller Proofs.CumulativeSumInstance.CumulativeSum_long_long_sum_1
    [.vectorReference vslot,.value e] Sinit
    (callerP caller ++ [(⟨i32,(a : Int)⟩ : Cell)]) [(⟨(callerP caller).length,true⟩ : CppState.Binding)]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [VectorFillCall.take_P caller]) ok.base (by decide) 1 rr
    (by rw [body_eqP]; exact hexec) _ hret s64 rfl hres (by omega) (by simp) e.nodes 120 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hps]; simp only [stI]; exact VectorFillCall.take_P caller _
  rw [hs', hrvec, hwk] at post
  exact post

-- With the prefix sums of `A` the result of `cum_sum_range` is the sum of `A[a, b)`.
theorem cum_sum_range_value (A cs : List Int) (hcs : ∀ i, i ≤ A.length → cs.getD i 0 = pre A i) (a b : Nat)
    (hab : a ≤ b) (hb : b ≤ A.length) : cs.getD b 0 - cs.getD a 0 = ((A.drop a).take (b - a)).sum := by
  rw [hcs b hb, hcs a (by omega)]
  exact pre_diff A a b hab

open Proofs.MultiVec Proofs.MultiVecCall Proofs.MultiKit Proofs.FenwickTreeVecCall Proofs.CumulativeSumExec Proofs.MatMulPrepare Proofs.FenwickTreeExec Proofs.GenState in
set_option maxHeartbeats 4000000 in
/-- `CumulativeSum<long long>(v)` fills the field `cs` (already `v.size() + 1` elements long by the standard constructor)
with the prefix sums of `v`. -/
theorem cumulative_sum_from_vector_correct (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {m1 : Bool}
    {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 false m1 vbuf1)
    (h10 : V1 ≠ V0) (T0 V : List Int) (n : Nat) (hn : n < 2147483646) (hV : V.length = n) (hT : T0.length = n + 1)
    (hpre : ∀ q, q ≤ n → s64.valid (pre V q) = true)
    (i0 : vbuf0.items = T0.map Value.integer) (i1 : vbuf1.items = V.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer s64))) (bv1 : vbuf1.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit s64)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState) (X : List Int),
      prepare caller Proofs.CumulativeSumInstance.CumulativeSum_long_long_new0.parameters
        [.vectorReference s0,.vectorReference s1] = some Sinit ∧
      Proofs.CumulativeSumInstance.CumulativeSum_long_long_new0.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1] = .finished (res,Ret.unit) ∧
      X.length = n + 1 ∧ (∀ q, q ≤ n → X.getD q 0 = pre V q) ∧
      ScalarPostM (mvFT V0 V1 vsc0 vsc1 m1 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h10)
        caller Sinit res 0 (220 * n + 200) caller.scalars.memory (n + 1) (VFT X V) := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ := prepare_ft caller ok0 ok1
  have fwS := fwFT_init caller ok0 ok1 h10 T0 V (by omega) (by omega) i0 i1 bv0 bv1 l0 l1 o0 o1
  rw [← sFrame] at fwS
  have hVv := items_valid vbuf1 V s64 i1 bv1
  obtain ⟨rr,X,hexec,hret,hrps,hrvv,hXl,hXs,hcost,hneed,hwk⟩ :=
    body_execC (mvFT V0 V1 vsc0 vsc1 m1 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h10) rfl (by simp [mvFT]) (by simp [mvFT])
      (n + 1) (callerP caller) T0 V n (by omega) hV hT hVv hpre (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have hmk : (⟨callerP caller, []⟩ : PS) = gS (callerP caller) [] := by simp [gS]
  have hpost := call_vecm_unit (mvFT V0 V1 vsc0 vsc1 m1 caller.frame.state.liveSpace
        caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h10)
    (fun k => decide (k = 0))
    (by intro k hk; have : k = 0 := by simpa using hk
        subst this; simp [mvFT])
    caller Proofs.CumulativeSumInstance.CumulativeSum_long_long_new0
    [.vectorReference s0,.vectorReference s1] Sinit (callerP caller) []
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]) (by simp [callerP]) ok0.base (by decide)
    (n + 1) rr (by rw [hmk, body_eqC]; exact hexec) hret rfl (by omega)
    (by simp [hlenP]) 0 (220 * n + 200) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,X,hprep,hrun,hXl,hXs,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk

end Proofs.CumulativeSumCall
