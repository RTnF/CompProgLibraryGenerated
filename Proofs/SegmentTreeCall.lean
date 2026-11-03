import Proofs.SegmentTreePrepare
import Proofs.SegmentTreeSet
import Proofs.SegmentTreeProduct
import Proofs.SegmentTreeGet
import Proofs.SegmentTreeCtor
import Proofs.SegmentTreeMinPrepare
import Proofs.SegmentTreeMinSet
import Proofs.SegmentTreeMinProduct
import Proofs.SegmentTreeMinGet
import Proofs.SegmentTreeMinCtor
import Proofs.InvGcdCall
import Proofs.MultiVecCall

namespace Proofs.SegmentTreeCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCall
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (cs)
open Proofs.InvGcdExec (VO)
open Proofs.InvGcdCall (mvIG fwIG_init)
open Proofs.SegTreeMath
open Proofs.SegmentTreeExec (maxMon mx)

theorem wr_bodySet : WrM (fun _ => true) (Proofs.SegmentTreeSet.bodySet 1) = true := by decide

set_option maxHeartbeats 16000000 in
/-- `SegmentTree::set(idx, val)` on the tree stored in `node`: afterwards `node` is again a tree. -/
theorem segtree_set_correct (caller : NState) {s0 vb0 V0 vsc0 : Nat} {vbuf0 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (V : List Int) (n N h idx : Nat) (val : Int)
    (hN : N = 2 ^ h) (hn : n < 2147483648) (hh30 : h ≤ 30) (hidx : idx < N) (hT : TInv maxMon V N) (hV : AllV maxMon V)
    (hval : s64.valid val = true) (hV2 : V.length < 2147483647)
    (i0 : vbuf0.items = V.map Value.integer) (bv0 : vbuf0.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (o0 : vbuf0.owner = V0)
    (e1 e2 e3 e4 e5 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true)
    (hs4 : e4.scalarOnly = true) (hs5 : e5.scalarOnly = true)
    (ty1 : e1.resultType = i32) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32) (ty4 : e4.resultType = i32)
    (ty5 : e5.resultType = s64)
    (value1 : e1.denote (envOf caller) = some (n : Int)) (value2 : e2.denote (envOf caller) = some (N : Int))
    (value3 : e3.denote (envOf caller) = some (h : Int)) (value4 : e4.denote (envOf caller) = some (idx : Int))
    (value5 : e5.denote (envOf caller) = some val) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.SegmentTreeInstance.SegmentTree_cp__SegMax_long_long__long_long_set.parameters
        [.vectorReference s0,.value e1,.value e2,.value e3,.value e4,.value e5] = some Sinit ∧
      Proofs.SegmentTreeInstance.SegmentTree_cp__SegMax_long_long__long_long_set.callFuel fuel caller
        [.vectorReference s0,.value e1,.value e2,.value e3,.value e4,.value e5] = .finished (res,Ret.unit) ∧
      ∃ Vf : List Int, TInv maxMon Vf N ∧ AllV maxMon Vf ∧ Vf.length = 2 * N ∧ Vf.getD (idx + N) 0 = val ∧
        (∀ j, N ≤ j → j ≠ idx + N → Vf.getD j 0 = V.getD j 0) ∧
        ScalarPostM (mvIG V0 vsc0 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
          caller.frame.state.storage.objects.length)
          caller Sinit res (e1.nodes + e2.nodes + e3.nodes + e4.nodes + e5.nodes) (900 * h + 600) caller.scalars.memory (h + 1)
          (VO Vf) := by
  have hn31 : n < 2147483648 := hn
  have h30 : 2 ^ 30 = 1073741824 := by norm_num
  have hN30 : N ≤ 1073741824 := by rw [hN, ← h30]; exact Nat.pow_le_pow_right (by decide) hh30
  have hlenV := hT.2.1
  obtain ⟨t1,t2,t3,t4,t5,g1,g2,g3,g4,g5,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    Proofs.SegmentTreePrepare.prepare_set caller ok0 e1 e2 e3 e4 e5 (n : Int) (N : Int) (h : Int) (idx : Int) val hs1 hs2 hs3 hs4 hs5
      ty1 ty2 ty3 ty4 ty5 value1 value2 value3 value4 value5 (validN n hn31) (validN N (by omega)) (validN h (by omega))
      (validN idx (by omega)) hval
  have fwS := fwIG_init caller ok0 V hV2 i0 bv0 l0 o0
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,⟨cl,hrps⟩,Vf,hrvv,hTf,hVf,hlenf,hleaf,hothers,hcost,hneed,hwk⟩ :=
    Proofs.SegmentTreeSet.body_execSet (mvIG V0 vsc0 caller.frame.state.liveSpace caller.frame.state.storage.work
      (caller.scope + 1) caller.frame.state.storage.objects.length) rfl rfl (callerP caller) n N h idx val V hN hn hh30 hidx hT hV hval
    (h + 3) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,(N : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(idx : Int)⟩,⟨s64,val⟩]).take
      caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,(N : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(idx : Int)⟩,⟨s64,val⟩],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,
       ⟨(callerP caller).length+3,true⟩,⟨(callerP caller).length+4,true⟩]⟩ : PS) =
      gS (callerP caller) [ci n, ci N, ci h, ci idx, cs val] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  have gw2 := g2.2.2.1
  have gw3 := g3.2.2.1
  have gw4 := g4.2.2.1
  have gw5 := g5.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1 gw2 gw3 gw4 gw5
  have hpost := call_vecm_unit (mvIG V0 vsc0 caller.frame.state.liveSpace
      caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length)
    (fun _ => true) (by intro k hk; exact ⟨rfl, rfl⟩)
    caller Proofs.SegmentTreeInstance.SegmentTree_cp__SegMax_long_long__long_long_set
    [.vectorReference s0,.value e1,.value e2,.value e3,.value e4,.value e5] Sinit
    (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,(N : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(idx : Int)⟩,⟨s64,val⟩])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,
       ⟨(callerP caller).length+3,true⟩,⟨(callerP caller).length+4,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [Proofs.SegmentTreeSet.body_eqSet]; exact wr_bodySet)
    (h + 3) rr (by rw [hmk, Proofs.SegmentTreeSet.body_eqSet]; exact hexec) hret rfl (by omega) (by simp [hlenP])
    (e1.nodes + e2.nodes + e3.nodes + e4.nodes + e5.nodes) (900 * h + 600) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,Vf,hTf,hVf,hlenf,hleaf,hothers,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk

theorem wr_bodyAny (b : Command) (h : WrM (fun _ => true) b = true) : WrM (fun _ => true) b = true := h

set_option maxHeartbeats 16000000 in
/-- `SegmentTree::get(idx)`: the leaf `node[idx + n_node]`. -/
theorem segtree_get_correct (caller : NState) {s0 vb0 V0 vsc0 : Nat} {vbuf0 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (V : List Int) (n N h idx : Nat)
    (hn : n < 2147483648) (hN : N < 2147483648) (hh : h < 2147483648) (hidx : idx + N < 2147483648)
    (hlt : idx + N < V.length) (hv : s64.valid (V.getD (idx + N) 0) = true) (hV2 : V.length < 2147483647)
    (i0 : vbuf0.items = V.map Value.integer) (bv0 : vbuf0.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (o0 : vbuf0.owner = V0)
    (e1 e2 e3 e4 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true)
    (hs4 : e4.scalarOnly = true)
    (ty1 : e1.resultType = i32) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32) (ty4 : e4.resultType = i32)
    (value1 : e1.denote (envOf caller) = some (n : Int)) (value2 : e2.denote (envOf caller) = some (N : Int))
    (value3 : e3.denote (envOf caller) = some (h : Int)) (value4 : e4.denote (envOf caller) = some (idx : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.SegmentTreeInstance.SegmentTree_cp__SegMax_long_long__long_long_get.parameters
        [.vectorReference s0,.value e1,.value e2,.value e3,.value e4] = some Sinit ∧
      Proofs.SegmentTreeInstance.SegmentTree_cp__SegMax_long_long__long_long_get.callFuel fuel caller
        [.vectorReference s0,.value e1,.value e2,.value e3,.value e4] = .finished (res,.scalar (V.getD (idx + N) 0)) ∧
      ScalarPostM (mvIG V0 vsc0 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
          caller.frame.state.storage.objects.length)
          caller Sinit res (e1.nodes + e2.nodes + e3.nodes + e4.nodes) 100 caller.scalars.memory 0 (VO V) := by
  obtain ⟨t1,t2,t3,t4,g1,g2,g3,g4,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    Proofs.SegmentTreePrepare.prepare_get caller ok0 e1 e2 e3 e4 (n : Int) (N : Int) (h : Int) (idx : Int) hs1 hs2 hs3 hs4
      ty1 ty2 ty3 ty4 value1 value2 value3 value4 (validN n hn) (validN N hN) (validN h hh) (validN idx (by omega))
  have fwS := fwIG_init caller ok0 V hV2 i0 bv0 l0 o0
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrvv,⟨cl,hrps⟩,hcost,hneed,hwk⟩ :=
    Proofs.SegmentTreeGet.body_execGet (mvIG V0 vsc0 caller.frame.state.liveSpace caller.frame.state.storage.work
      (caller.scope + 1) caller.frame.state.storage.objects.length) rfl rfl (callerP caller) n N h idx V hn hN hh hidx hlt hv 2
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,(N : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(idx : Int)⟩]).take
      caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,(N : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(idx : Int)⟩],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,
       ⟨(callerP caller).length+3,true⟩]⟩ : PS) = gS (callerP caller) [ci n, ci N, ci h, ci idx] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  have gw2 := g2.2.2.1
  have gw3 := g3.2.2.1
  have gw4 := g4.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1 gw2 gw3 gw4
  have hpost := call_vecm (mvIG V0 vsc0 caller.frame.state.liveSpace
      caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length)
    (fun _ => true) (by intro k hk; exact ⟨rfl, rfl⟩)
    caller Proofs.SegmentTreeInstance.SegmentTree_cp__SegMax_long_long__long_long_get
    [.vectorReference s0,.value e1,.value e2,.value e3,.value e4] Sinit
    (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,(N : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(idx : Int)⟩])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,
       ⟨(callerP caller).length+3,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [Proofs.SegmentTreeGet.body_eqGet]; decide)
    2 rr (by rw [hmk, Proofs.SegmentTreeGet.body_eqGet]; exact hexec) _ hret s64 rfl hv (by omega) (by simp [hlenP])
    (e1.nodes + e2.nodes + e3.nodes + e4.nodes) 100 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) (by omega)

set_option maxHeartbeats 16000000 in
/-- `SegmentTree::product(l, r)`: the product of the leaves `[l, r)`. -/
theorem segtree_product_correct (caller : NState) {s0 vb0 V0 vsc0 : Nat} {vbuf0 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (V : List Int) (n N h l0 r0 : Nat)
    (hn : n < 2147483648) (hN2 : 2 * N < 2147483648) (hh : h < 2147483648) (hT : TInv maxMon V N) (hV : AllV maxMon V)
    (hlr : l0 ≤ r0) (hrN : r0 ≤ N) (hV2 : V.length < 2147483647)
    (i0 : vbuf0.items = V.map Value.integer) (bv0 : vbuf0.Valid (accepts (.integer s64)))
    (l0' : vbuf0.limit = CppVectorBindings.sizeLimit s64) (o0 : vbuf0.owner = V0)
    (e1 e2 e3 e4 e5 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true)
    (hs4 : e4.scalarOnly = true) (hs5 : e5.scalarOnly = true)
    (ty1 : e1.resultType = i32) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32) (ty4 : e4.resultType = i32)
    (ty5 : e5.resultType = i32)
    (value1 : e1.denote (envOf caller) = some (n : Int)) (value2 : e2.denote (envOf caller) = some (N : Int))
    (value3 : e3.denote (envOf caller) = some (h : Int)) (value4 : e4.denote (envOf caller) = some (l0 : Int))
    (value5 : e5.denote (envOf caller) = some (r0 : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.SegmentTreeInstance.SegmentTree_cp__SegMax_long_long__long_long_product.parameters
        [.vectorReference s0,.value e1,.value e2,.value e3,.value e4,.value e5] = some Sinit ∧
      Proofs.SegmentTreeInstance.SegmentTree_cp__SegMax_long_long__long_long_product.callFuel fuel caller
        [.vectorReference s0,.value e1,.value e2,.value e3,.value e4,.value e5] =
        .finished (res,.scalar (rfold maxMon V (l0 + N) (r0 - l0))) ∧
      ScalarPostM (mvIG V0 vsc0 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
          caller.frame.state.storage.objects.length)
          caller Sinit res (e1.nodes + e2.nodes + e3.nodes + e4.nodes + e5.nodes) (1600 * (Nat.log2 (r0 - l0) + 1) + 500)
          caller.scalars.memory 0 (VO V) := by
  have hN31 : N < 2147483648 := by omega
  have hlenV := hT.2.1
  obtain ⟨t1,t2,t3,t4,t5,g1,g2,g3,g4,g5,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    Proofs.SegmentTreePrepare.prepare_prod caller ok0 e1 e2 e3 e4 e5 (n : Int) (N : Int) (h : Int) (l0 : Int) (r0 : Int)
      hs1 hs2 hs3 hs4 hs5 ty1 ty2 ty3 ty4 ty5 value1 value2 value3 value4 value5 (validN n hn) (validN N hN31) (validN h hh)
      (validN l0 (by omega)) (validN r0 (by omega))
  have fwS := fwIG_init caller ok0 V hV2 i0 bv0 l0' o0
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrvv,⟨cl,hrps⟩,hcost,hneed,hwk⟩ :=
    Proofs.SegmentTreeProduct.body_execProd (mvIG V0 vsc0 caller.frame.state.liveSpace caller.frame.state.storage.work
      (caller.scope + 1) caller.frame.state.storage.objects.length) rfl rfl (callerP caller) n N h l0 r0 V hn hN2 hh hT hV hlr hrN
    (Nat.log2 (r0 - l0) + 3) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,(N : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(l0 : Int)⟩,⟨i32,(r0 : Int)⟩]).take
      caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,(N : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(l0 : Int)⟩,⟨i32,(r0 : Int)⟩],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,
       ⟨(callerP caller).length+3,true⟩,⟨(callerP caller).length+4,true⟩]⟩ : PS) =
      gS (callerP caller) [ci n, ci N, ci h, ci l0, ci r0] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  have gw2 := g2.2.2.1
  have gw3 := g3.2.2.1
  have gw4 := g4.2.2.1
  have gw5 := g5.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1 gw2 gw3 gw4 gw5
  have hpost := call_vecm (mvIG V0 vsc0 caller.frame.state.liveSpace
      caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length)
    (fun _ => true) (by intro k hk; exact ⟨rfl, rfl⟩)
    caller Proofs.SegmentTreeInstance.SegmentTree_cp__SegMax_long_long__long_long_product
    [.vectorReference s0,.value e1,.value e2,.value e3,.value e4,.value e5] Sinit
    (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,(N : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(l0 : Int)⟩,⟨i32,(r0 : Int)⟩])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,
       ⟨(callerP caller).length+3,true⟩,⟨(callerP caller).length+4,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [Proofs.SegmentTreeProduct.body_eqProd]; decide)
    (Nat.log2 (r0 - l0) + 3) rr (by rw [hmk, Proofs.SegmentTreeProduct.body_eqProd]; exact hexec) _ hret s64 rfl
    (rfold_V maxMon V hV (r0 - l0) (l0 + N) (by omega)) (by omega) (by simp [hlenP])
    (e1.nodes + e2.nodes + e3.nodes + e4.nodes + e5.nodes) (1600 * (Nat.log2 (r0 - l0) + 1) + 500) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) (by omega)

set_option maxHeartbeats 16000000 in
/-- `SegmentTree::product_all()`: the root `node[1]`. -/
theorem segtree_product_all_correct (caller : NState) {s0 vb0 V0 vsc0 : Nat} {vbuf0 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (V : List Int) (n N h : Nat)
    (hn : n < 2147483648) (hN : N < 2147483648) (hh : h < 2147483648)
    (hlt : 1 < V.length) (hv : s64.valid (V.getD 1 0) = true) (hV2 : V.length < 2147483647)
    (i0 : vbuf0.items = V.map Value.integer) (bv0 : vbuf0.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (o0 : vbuf0.owner = V0)
    (e1 e2 e3 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true)
    (ty1 : e1.resultType = i32) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32)
    (value1 : e1.denote (envOf caller) = some (n : Int)) (value2 : e2.denote (envOf caller) = some (N : Int))
    (value3 : e3.denote (envOf caller) = some (h : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.SegmentTreeInstance.SegmentTree_cp__SegMax_long_long__long_long_product_all.parameters
        [.vectorReference s0,.value e1,.value e2,.value e3] = some Sinit ∧
      Proofs.SegmentTreeInstance.SegmentTree_cp__SegMax_long_long__long_long_product_all.callFuel fuel caller
        [.vectorReference s0,.value e1,.value e2,.value e3] = .finished (res,.scalar (V.getD 1 0)) ∧
      ScalarPostM (mvIG V0 vsc0 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
          caller.frame.state.storage.objects.length)
          caller Sinit res (e1.nodes + e2.nodes + e3.nodes) 100 caller.scalars.memory 0 (VO V) := by
  obtain ⟨t1,t2,t3,g1,g2,g3,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    Proofs.SegmentTreePrepare.prepare_all caller ok0 e1 e2 e3 (n : Int) (N : Int) (h : Int) hs1 hs2 hs3 ty1 ty2 ty3
      value1 value2 value3 (validN n hn) (validN N hN) (validN h hh)
  have fwS := fwIG_init caller ok0 V hV2 i0 bv0 l0 o0
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrvv,⟨cl,hrps⟩,hcost,hneed,hwk⟩ :=
    Proofs.SegmentTreeGet.body_execAll (mvIG V0 vsc0 caller.frame.state.liveSpace caller.frame.state.storage.work
      (caller.scope + 1) caller.frame.state.storage.objects.length) rfl rfl (callerP caller) n N h V hlt hv 2
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,(N : Int)⟩,⟨i32,(h : Int)⟩]).take
      caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,(N : Int)⟩,⟨i32,(h : Int)⟩],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩]⟩ : PS) =
      gS (callerP caller) [ci n, ci N, ci h] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  have gw2 := g2.2.2.1
  have gw3 := g3.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1 gw2 gw3
  have hpost := call_vecm (mvIG V0 vsc0 caller.frame.state.liveSpace
      caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length)
    (fun _ => true) (by intro k hk; exact ⟨rfl, rfl⟩)
    caller Proofs.SegmentTreeInstance.SegmentTree_cp__SegMax_long_long__long_long_product_all
    [.vectorReference s0,.value e1,.value e2,.value e3] Sinit
    (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,(N : Int)⟩,⟨i32,(h : Int)⟩])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [Proofs.SegmentTreeGet.body_eqAll]; decide)
    2 rr (by rw [hmk, Proofs.SegmentTreeGet.body_eqAll]; exact hexec) _ hret s64 rfl hv (by omega) (by simp [hlenP])
    (e1.nodes + e2.nodes + e3.nodes) 100 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) (by omega)

open Proofs.TreeArcCostsExec (VC)

/-- The callee of the constructor: `node` (writable) and `v` (read-only), both `long long` vectors. -/
def mvCT (V0 V1 vsc0 vsc1 : Nat) (m1 : Bool) (L0 T0 sc N : Nat) (h01 : V0 ≠ V1) : MV where
  nv := 2
  ty := fun _ => s64
  wV := fun k => decide (k = 0)
  flag := fun k => if k = 0 then true else m1
  R := fun k => if k = 0 then V0 else V1
  vsc := fun k => if k = 0 then vsc0 else vsc1
  perm := by
    intro k hk
    have : k = 0 := by simpa using hk
    subst this; simp
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by
    intro j k hj hk hjk hw
    have : k = 0 := by simpa using hw
    subst this
    have : j = 1 := by omega
    subst this
    simpa using h01.symm

theorem wr_bodyCtor : WrM (fun k => decide (k = 0)) (Proofs.SegmentTreeCtor.bodyCtor 2) = true := by decide

theorem cases2c (k : Nat) (hk : k < 2) : k = 0 ∨ k = 1 := by omega

theorem fwCT_init (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {m1 : Bool}
    {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 false m1 vbuf1)
    (h01 : V0 ≠ V1) (A B : List Int) (hA : A.length < 2147483647) (hB : B.length < 2147483647)
    (i0 : vbuf0.items = A.map Value.integer) (i1 : vbuf1.items = B.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer s64))) (bv1 : vbuf1.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit s64)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) :
    FWM (mvCT V0 V1 vsc0 vsc1 m1 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h01)
      (VC A B) (fun k => if k = 0 then vbuf0 else vbuf1) 0
      (⟨caller.frame.state, caller.frame.rootWritable,
        [⟨V0,.integer s64,true,.root vsc0⟩,⟨V1,.integer s64,false,.root vsc1⟩]⟩ : Frame) := by
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · intro k hk
    rcases cases2c k hk with rfl | rfl
    · simpa [mvCT] using ok0.vtag
    · simpa [mvCT] using ok1.vtag
  · intro k hk
    rcases cases2c k hk with rfl | rfl
    · simpa [mvCT] using ok0.vfound
    · simpa [mvCT] using ok1.vfound
  · intro k hk
    rcases cases2c k hk with rfl | rfl
    · simpa [mvCT] using ok0.flag
    · simpa [mvCT] using ok1.flag
  · intro k hk
    rcases cases2c k hk with rfl | rfl
    · simpa [mvCT, VC] using i0
    · simpa [mvCT, VC] using i1
  · intro k hk
    rcases cases2c k hk with rfl | rfl
    · simpa [mvCT] using bv0
    · simpa [mvCT] using bv1
  · intro k hk
    rcases cases2c k hk with rfl | rfl
    · simpa [mvCT] using l0
    · simpa [mvCT] using l1
  · intro k hk
    rcases cases2c k hk with rfl | rfl
    · simpa [mvCT] using o0
    · simpa [mvCT] using o1
  · intro k hk
    rcases cases2c k hk with rfl | rfl
    · simp [VC]; omega
    · simp [VC]; omega

open Proofs.SegmentTreeCtor (szv EMIN)

set_option maxHeartbeats 32000000 in
/-- The constructor `SegmentTree(const vector<T>& v)` builds the tree in `node` (a vector of `2 * n_node` copies of the identity). -/
theorem segtree_ctor_correct (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {m1 : Bool} {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 false m1 vbuf1)
    (h01 : V0 ≠ V1) (Vin : List Int) (n : Nat) (hnv1 : Vin.length = n) (hn1 : 1 ≤ n) (hn29 : n ≤ 536870912)
    (hVin : AllV maxMon Vin) (k : Nat) (hk1 : n ≤ szv k) (hk2 : ∀ j, j < k → szv j < n)
    (i0 : vbuf0.items = (List.replicate (2 * szv k) EMIN).map Value.integer) (i1 : vbuf1.items = Vin.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer s64))) (bv1 : vbuf1.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit s64)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.SegmentTreeInstance.SegmentTree_cp__SegMax_long_long__long_long_new0.parameters
        [.vectorReference s0,.vectorReference s1] = some Sinit ∧
      Proofs.SegmentTreeInstance.SegmentTree_cp__SegMax_long_long__long_long_new0.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1] = .finished (res,Ret.unit) ∧
      ∃ Vf : List Int, TInv maxMon Vf (szv k) ∧ AllV maxMon Vf ∧ Vf.length = 2 * szv k ∧
        (∀ i, i < n → Vf.getD (szv k + i) 0 = Vin.getD i 0) ∧ (∀ i, n ≤ i → i < szv k → Vf.getD (szv k + i) 0 = EMIN) ∧
        ScalarPostM (mvCT V0 V1 vsc0 vsc1 m1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
          caller.frame.state.storage.objects.length h01)
          caller Sinit res 0 (3000 * (2 ^ k + 1) + 3200) caller.scalars.memory (2 ^ k + n) (VC Vf Vin) := by
  have h29 : 2 ^ 29 = 536870912 := by norm_num
  have hk29 : k ≤ 29 := by
    apply Classical.byContradiction
    intro hh
    have := hk2 29 (by omega)
    have h2 : szv 29 = 536870912 := by unfold szv; rw [if_neg (by omega), h29]
    omega
  have hN29 : szv k ≤ 536870912 := by
    unfold szv; split
    · omega
    · rw [← h29]; exact Nat.pow_le_pow_right (by decide) hk29
  have hnodeLen : (List.replicate (2 * szv k) EMIN).length < 2147483647 := by simp; omega
  have hVinLen : Vin.length < 2147483647 := by omega
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    Proofs.SegmentTreePrepare.prepare_ctor caller ok0 ok1
  have fwS := fwCT_init caller ok0 ok1 h01 _ Vin hnodeLen hVinLen i0 i1 bv0 bv1 l0 l1 o0 o1
  rw [← sFrame] at fwS
  have hp2k : 0 < 2 ^ k := Nat.two_pow_pos k
  obtain ⟨rr,hexec,hret,⟨cl,hrps⟩,Vf,hrvv,hTf,hVf,hlenf,hleafc,hleafe,hcost,hneed,hwk⟩ :=
    Proofs.SegmentTreeCtor.body_execCtor (mvCT V0 V1 vsc0 vsc1 m1 caller.frame.state.liveSpace caller.frame.state.storage.work
      (caller.scope + 1) caller.frame.state.storage.objects.length h01) rfl rfl rfl (callerP caller) Vin n hnv1 hn1 hn29 hVin k hk1 hk2
    (40 + n + 2 ^ k) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have hmk : (⟨callerP caller, []⟩ : PS) = gS (callerP caller) [] := by simp [gS]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left
  have hch : ((caller.charge 1 1).charge 1 1).scalars.work = caller.scalars.work + 2 := by
    simp [NState.charge, NState.observe, CppState.State.observe]
  have hpost := call_vecm_unit (mvCT V0 V1 vsc0 vsc1 m1 caller.frame.state.liveSpace
      caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h01)
    (fun k => decide (k = 0))
    (by intro k hk; have : k = 0 := by simpa using hk
        subst this; simp [mvCT])
    caller Proofs.SegmentTreeInstance.SegmentTree_cp__SegMax_long_long__long_long_new0
    [.vectorReference s0,.vectorReference s1] Sinit (callerP caller) []
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]) (by rw [takeM]) ok0.base (by rw [Proofs.SegmentTreeCtor.body_eqCtor]; exact wr_bodyCtor)
    (40 + n + 2 ^ k) rr (by rw [hmk, Proofs.SegmentTreeCtor.body_eqCtor]; exact hexec) hret rfl (by omega) (by simp [hlenP])
    0 (3000 * (2 ^ k + 1) + 3200) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,Vf,hTf,hVf,hlenf,hleafc,hleafe,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    exact List.take_left
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk


/-! ### The same theorems for `SegmentTree<SegMin<long long>>` -/
namespace Min

open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCall
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (cs)
open Proofs.InvGcdExec (VO)
open Proofs.InvGcdCall (mvIG fwIG_init)
open Proofs.SegTreeMath
open Proofs.SegmentTreeMinExec (minMon mn)

theorem wr_bodySet : WrM (fun _ => true) (Proofs.SegmentTreeMinSet.bodySet 1) = true := by decide

set_option maxHeartbeats 16000000 in
/-- `SegmentTree::set(idx, val)` on the tree stored in `node`: afterwards `node` is again a tree. -/
theorem segtree_set_correct (caller : NState) {s0 vb0 V0 vsc0 : Nat} {vbuf0 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (V : List Int) (n N h idx : Nat) (val : Int)
    (hN : N = 2 ^ h) (hn : n < 2147483648) (hh30 : h ≤ 30) (hidx : idx < N) (hT : TInv minMon V N) (hV : AllV minMon V)
    (hval : s64.valid val = true) (hV2 : V.length < 2147483647)
    (i0 : vbuf0.items = V.map Value.integer) (bv0 : vbuf0.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (o0 : vbuf0.owner = V0)
    (e1 e2 e3 e4 e5 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true)
    (hs4 : e4.scalarOnly = true) (hs5 : e5.scalarOnly = true)
    (ty1 : e1.resultType = i32) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32) (ty4 : e4.resultType = i32)
    (ty5 : e5.resultType = s64)
    (value1 : e1.denote (envOf caller) = some (n : Int)) (value2 : e2.denote (envOf caller) = some (N : Int))
    (value3 : e3.denote (envOf caller) = some (h : Int)) (value4 : e4.denote (envOf caller) = some (idx : Int))
    (value5 : e5.denote (envOf caller) = some val) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.SegmentTreeInstance.SegmentTree_cp__SegMin_long_long__long_long_set.parameters
        [.vectorReference s0,.value e1,.value e2,.value e3,.value e4,.value e5] = some Sinit ∧
      Proofs.SegmentTreeInstance.SegmentTree_cp__SegMin_long_long__long_long_set.callFuel fuel caller
        [.vectorReference s0,.value e1,.value e2,.value e3,.value e4,.value e5] = .finished (res,Ret.unit) ∧
      ∃ Vf : List Int, TInv minMon Vf N ∧ AllV minMon Vf ∧ Vf.length = 2 * N ∧ Vf.getD (idx + N) 0 = val ∧
        (∀ j, N ≤ j → j ≠ idx + N → Vf.getD j 0 = V.getD j 0) ∧
        ScalarPostM (mvIG V0 vsc0 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
          caller.frame.state.storage.objects.length)
          caller Sinit res (e1.nodes + e2.nodes + e3.nodes + e4.nodes + e5.nodes) (900 * h + 600) caller.scalars.memory (h + 1)
          (VO Vf) := by
  have hn31 : n < 2147483648 := hn
  have h30 : 2 ^ 30 = 1073741824 := by norm_num
  have hN30 : N ≤ 1073741824 := by rw [hN, ← h30]; exact Nat.pow_le_pow_right (by decide) hh30
  have hlenV := hT.2.1
  obtain ⟨t1,t2,t3,t4,t5,g1,g2,g3,g4,g5,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    Proofs.SegmentTreeMinPrepare.prepare_set caller ok0 e1 e2 e3 e4 e5 (n : Int) (N : Int) (h : Int) (idx : Int) val hs1 hs2 hs3 hs4 hs5
      ty1 ty2 ty3 ty4 ty5 value1 value2 value3 value4 value5 (validN n hn31) (validN N (by omega)) (validN h (by omega))
      (validN idx (by omega)) hval
  have fwS := fwIG_init caller ok0 V hV2 i0 bv0 l0 o0
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,⟨cl,hrps⟩,Vf,hrvv,hTf,hVf,hlenf,hleaf,hothers,hcost,hneed,hwk⟩ :=
    Proofs.SegmentTreeMinSet.body_execSet (mvIG V0 vsc0 caller.frame.state.liveSpace caller.frame.state.storage.work
      (caller.scope + 1) caller.frame.state.storage.objects.length) rfl rfl (callerP caller) n N h idx val V hN hn hh30 hidx hT hV hval
    (h + 3) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,(N : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(idx : Int)⟩,⟨s64,val⟩]).take
      caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,(N : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(idx : Int)⟩,⟨s64,val⟩],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,
       ⟨(callerP caller).length+3,true⟩,⟨(callerP caller).length+4,true⟩]⟩ : PS) =
      gS (callerP caller) [ci n, ci N, ci h, ci idx, cs val] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  have gw2 := g2.2.2.1
  have gw3 := g3.2.2.1
  have gw4 := g4.2.2.1
  have gw5 := g5.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1 gw2 gw3 gw4 gw5
  have hpost := call_vecm_unit (mvIG V0 vsc0 caller.frame.state.liveSpace
      caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length)
    (fun _ => true) (by intro k hk; exact ⟨rfl, rfl⟩)
    caller Proofs.SegmentTreeInstance.SegmentTree_cp__SegMin_long_long__long_long_set
    [.vectorReference s0,.value e1,.value e2,.value e3,.value e4,.value e5] Sinit
    (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,(N : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(idx : Int)⟩,⟨s64,val⟩])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,
       ⟨(callerP caller).length+3,true⟩,⟨(callerP caller).length+4,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [Proofs.SegmentTreeMinSet.body_eqSet]; exact wr_bodySet)
    (h + 3) rr (by rw [hmk, Proofs.SegmentTreeMinSet.body_eqSet]; exact hexec) hret rfl (by omega) (by simp [hlenP])
    (e1.nodes + e2.nodes + e3.nodes + e4.nodes + e5.nodes) (900 * h + 600) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,Vf,hTf,hVf,hlenf,hleaf,hothers,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk

theorem wr_bodyAny (b : Command) (h : WrM (fun _ => true) b = true) : WrM (fun _ => true) b = true := h

set_option maxHeartbeats 16000000 in
/-- `SegmentTree::get(idx)`: the leaf `node[idx + n_node]`. -/
theorem segtree_get_correct (caller : NState) {s0 vb0 V0 vsc0 : Nat} {vbuf0 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (V : List Int) (n N h idx : Nat)
    (hn : n < 2147483648) (hN : N < 2147483648) (hh : h < 2147483648) (hidx : idx + N < 2147483648)
    (hlt : idx + N < V.length) (hv : s64.valid (V.getD (idx + N) 0) = true) (hV2 : V.length < 2147483647)
    (i0 : vbuf0.items = V.map Value.integer) (bv0 : vbuf0.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (o0 : vbuf0.owner = V0)
    (e1 e2 e3 e4 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true)
    (hs4 : e4.scalarOnly = true)
    (ty1 : e1.resultType = i32) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32) (ty4 : e4.resultType = i32)
    (value1 : e1.denote (envOf caller) = some (n : Int)) (value2 : e2.denote (envOf caller) = some (N : Int))
    (value3 : e3.denote (envOf caller) = some (h : Int)) (value4 : e4.denote (envOf caller) = some (idx : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.SegmentTreeInstance.SegmentTree_cp__SegMin_long_long__long_long_get.parameters
        [.vectorReference s0,.value e1,.value e2,.value e3,.value e4] = some Sinit ∧
      Proofs.SegmentTreeInstance.SegmentTree_cp__SegMin_long_long__long_long_get.callFuel fuel caller
        [.vectorReference s0,.value e1,.value e2,.value e3,.value e4] = .finished (res,.scalar (V.getD (idx + N) 0)) ∧
      ScalarPostM (mvIG V0 vsc0 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
          caller.frame.state.storage.objects.length)
          caller Sinit res (e1.nodes + e2.nodes + e3.nodes + e4.nodes) 100 caller.scalars.memory 0 (VO V) := by
  obtain ⟨t1,t2,t3,t4,g1,g2,g3,g4,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    Proofs.SegmentTreeMinPrepare.prepare_get caller ok0 e1 e2 e3 e4 (n : Int) (N : Int) (h : Int) (idx : Int) hs1 hs2 hs3 hs4
      ty1 ty2 ty3 ty4 value1 value2 value3 value4 (validN n hn) (validN N hN) (validN h hh) (validN idx (by omega))
  have fwS := fwIG_init caller ok0 V hV2 i0 bv0 l0 o0
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrvv,⟨cl,hrps⟩,hcost,hneed,hwk⟩ :=
    Proofs.SegmentTreeMinGet.body_execGet (mvIG V0 vsc0 caller.frame.state.liveSpace caller.frame.state.storage.work
      (caller.scope + 1) caller.frame.state.storage.objects.length) rfl rfl (callerP caller) n N h idx V hn hN hh hidx hlt hv 2
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,(N : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(idx : Int)⟩]).take
      caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,(N : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(idx : Int)⟩],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,
       ⟨(callerP caller).length+3,true⟩]⟩ : PS) = gS (callerP caller) [ci n, ci N, ci h, ci idx] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  have gw2 := g2.2.2.1
  have gw3 := g3.2.2.1
  have gw4 := g4.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1 gw2 gw3 gw4
  have hpost := call_vecm (mvIG V0 vsc0 caller.frame.state.liveSpace
      caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length)
    (fun _ => true) (by intro k hk; exact ⟨rfl, rfl⟩)
    caller Proofs.SegmentTreeInstance.SegmentTree_cp__SegMin_long_long__long_long_get
    [.vectorReference s0,.value e1,.value e2,.value e3,.value e4] Sinit
    (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,(N : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(idx : Int)⟩])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,
       ⟨(callerP caller).length+3,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [Proofs.SegmentTreeMinGet.body_eqGet]; decide)
    2 rr (by rw [hmk, Proofs.SegmentTreeMinGet.body_eqGet]; exact hexec) _ hret s64 rfl hv (by omega) (by simp [hlenP])
    (e1.nodes + e2.nodes + e3.nodes + e4.nodes) 100 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) (by omega)

set_option maxHeartbeats 16000000 in
/-- `SegmentTree::product(l, r)`: the product of the leaves `[l, r)`. -/
theorem segtree_product_correct (caller : NState) {s0 vb0 V0 vsc0 : Nat} {vbuf0 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (V : List Int) (n N h l0 r0 : Nat)
    (hn : n < 2147483648) (hN2 : 2 * N < 2147483648) (hh : h < 2147483648) (hT : TInv minMon V N) (hV : AllV minMon V)
    (hlr : l0 ≤ r0) (hrN : r0 ≤ N) (hV2 : V.length < 2147483647)
    (i0 : vbuf0.items = V.map Value.integer) (bv0 : vbuf0.Valid (accepts (.integer s64)))
    (l0' : vbuf0.limit = CppVectorBindings.sizeLimit s64) (o0 : vbuf0.owner = V0)
    (e1 e2 e3 e4 e5 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true)
    (hs4 : e4.scalarOnly = true) (hs5 : e5.scalarOnly = true)
    (ty1 : e1.resultType = i32) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32) (ty4 : e4.resultType = i32)
    (ty5 : e5.resultType = i32)
    (value1 : e1.denote (envOf caller) = some (n : Int)) (value2 : e2.denote (envOf caller) = some (N : Int))
    (value3 : e3.denote (envOf caller) = some (h : Int)) (value4 : e4.denote (envOf caller) = some (l0 : Int))
    (value5 : e5.denote (envOf caller) = some (r0 : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.SegmentTreeInstance.SegmentTree_cp__SegMin_long_long__long_long_product.parameters
        [.vectorReference s0,.value e1,.value e2,.value e3,.value e4,.value e5] = some Sinit ∧
      Proofs.SegmentTreeInstance.SegmentTree_cp__SegMin_long_long__long_long_product.callFuel fuel caller
        [.vectorReference s0,.value e1,.value e2,.value e3,.value e4,.value e5] =
        .finished (res,.scalar (rfold minMon V (l0 + N) (r0 - l0))) ∧
      ScalarPostM (mvIG V0 vsc0 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
          caller.frame.state.storage.objects.length)
          caller Sinit res (e1.nodes + e2.nodes + e3.nodes + e4.nodes + e5.nodes) (1600 * (Nat.log2 (r0 - l0) + 1) + 500)
          caller.scalars.memory 0 (VO V) := by
  have hN31 : N < 2147483648 := by omega
  have hlenV := hT.2.1
  obtain ⟨t1,t2,t3,t4,t5,g1,g2,g3,g4,g5,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    Proofs.SegmentTreeMinPrepare.prepare_prod caller ok0 e1 e2 e3 e4 e5 (n : Int) (N : Int) (h : Int) (l0 : Int) (r0 : Int)
      hs1 hs2 hs3 hs4 hs5 ty1 ty2 ty3 ty4 ty5 value1 value2 value3 value4 value5 (validN n hn) (validN N hN31) (validN h hh)
      (validN l0 (by omega)) (validN r0 (by omega))
  have fwS := fwIG_init caller ok0 V hV2 i0 bv0 l0' o0
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrvv,⟨cl,hrps⟩,hcost,hneed,hwk⟩ :=
    Proofs.SegmentTreeMinProduct.body_execProd (mvIG V0 vsc0 caller.frame.state.liveSpace caller.frame.state.storage.work
      (caller.scope + 1) caller.frame.state.storage.objects.length) rfl rfl (callerP caller) n N h l0 r0 V hn hN2 hh hT hV hlr hrN
    (Nat.log2 (r0 - l0) + 3) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,(N : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(l0 : Int)⟩,⟨i32,(r0 : Int)⟩]).take
      caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,(N : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(l0 : Int)⟩,⟨i32,(r0 : Int)⟩],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,
       ⟨(callerP caller).length+3,true⟩,⟨(callerP caller).length+4,true⟩]⟩ : PS) =
      gS (callerP caller) [ci n, ci N, ci h, ci l0, ci r0] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  have gw2 := g2.2.2.1
  have gw3 := g3.2.2.1
  have gw4 := g4.2.2.1
  have gw5 := g5.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1 gw2 gw3 gw4 gw5
  have hpost := call_vecm (mvIG V0 vsc0 caller.frame.state.liveSpace
      caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length)
    (fun _ => true) (by intro k hk; exact ⟨rfl, rfl⟩)
    caller Proofs.SegmentTreeInstance.SegmentTree_cp__SegMin_long_long__long_long_product
    [.vectorReference s0,.value e1,.value e2,.value e3,.value e4,.value e5] Sinit
    (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,(N : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(l0 : Int)⟩,⟨i32,(r0 : Int)⟩])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,
       ⟨(callerP caller).length+3,true⟩,⟨(callerP caller).length+4,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [Proofs.SegmentTreeMinProduct.body_eqProd]; decide)
    (Nat.log2 (r0 - l0) + 3) rr (by rw [hmk, Proofs.SegmentTreeMinProduct.body_eqProd]; exact hexec) _ hret s64 rfl
    (rfold_V minMon V hV (r0 - l0) (l0 + N) (by omega)) (by omega) (by simp [hlenP])
    (e1.nodes + e2.nodes + e3.nodes + e4.nodes + e5.nodes) (1600 * (Nat.log2 (r0 - l0) + 1) + 500) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) (by omega)

set_option maxHeartbeats 16000000 in
/-- `SegmentTree::product_all()`: the root `node[1]`. -/
theorem segtree_product_all_correct (caller : NState) {s0 vb0 V0 vsc0 : Nat} {vbuf0 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (V : List Int) (n N h : Nat)
    (hn : n < 2147483648) (hN : N < 2147483648) (hh : h < 2147483648)
    (hlt : 1 < V.length) (hv : s64.valid (V.getD 1 0) = true) (hV2 : V.length < 2147483647)
    (i0 : vbuf0.items = V.map Value.integer) (bv0 : vbuf0.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (o0 : vbuf0.owner = V0)
    (e1 e2 e3 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true)
    (ty1 : e1.resultType = i32) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32)
    (value1 : e1.denote (envOf caller) = some (n : Int)) (value2 : e2.denote (envOf caller) = some (N : Int))
    (value3 : e3.denote (envOf caller) = some (h : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.SegmentTreeInstance.SegmentTree_cp__SegMin_long_long__long_long_product_all.parameters
        [.vectorReference s0,.value e1,.value e2,.value e3] = some Sinit ∧
      Proofs.SegmentTreeInstance.SegmentTree_cp__SegMin_long_long__long_long_product_all.callFuel fuel caller
        [.vectorReference s0,.value e1,.value e2,.value e3] = .finished (res,.scalar (V.getD 1 0)) ∧
      ScalarPostM (mvIG V0 vsc0 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
          caller.frame.state.storage.objects.length)
          caller Sinit res (e1.nodes + e2.nodes + e3.nodes) 100 caller.scalars.memory 0 (VO V) := by
  obtain ⟨t1,t2,t3,g1,g2,g3,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    Proofs.SegmentTreeMinPrepare.prepare_all caller ok0 e1 e2 e3 (n : Int) (N : Int) (h : Int) hs1 hs2 hs3 ty1 ty2 ty3
      value1 value2 value3 (validN n hn) (validN N hN) (validN h hh)
  have fwS := fwIG_init caller ok0 V hV2 i0 bv0 l0 o0
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrvv,⟨cl,hrps⟩,hcost,hneed,hwk⟩ :=
    Proofs.SegmentTreeMinGet.body_execAll (mvIG V0 vsc0 caller.frame.state.liveSpace caller.frame.state.storage.work
      (caller.scope + 1) caller.frame.state.storage.objects.length) rfl rfl (callerP caller) n N h V hlt hv 2
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,(N : Int)⟩,⟨i32,(h : Int)⟩]).take
      caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,(N : Int)⟩,⟨i32,(h : Int)⟩],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩]⟩ : PS) =
      gS (callerP caller) [ci n, ci N, ci h] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  have gw2 := g2.2.2.1
  have gw3 := g3.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1 gw2 gw3
  have hpost := call_vecm (mvIG V0 vsc0 caller.frame.state.liveSpace
      caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length)
    (fun _ => true) (by intro k hk; exact ⟨rfl, rfl⟩)
    caller Proofs.SegmentTreeInstance.SegmentTree_cp__SegMin_long_long__long_long_product_all
    [.vectorReference s0,.value e1,.value e2,.value e3] Sinit
    (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,(N : Int)⟩,⟨i32,(h : Int)⟩])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [Proofs.SegmentTreeMinGet.body_eqAll]; decide)
    2 rr (by rw [hmk, Proofs.SegmentTreeMinGet.body_eqAll]; exact hexec) _ hret s64 rfl hv (by omega) (by simp [hlenP])
    (e1.nodes + e2.nodes + e3.nodes) 100 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) (by omega)

open Proofs.TreeArcCostsExec (VC)

/-- The callee of the constructor: `node` (writable) and `v` (read-only), both `long long` vectors. -/
def mvCT (V0 V1 vsc0 vsc1 : Nat) (m1 : Bool) (L0 T0 sc N : Nat) (h01 : V0 ≠ V1) : MV where
  nv := 2
  ty := fun _ => s64
  wV := fun k => decide (k = 0)
  flag := fun k => if k = 0 then true else m1
  R := fun k => if k = 0 then V0 else V1
  vsc := fun k => if k = 0 then vsc0 else vsc1
  perm := by
    intro k hk
    have : k = 0 := by simpa using hk
    subst this; simp
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by
    intro j k hj hk hjk hw
    have : k = 0 := by simpa using hw
    subst this
    have : j = 1 := by omega
    subst this
    simpa using h01.symm

theorem wr_bodyCtor : WrM (fun k => decide (k = 0)) (Proofs.SegmentTreeMinCtor.bodyCtor 2) = true := by decide

theorem cases2c (k : Nat) (hk : k < 2) : k = 0 ∨ k = 1 := by omega

theorem fwCT_init (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {m1 : Bool}
    {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 false m1 vbuf1)
    (h01 : V0 ≠ V1) (A B : List Int) (hA : A.length < 2147483647) (hB : B.length < 2147483647)
    (i0 : vbuf0.items = A.map Value.integer) (i1 : vbuf1.items = B.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer s64))) (bv1 : vbuf1.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit s64)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) :
    FWM (mvCT V0 V1 vsc0 vsc1 m1 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h01)
      (VC A B) (fun k => if k = 0 then vbuf0 else vbuf1) 0
      (⟨caller.frame.state, caller.frame.rootWritable,
        [⟨V0,.integer s64,true,.root vsc0⟩,⟨V1,.integer s64,false,.root vsc1⟩]⟩ : Frame) := by
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · intro k hk
    rcases cases2c k hk with rfl | rfl
    · simpa [mvCT] using ok0.vtag
    · simpa [mvCT] using ok1.vtag
  · intro k hk
    rcases cases2c k hk with rfl | rfl
    · simpa [mvCT] using ok0.vfound
    · simpa [mvCT] using ok1.vfound
  · intro k hk
    rcases cases2c k hk with rfl | rfl
    · simpa [mvCT] using ok0.flag
    · simpa [mvCT] using ok1.flag
  · intro k hk
    rcases cases2c k hk with rfl | rfl
    · simpa [mvCT, VC] using i0
    · simpa [mvCT, VC] using i1
  · intro k hk
    rcases cases2c k hk with rfl | rfl
    · simpa [mvCT] using bv0
    · simpa [mvCT] using bv1
  · intro k hk
    rcases cases2c k hk with rfl | rfl
    · simpa [mvCT] using l0
    · simpa [mvCT] using l1
  · intro k hk
    rcases cases2c k hk with rfl | rfl
    · simpa [mvCT] using o0
    · simpa [mvCT] using o1
  · intro k hk
    rcases cases2c k hk with rfl | rfl
    · simp [VC]; omega
    · simp [VC]; omega

open Proofs.SegmentTreeMinCtor (EMAX)

set_option maxHeartbeats 32000000 in
/-- The constructor `SegmentTree(const vector<T>& v)` builds the tree in `node` (a vector of `2 * n_node` copies of the identity). -/
theorem segtree_ctor_correct (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {m1 : Bool} {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 false m1 vbuf1)
    (h01 : V0 ≠ V1) (Vin : List Int) (n : Nat) (hnv1 : Vin.length = n) (hn1 : 1 ≤ n) (hn29 : n ≤ 536870912)
    (hVin : AllV minMon Vin) (k : Nat) (hk1 : n ≤ Proofs.SegmentTreeMinCtor.szv k) (hk2 : ∀ j, j < k → Proofs.SegmentTreeMinCtor.szv j < n)
    (i0 : vbuf0.items = (List.replicate (2 * Proofs.SegmentTreeMinCtor.szv k) EMAX).map Value.integer) (i1 : vbuf1.items = Vin.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer s64))) (bv1 : vbuf1.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit s64)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.SegmentTreeInstance.SegmentTree_cp__SegMin_long_long__long_long_new0.parameters
        [.vectorReference s0,.vectorReference s1] = some Sinit ∧
      Proofs.SegmentTreeInstance.SegmentTree_cp__SegMin_long_long__long_long_new0.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1] = .finished (res,Ret.unit) ∧
      ∃ Vf : List Int, TInv minMon Vf (Proofs.SegmentTreeMinCtor.szv k) ∧ AllV minMon Vf ∧ Vf.length = 2 * Proofs.SegmentTreeMinCtor.szv k ∧
        (∀ i, i < n → Vf.getD (Proofs.SegmentTreeMinCtor.szv k + i) 0 = Vin.getD i 0) ∧ (∀ i, n ≤ i → i < Proofs.SegmentTreeMinCtor.szv k → Vf.getD (Proofs.SegmentTreeMinCtor.szv k + i) 0 = EMAX) ∧
        ScalarPostM (mvCT V0 V1 vsc0 vsc1 m1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
          caller.frame.state.storage.objects.length h01)
          caller Sinit res 0 (3000 * (2 ^ k + 1) + 3200) caller.scalars.memory (2 ^ k + n) (VC Vf Vin) := by
  have h29 : 2 ^ 29 = 536870912 := by norm_num
  have hk29 : k ≤ 29 := by
    apply Classical.byContradiction
    intro hh
    have := hk2 29 (by omega)
    have h2 : Proofs.SegmentTreeMinCtor.szv 29 = 536870912 := by unfold Proofs.SegmentTreeMinCtor.szv; rw [if_neg (by omega), h29]
    omega
  have hN29 : Proofs.SegmentTreeMinCtor.szv k ≤ 536870912 := by
    unfold Proofs.SegmentTreeMinCtor.szv; split
    · omega
    · rw [← h29]; exact Nat.pow_le_pow_right (by decide) hk29
  have hnodeLen : (List.replicate (2 * Proofs.SegmentTreeMinCtor.szv k) EMAX).length < 2147483647 := by simp; omega
  have hVinLen : Vin.length < 2147483647 := by omega
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    Proofs.SegmentTreeMinPrepare.prepare_ctor caller ok0 ok1
  have fwS := fwCT_init caller ok0 ok1 h01 _ Vin hnodeLen hVinLen i0 i1 bv0 bv1 l0 l1 o0 o1
  rw [← sFrame] at fwS
  have hp2k : 0 < 2 ^ k := Nat.two_pow_pos k
  obtain ⟨rr,hexec,hret,⟨cl,hrps⟩,Vf,hrvv,hTf,hVf,hlenf,hleafc,hleafe,hcost,hneed,hwk⟩ :=
    Proofs.SegmentTreeMinCtor.body_execCtor (mvCT V0 V1 vsc0 vsc1 m1 caller.frame.state.liveSpace caller.frame.state.storage.work
      (caller.scope + 1) caller.frame.state.storage.objects.length h01) rfl rfl rfl (callerP caller) Vin n hnv1 hn1 hn29 hVin k hk1 hk2
    (40 + n + 2 ^ k) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have hmk : (⟨callerP caller, []⟩ : PS) = gS (callerP caller) [] := by simp [gS]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left
  have hch : ((caller.charge 1 1).charge 1 1).scalars.work = caller.scalars.work + 2 := by
    simp [NState.charge, NState.observe, CppState.State.observe]
  have hpost := call_vecm_unit (mvCT V0 V1 vsc0 vsc1 m1 caller.frame.state.liveSpace
      caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h01)
    (fun k => decide (k = 0))
    (by intro k hk; have : k = 0 := by simpa using hk
        subst this; simp [mvCT])
    caller Proofs.SegmentTreeInstance.SegmentTree_cp__SegMin_long_long__long_long_new0
    [.vectorReference s0,.vectorReference s1] Sinit (callerP caller) []
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]) (by rw [takeM]) ok0.base (by rw [Proofs.SegmentTreeMinCtor.body_eqCtor]; exact wr_bodyCtor)
    (40 + n + 2 ^ k) rr (by rw [hmk, Proofs.SegmentTreeMinCtor.body_eqCtor]; exact hexec) hret rfl (by omega) (by simp [hlenP])
    0 (3000 * (2 ^ k + 1) + 3200) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,Vf,hTf,hVf,hlenf,hleafc,hleafe,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    exact List.take_left
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk


end Min

end Proofs.SegmentTreeCall
