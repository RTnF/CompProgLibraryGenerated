import Proofs.PrimPrepare
import Proofs.PrimBridge
import Proofs.DijkstraOldCall

namespace Proofs.PrimCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCall
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare Proofs.PrimPrepare Proofs.DijkstraOldExec Proofs.DijkstraOldScan Proofs.DijkstraOldCall Proofs.PrimExec
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.PrimBridge

theorem body_eqPR5 : Proofs.PrimInstance.prim_std_vector_int.body = progPR 5 := rfl

theorem wr_bodyPR : WrM (fun k => decide (k = 3 ∨ k = 4)) (progPR 5) = true := by decide


open Proofs.BellmanFordMath (Edge)
open Proofs.DijkstraMath (Eall)

set_option maxHeartbeats 8000000 in
/-- `cp::prim(head, target, cost, dist, done, n, inf)` (array version, `O(n^2 + m)`): the returned value is the weight of a
minimum spanning forest of the symmetric graph given by the CSR arrays. -/
theorem prim_correct (caller : NState)
    {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 s3 vb3 V3 vsc3 s4 vb4 V4 vsc4 : Nat} {m0 m1 m2 : Bool}
    {vbuf0 vbuf1 vbuf2 vbuf3 vbuf4 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 false m1 vbuf1)
    (ok2 : VOKG caller s64 s2 vb2 V2 vsc2 false m2 vbuf2) (ok3 : VOKG caller s64 s3 vb3 V3 vsc3 true true vbuf3)
    (ok4 : VOKG caller i32 s4 vb4 V4 vsc4 true true vbuf4)
    (h03 : V0 ≠ V3) (h13 : V1 ≠ V3) (h23 : V2 ≠ V3) (h04 : V0 ≠ V4) (h14 : V1 ≠ V4) (h24 : V2 ≠ V4) (h34 : V3 ≠ V4)
    (H T : List Nat) (C Dd0 : List Int) (n : Nat) (inf Cm : Int) (hn : n < 2147483646) (hTM : T.length < 2147483647)
    (HK : Proofs.TopoSortMath.HeadOK H T n) (hTn : ∀ x ∈ T, x < n) (hCl : C.length = T.length) (hDl : Dd0.length = n)
    (hC0 : ∀ x ∈ C, 0 ≤ x ∧ x < inf) (hCm : ∀ x ∈ C, x ≤ Cm) (hCm0 : 0 ≤ Cm)
    (hov : (n : Int) * Cm ≤ 9223372036854775807) (hinf0 : 0 ≤ inf) (hinfB : inf ≤ 4611686018427387904)
    (hall : ∀ j, j < n → Dd0.getD j 0 = inf)
    (hsym : ∀ e ∈ Eall n (outEdges H T C), (e.2.1, e.1, e.2.2) ∈ Eall n (outEdges H T C))
    (i0 : vbuf0.items = (H.map (fun x : Nat => (x : Int))).map Value.integer)
    (i1 : vbuf1.items = (T.map (fun x : Nat => (x : Int))).map Value.integer)
    (i2 : vbuf2.items = C.map Value.integer) (i3 : vbuf3.items = Dd0.map Value.integer)
    (i4 : vbuf4.items = ((List.replicate n 0).map (fun x : Nat => (x : Int))).map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer i32))) (bv1 : vbuf1.Valid (accepts (.integer i32)))
    (bv2 : vbuf2.Valid (accepts (.integer s64))) (bv3 : vbuf3.Valid (accepts (.integer s64)))
    (bv4 : vbuf4.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit i32)
    (l2 : vbuf2.limit = CppVectorBindings.sizeLimit s64) (l3 : vbuf3.limit = CppVectorBindings.sizeLimit s64)
    (l4 : vbuf4.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) (o2 : vbuf2.owner = V2) (o3 : vbuf3.owner = V3) (o4 : vbuf4.owner = V4)
    (e1 e2 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (ty1 : e1.resultType = i32)
    (ty2 : e2.resultType = s64) (value1 : e1.denote (envOf caller) = some (n : Int))
    (value2 : e2.denote (envOf caller) = some inf) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState) (W : Nat) (Dd : List Int) (Dn : List Nat),
      prepare caller Proofs.PrimInstance.prim_std_vector_int.parameters
        [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3,.vectorReference s4,
         .value e1,.value e2] = some Sinit ∧
      Proofs.PrimInstance.prim_std_vector_int.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3,.vectorReference s4,
         .value e1,.value e2] = .finished (res,Ret.scalar (W : Int)) ∧
      IsMSF n Cm.toNat ((Eall n (outEdges H T C)).map toArc) W ∧
      ScalarPostM (mvDJ V0 V1 V2 V3 V4 vsc0 vsc1 vsc2 vsc3 vsc4 m0 m1 m2 caller.frame.state.liveSpace
        caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h03 h13 h23 h04 h14 h24 h34)
        caller Sinit res (e1.nodes + e2.nodes) ((640 * n + 760) * n + 420 * T.length + 150) caller.scalars.memory
        (T.length + 2 * n) (VD H T C Dd Dn) := by
  have hn32 : n < 2147483648 := by omega
  obtain ⟨t1,t2,g1,g2,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_pr caller ok0 ok1 ok2 ok3 ok4 e1 e2 (n : Int) inf hs1 hs2 ty1 ty2 value1 value2 (validN n hn32)
      (Proofs.BellmanFordExec.s64_valid_of inf (by omega))
  have hHl : H.length < 2147483647 := by rw [HK.len]; omega
  have hDnl : (doneOf n []).length < 2147483647 := by rw [doneOf_length]; omega
  have hDl' : Dd0.length < 2147483647 := by omega
  have hCl' : C.length < 2147483647 := by omega
  have hdoneL : doneOf n [] = List.replicate n 0 := doneOf_nil n
  have fwS := fwDJ_init caller ok0 ok1 ok2 ok3 ok4 h03 h13 h23 h04 h14 h24 h34 H T C Dd0 (doneOf n []) hHl hTM hCl' hDl' hDnl i0 i1 i2 i3
    (by rw [hdoneL]; exact i4) bv0 bv1 bv2 bv3 bv4 l0 l1 l2 l3 l4 o0 o1 o2 o3 o4
  rw [← sFrame] at fwS
  obtain ⟨rr,D,pk,Dd,Dn,hexec,hret,hrvv,hrps,hI,hDn,hc,hnd,hcost,hneed,hwk⟩ :=
    prog_exec (mvDJ V0 V1 V2 V3 V4 vsc0 vsc1 vsc2 vsc3 vsc4 m0 m1 m2 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h03 h13 h23 h04 h14 h24 h34) (by simp [mvDJ]) (by simp [mvDJ])
      (by simp [mvDJ]) (by simp [mvDJ]) (by simp [mvDJ]) (by simp [mvDJ]) H T C Dd0 (callerP caller) n inf Cm
      (by unfold Proofs.BellmanFordExec.M31; omega) (by omega) HK hTn hTM hCl hC0 hCm hCm0 hov hinf0 hinfB hDl hall
      (2 * n + T.length + 9) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),(⟨s64,inf⟩ : Cell)]).take caller.scalars.memory.length =
      caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),(⟨s64,inf⟩ : Cell)],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]⟩ : PS) = gS (callerP caller) [ci n, Proofs.BellmanFordExec.cs inf] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  have gw2 := g2.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1 gw2
  have hEd := edges_ok H T C n inf HK hTn hCl hC0
  have hEm : ∀ e ∈ Eall n (outEdges H T C), e.1 < n ∧ e.2.1 < n ∧ 0 ≤ e.2.2 ∧ e.2.2 ≤ Cm := by
    intro e he
    obtain ⟨u, hu, hmem⟩ := Proofs.DijkstraMath.mem_Eall_inv n (outEdges H T C) e he
    obtain ⟨h1, p, hp, h2, h3⟩ := outEdges_range H T C n HK hCl u hu e hmem
    have hmemC := Proofs.BellmanFordExec.getD_mem C p (by omega)
    have hE := hEd e he
    refine ⟨hE.1, hE.2.1, hE.2.2.1, ?_⟩
    rw [h3]; exact hCm _ hmemC
  have hpk : ∀ x ∈ pk, 0 ≤ x := by
    intro x hx
    exact (Proofs.PrimStep.pk_bounds hI Cm hCm0 (fun e he => ⟨(hEm e he).2.2.1, (hEm e he).2.2.2⟩) x hx).1
  obtain ⟨hmsf, hcast⟩ := prim_msf hI hDn hCm0 hEm hsym hpk
  have hv : s64.valid pk.sum = true := Proofs.BellmanFordExec.s64_valid_of pk.sum (by omega)
  have hpost := call_vecm (mvDJ V0 V1 V2 V3 V4 vsc0 vsc1 vsc2 vsc3 vsc4 m0 m1 m2 caller.frame.state.liveSpace
        caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h03 h13 h23 h04 h14 h24 h34)
    (fun k => decide (k = 3 ∨ k = 4))
    (by intro k hk; have : k = 3 ∨ k = 4 := by simpa using hk
        rcases this with rfl | rfl <;> simp [mvDJ])
    caller Proofs.PrimInstance.prim_std_vector_int
    [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3,.vectorReference s4,.value e1,.value e2] Sinit
    (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),(⟨s64,inf⟩ : Cell)])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [body_eqPR5]; exact wr_bodyPR)
    (2 * n + T.length + 9) rr (by rw [hmk, body_eqPR5]; exact hexec) pk.sum hret s64 rfl hv
    (by omega) (by simp [hlenP]) (e1.nodes + e2.nodes) ((640 * n + 760) * n + 420 * T.length + 150) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,(pk.map Int.toNat).sum,Dd,Dn,hprep,?_,hmsf,?_⟩
  · rw [hcast]; exact hrun
  · have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
      rw [hrps]
      simp only [gS_mem, callerP, List.append_assoc]
      rw [List.take_append_of_le_length (by simp)]
      exact List.take_length
    rw [hs', hrvv] at post
    exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk

end Proofs.PrimCall
