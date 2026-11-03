import Proofs.BeatsPrepGen
import Proofs.MultiVecCallB
namespace Proofs.BeatsPrepare
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCallB
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare

/-- The callee: `nv` flat vector parameters given by functions. -/
def mvB (nv : Nat) (ty : Nat → Ty) (w m : Nat → Bool) (V vsc : Nat → Nat) (hperm : ∀ k, w k = true → m k = true)
    (hdist : ∀ j k, j < nv → k < nv → j ≠ k → w k = true → V j ≠ V k) (L0 T0 sc N : Nat) : MV where
  nv := nv
  ty := ty
  wV := w
  flag := m
  R := V
  vsc := vsc
  perm := hperm
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := hdist

theorem fw_init (caller : NState) (nv : Nat) (hnv : 0 < nv) (ty : Nat → Ty) (w : Nat → Bool) (sl vb V vsc : Nat → Nat) (m : Nat → Bool)
    (vbuf : Nat → Buffer Value) (hok : ∀ i, i < nv → VOKG caller (ty i) (sl i) (vb i) (V i) (vsc i) (w i) (m i) (vbuf i))
    (hperm : ∀ k, w k = true → m k = true) (hdist : ∀ j k, j < nv → k < nv → j ≠ k → w k = true → V j ≠ V k)
    (vv0 : Nat → List Int) (hitems : ∀ k, k < nv → (vbuf k).items = (vv0 k).map Value.integer)
    (hbv : ∀ k, k < nv → (vbuf k).Valid (accepts (.integer (ty k))))
    (hlim : ∀ k, k < nv → (vbuf k).limit = CppVectorBindings.sizeLimit (ty k))
    (how : ∀ k, k < nv → (vbuf k).owner = V k) (hsmall : ∀ k, k < nv → (vv0 k).length < 18446744073709551616) :
    FWM (mvB nv ty w m V vsc hperm hdist caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length) vv0 vbuf 0
      (⟨caller.frame.state, caller.frame.rootWritable, bl ty V vsc w 0 nv⟩ : Frame) := by
  refine ⟨(hok 0 hnv).valid, (hok 0 hnv).lengths, rfl, rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := (hok 0 hnv).strict owner k h
    show k < caller.scope + 1
    omega
  · simp [bl, bindOf, mvB, List.range_eq_range']
  · intro k hk; exact (hok k hk).vtag
  · intro k hk; exact (hok k hk).vfound
  · intro k hk; exact (hok k hk).flag
  · exact hitems
  · exact hbv
  · exact hlim
  · exact how
  · exact hsmall


set_option maxHeartbeats 64000000 in
/-- The call of a method with `nv` flat vector parameters and the scalar arguments `L`, returning nothing. -/
theorem beats_call_unit (B : Nat) (caller : NState) (nv : Nat) (hnv : 0 < nv) (ty : Nat → Ty) (w : Nat → Bool) (sl vb V vsc : Nat → Nat) (m : Nat → Bool)
    (vbuf : Nat → Buffer Value) (hok : ∀ i, i < nv → VOKG caller (ty i) (sl i) (vb i) (V i) (vsc i) (w i) (m i) (vbuf i))
    (hperm : ∀ k, w k = true → m k = true) (hdist : ∀ j k, j < nv → k < nv → j ≠ k → w k = true → V j ≠ V k)
    (wp : Nat → Bool) (hwp : ∀ k, wp k = true → w k = true ∧ m k = true)
    (L : List (NExpr × Ty × Int)) (prog : NProgram)
    (hp : prog.parameters = vparams ty w 0 nv ++ L.map (fun x => CppVectorBindings.Parameter.scalar x.2.1 false true))
    (hL : ∀ x ∈ L, x.1.scalarOnly = true ∧ x.1.resultType = x.2.1 ∧ x.1.denote (envOf caller) = some x.2.2 ∧ x.2.1.valid x.2.2 = true)
    (vv0 : Nat → List Int) (hitems : ∀ k, k < nv → (vbuf k).items = (vv0 k).map Value.integer)
    (hbv : ∀ k, k < nv → (vbuf k).Valid (accepts (.integer (ty k))))
    (hlim : ∀ k, k < nv → (vbuf k).limit = CppVectorBindings.sizeLimit (ty k))
    (how : ∀ k, k < nv → (vbuf k).owner = V k) (hsmall : ∀ k, k < nv → (vv0 k).length < 18446744073709551616)
    (hwr : WrM wp prog.body = true) (hres : prog.result = ResultKind.unit)
    (fu : Nat) (r : PRM)
    (hexec : pexecM (mvB nv ty w m V vsc hperm hdist caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length) fu prog.body
        ⟨callerP caller ++ L.map (fun x => (⟨x.2.1, x.2.2⟩ : Cell)),
         (List.range L.length).map (fun j => (⟨(callerP caller).length + j, true⟩ : CppState.Binding))⟩ vv0 = some r)
    (hret : r.ret = none)
    (hneed : r.need ≤ (callerP caller).length + (B + 12))
    (hlive0 : (callerP caller ++ L.map (fun x => (⟨x.2.1, x.2.2⟩ : Cell))).length + L.length ≤ (callerP caller).length + B)
    (extra : Nat) (hextra : r.cost + 2 * nv + L.length + 2 ≤ extra) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller prog.parameters (vargs sl 0 nv ++ L.map (fun x => NArgument.value x.1)) = some Sinit ∧
      prog.callFuel fuel caller (vargs sl 0 nv ++ L.map (fun x => NArgument.value x.1)) = .finished (res, Ret.unit) ∧
      ScalarPostMB B (mvB nv ty w m V vsc hperm hdist caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
          caller.frame.state.storage.objects.length) caller Sinit res (L.map (fun x => x.1.nodes)).sum extra
        (r.ps.mem.take caller.scalars.memory.length) r.wk r.vv := by
  obtain ⟨last, hg, Sinit, hprep, sSlots, sMem, sBind, sBase, sScope, sFrame, sWork, sPeak1, sPeak2⟩ :=
    prepare_gen caller nv hnv ty w sl vb V vsc m vbuf hok L prog hp hL
  have fwS := fw_init caller nv hnv ty w sl vb V vsc m vbuf hok hperm hdist vv0 hitems hbv hlim how hsmall
  rw [← sFrame] at fwS
  have takeM : (callerP caller ++ L.map (fun x => (⟨x.2.1, x.2.2⟩ : Cell))).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hlenP : (callerP caller).length = caller.scalars.memory.length + (caller.scalars.bindings.length + caller.frame.bindings.length) := by
    simp [callerP]
  have hnodes : last.scalars.work ≤ caller.scalars.work + nv + (L.map (fun x => x.1.nodes)).sum := by
    have h1 := hg.2.2.1
    rw [chargeN_work] at h1; omega
  have hpost := call_vecm_unitB B (mvB nv ty w m V vsc hperm hdist caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
      caller.frame.state.storage.objects.length) wp hwp caller prog
    (vargs sl 0 nv ++ L.map (fun x => NArgument.value x.1)) Sinit
    (callerP caller ++ L.map (fun x => (⟨x.2.1, x.2.2⟩ : Cell)))
    ((List.range L.length).map (fun j => (⟨(callerP caller).length + j, true⟩ : CppState.Binding)))
    hprep (by rw [sSlots]; simp only [List.length_map, List.length_range]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) (hok 0 hnv).base hwr fu r hexec hret hres hneed (by simpa using hlive0)
    (L.map (fun x => x.1.nodes)).sum extra (by omega)
  obtain ⟨fuel, res, hrun, post⟩ := hpost
  exact ⟨Sinit, fuel, res, hprep, hrun, post⟩

set_option maxHeartbeats 64000000 in
/-- The call of a method with `nv` flat vector parameters and the scalar arguments `L`, returning the scalar `v`. -/
theorem beats_call_val (B : Nat) (caller : NState) (nv : Nat) (hnv : 0 < nv) (ty : Nat → Ty) (w : Nat → Bool) (sl vb V vsc : Nat → Nat) (m : Nat → Bool)
    (vbuf : Nat → Buffer Value) (hok : ∀ i, i < nv → VOKG caller (ty i) (sl i) (vb i) (V i) (vsc i) (w i) (m i) (vbuf i))
    (hperm : ∀ k, w k = true → m k = true) (hdist : ∀ j k, j < nv → k < nv → j ≠ k → w k = true → V j ≠ V k)
    (wp : Nat → Bool) (hwp : ∀ k, wp k = true → w k = true ∧ m k = true)
    (L : List (NExpr × Ty × Int)) (prog : NProgram)
    (hp : prog.parameters = vparams ty w 0 nv ++ L.map (fun x => CppVectorBindings.Parameter.scalar x.2.1 false true))
    (hL : ∀ x ∈ L, x.1.scalarOnly = true ∧ x.1.resultType = x.2.1 ∧ x.1.denote (envOf caller) = some x.2.2 ∧ x.2.1.valid x.2.2 = true)
    (vv0 : Nat → List Int) (hitems : ∀ k, k < nv → (vbuf k).items = (vv0 k).map Value.integer)
    (hbv : ∀ k, k < nv → (vbuf k).Valid (accepts (.integer (ty k))))
    (hlim : ∀ k, k < nv → (vbuf k).limit = CppVectorBindings.sizeLimit (ty k))
    (how : ∀ k, k < nv → (vbuf k).owner = V k) (hsmall : ∀ k, k < nv → (vv0 k).length < 18446744073709551616)
    (hwr : WrM wp prog.body = true) (rty : Ty) (hres : prog.result = ResultKind.scalar rty)
    (fu : Nat) (r : PRM)
    (hexec : pexecM (mvB nv ty w m V vsc hperm hdist caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length) fu prog.body
        ⟨callerP caller ++ L.map (fun x => (⟨x.2.1, x.2.2⟩ : Cell)),
         (List.range L.length).map (fun j => (⟨(callerP caller).length + j, true⟩ : CppState.Binding))⟩ vv0 = some r)
    (v : Int) (hret : r.ret = some v) (hv : rty.valid v = true)
    (hneed : r.need ≤ (callerP caller).length + (B + 12))
    (hlive0 : (callerP caller ++ L.map (fun x => (⟨x.2.1, x.2.2⟩ : Cell))).length + L.length ≤ (callerP caller).length + B)
    (extra : Nat) (hextra : r.cost + 2 * nv + L.length + 2 ≤ extra) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller prog.parameters (vargs sl 0 nv ++ L.map (fun x => NArgument.value x.1)) = some Sinit ∧
      prog.callFuel fuel caller (vargs sl 0 nv ++ L.map (fun x => NArgument.value x.1)) = .finished (res, Ret.scalar v) ∧
      ScalarPostMB B (mvB nv ty w m V vsc hperm hdist caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
          caller.frame.state.storage.objects.length) caller Sinit res (L.map (fun x => x.1.nodes)).sum extra
        (r.ps.mem.take caller.scalars.memory.length) r.wk r.vv := by
  obtain ⟨last, hg, Sinit, hprep, sSlots, sMem, sBind, sBase, sScope, sFrame, sWork, sPeak1, sPeak2⟩ :=
    prepare_gen caller nv hnv ty w sl vb V vsc m vbuf hok L prog hp hL
  have fwS := fw_init caller nv hnv ty w sl vb V vsc m vbuf hok hperm hdist vv0 hitems hbv hlim how hsmall
  rw [← sFrame] at fwS
  have takeM : (callerP caller ++ L.map (fun x => (⟨x.2.1, x.2.2⟩ : Cell))).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hlenP : (callerP caller).length = caller.scalars.memory.length + (caller.scalars.bindings.length + caller.frame.bindings.length) := by
    simp [callerP]
  have hnodes : last.scalars.work ≤ caller.scalars.work + nv + (L.map (fun x => x.1.nodes)).sum := by
    have h1 := hg.2.2.1
    rw [chargeN_work] at h1; omega
  have hpost := call_vecmB B (mvB nv ty w m V vsc hperm hdist caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
      caller.frame.state.storage.objects.length) wp hwp caller prog
    (vargs sl 0 nv ++ L.map (fun x => NArgument.value x.1)) Sinit
    (callerP caller ++ L.map (fun x => (⟨x.2.1, x.2.2⟩ : Cell)))
    ((List.range L.length).map (fun j => (⟨(callerP caller).length + j, true⟩ : CppState.Binding)))
    hprep (by rw [sSlots]; simp only [List.length_map, List.length_range]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) (hok 0 hnv).base hwr fu r hexec v hret rty hres hv hneed (by simpa using hlive0)
    (L.map (fun x => x.1.nodes)).sum extra (by omega)
  obtain ⟨fuel, res, hrun, post⟩ := hpost
  exact ⟨Sinit, fuel, res, hprep, hrun, post⟩

end Proofs.BeatsPrepare
