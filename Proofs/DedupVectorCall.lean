import Proofs.VectorFillCall
import Proofs.Generated.SortUtil

namespace Proofs.DedupVectorCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.StraightLine Proofs.Mod61Body Proofs.VecExpr Proofs.VecStraight Proofs.VecCall Proofs.VecKit
open Proofs.CppNestedFacts Proofs.IntSim Proofs.ScalarCall Proofs.VecWrite Proofs.VecWriteCall Proofs.VecKitW
open Proofs.VectorFillCall (VOKW take_P)
open Proofs.CppState (Cell)

abbrev dedupS : NStmt := .dedupVec (.local 0) s64
abbrev bodyCmdD : Command := .sequence (.primitive dedupS) (.primitive .skip)

theorem body_eq : Proofs.SortUtilInstance.dedup_vector_std_vector_long_long.body = bodyCmdD := rfl

theorem pstmt_dedup (P : List Cell) (vec : List Int) :
    pstmtW s64 dedupS ⟨P,[]⟩ vec = some ⟨⟨P,[]⟩,uniqAdj vec,none,3,P.length+3,
      vec.length + vec.length⟩ := by
  simp [pstmtW]

theorem body_execD (P : List Cell) (vec : List Int) (fu : Nat) :
    ∃ r, pexecW s64 fu bodyCmdD ⟨P,[]⟩ vec = some r ∧ r.ps = ⟨P,[]⟩ ∧
      r.vec = uniqAdj vec ∧ r.ret = none ∧ r.cost = 3 ∧ r.need = P.length+3 ∧
      r.wk = vec.length + vec.length := by
  have a1 := (pexecW_prim s64 fu dedupS _ _).trans (pstmt_dedup P vec)
  have a2 := seqW_some a1 rfl (pexecW_skip s64 fu ⟨P,[]⟩ (uniqAdj vec))
  refine ⟨_, a2, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp

theorem prepare_dv (caller : NState) {vslot vb V vsc : Nat} {vbuf : Buffer Value}
    (ok : VOKW caller vslot vb V vsc vbuf) :
    ∃ Sinit, prepare caller Proofs.SortUtilInstance.dedup_vector_std_vector_long_long.parameters [.vectorReference vslot] = some Sinit ∧
        Sinit.slots = [.vector 0] ∧ Sinit.scalars.memory = callerP caller ∧
        Sinit.scalars.bindings = [] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer s64,true,.root vsc⟩]⟩ ∧
        Sinit.scalars.work = caller.scalars.work+3 ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨resolved,_,_⟩ := resolve_vroot caller.frame vb V vsc s64 true true vbuf ok.binding ok.valid ok.vtag ok.vfound
    ok.lengths ok.flag (fun _ => rfl)
  have rvec : resolve caller (.vector s64 true) (.vectorReference vslot) =
      some (caller.charge 1 1,.vector V vsc s64 true) := by
    simp [resolve,ok.slot,ok.binding,resolved]
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
  have hp : Proofs.SortUtilInstance.dedup_vector_std_vector_long_long.parameters = [.vector s64 true] := rfl
  rw [hp]
  simp [prepare,ok.valid,resolveAll,rvec]
  simp [bound,bindAll,bindOne,CppState.bindArgument,callerP,NState.observe,CppState.State.observe]
  exact ⟨charge_work caller 1 1,by simp [charge_scalar_peak]; exact Nat.le_max_left _ _⟩

set_option maxHeartbeats 4000000 in
theorem dedup_vector_correct (caller : NState) {vslot vb V vsc : Nat} {vbuf : Buffer Value}
    (ok : VOKW caller vslot vb V vsc vbuf) (vec : List Int) (hitems : vbuf.items = vec.map Value.integer)
    (hbvalid : vbuf.Valid (accepts (.integer s64))) (hlimit : vbuf.limit = CppVectorBindings.sizeLimit s64)
    (howner : vbuf.owner = V) (hn : vec.length < 2147483648) :
    ∃ Sinit fuel res, prepare caller Proofs.SortUtilInstance.dedup_vector_std_vector_long_long.parameters
        [.vectorReference vslot] = some Sinit ∧
      Proofs.SortUtilInstance.dedup_vector_std_vector_long_long.callFuel fuel caller [.vectorReference vslot] =
        .finished (res,Ret.unit) ∧
      ScalarPost3 caller Sinit res 0 7 caller.scalars.memory
        (vec.length + vec.length) V
        (uniqAdj vec) := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ := prepare_dv caller ok
  let vc : VCtx := ⟨s64,true,true,V,vsc,vbuf,vec,hitems,fun _ => rfl,by omega,caller.frame.state.liveSpace,
    caller.frame.state.storage.work,caller.scope+1,caller.frame.state.storage.objects.length⟩
  have fwS : FW vc vec vbuf 0 Sinit.frame := by
    rw [sFrame]
    refine ⟨ok.valid,ok.lengths,rfl,rfl,?_,rfl,rfl,ok.vtag,ok.vfound,ok.flag,hitems,hbvalid,hlimit,howner,by omega⟩
    intro owner k h
    have := ok.strict owner k h
    show k < caller.scope+1
    omega
  obtain ⟨r,hexec,hrps,hrvec,hret,hcost,hneed,hwk⟩ := body_execD (callerP caller) vec 1
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simpa using take_P caller []
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have hpost := call_vecw_unit vc true (fun _ => ⟨rfl,rfl⟩) caller Proofs.SortUtilInstance.dedup_vector_std_vector_long_long [.vectorReference vslot] Sinit
    (callerP caller) []
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlen]) (by rw [takeM]) ok.base (by decide) 1 r
    (by rw [body_eq]; exact hexec) hret rfl (by omega) (by simp) 0 7 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]; exact takeM
  rw [hs'] at post
  rw [hrvec, hwk] at post
  exact post


theorem uniqAdjAux_sorted : ∀ (t : List Int) (p : Int), (p :: t).Pairwise (fun a b => a ≤ b) →
    (uniqAdjAux p t).Pairwise (fun a b => a < b) ∧ ∀ x, x ∈ uniqAdjAux p t ↔ x ∈ t ∧ p < x
  | [], p, _ => by simp [uniqAdjAux]
  | y :: t, p, h => by
    rw [List.pairwise_cons] at h
    obtain ⟨hp, ht⟩ := h
    rw [List.pairwise_cons] at ht
    obtain ⟨hy, ht'⟩ := ht
    have hpy : p ≤ y := hp y (List.mem_cons_self ..)
    by_cases e : y = p
    · simp only [uniqAdjAux, e, if_true]
      have hpt : (p :: t).Pairwise (fun a b => a ≤ b) :=
        List.pairwise_cons.mpr ⟨fun b hb => hp b (List.mem_cons_of_mem _ hb), ht'⟩
      obtain ⟨ih1, ih2⟩ := uniqAdjAux_sorted t p hpt
      refine ⟨ih1, fun x => ?_⟩
      rw [ih2 x]
      simp only [List.mem_cons]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨Or.inr h1, h2⟩
      · rintro ⟨h1 | h1, h2⟩
        · exact absurd (e ▸ h1 ▸ h2) (by omega)
        · exact ⟨h1, h2⟩
    · simp only [uniqAdjAux, e, if_false]
      have hlt : p < y := by omega
      have hyt : (y :: t).Pairwise (fun a b => a ≤ b) := List.pairwise_cons.mpr ⟨hy, ht'⟩
      obtain ⟨ih1, ih2⟩ := uniqAdjAux_sorted t y hyt
      refine ⟨List.pairwise_cons.mpr ⟨fun b hb => ((ih2 b).mp hb).2, ih1⟩, fun x => ?_⟩
      simp only [List.mem_cons, ih2 x]
      constructor
      · rintro (h1 | ⟨h1, h2⟩)
        · exact ⟨Or.inl h1, by omega⟩
        · exact ⟨Or.inr h1, by omega⟩
      · rintro ⟨h1 | h1, h2⟩
        · exact Or.inl h1
        · have := hy x h1
          by_cases hxy : x = y
          · exact Or.inl hxy
          · exact Or.inr ⟨h1, by omega⟩

/-- On an ascending input, `dedup_vector` leaves a strictly ascending vector with the same set of elements. -/
theorem uniqAdj_sorted_spec (l : List Int) (h : l.Pairwise (fun a b => a ≤ b)) :
    (uniqAdj l).Pairwise (fun a b => a < b) ∧ ∀ x, x ∈ uniqAdj l ↔ x ∈ l := by
  cases l with
  | nil => simp [uniqAdj]
  | cons a t =>
    obtain ⟨h1, h2⟩ := uniqAdjAux_sorted t a h
    rw [List.pairwise_cons] at h
    refine ⟨List.pairwise_cons.mpr ⟨fun b hb => ((h2 b).mp hb).2, h1⟩, fun x => ?_⟩
    simp only [uniqAdj, List.mem_cons, h2 x]
    constructor
    · rintro (h3 | ⟨h3, _⟩)
      · exact Or.inl h3
      · exact Or.inr h3
    · rintro (h3 | h3)
      · exact Or.inl h3
      · by_cases hxa : x = a
        · exact Or.inl hxa
        · exact Or.inr ⟨h3, by have := h.1 x h3; omega⟩
