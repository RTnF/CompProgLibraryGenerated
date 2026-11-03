import Proofs.VectorFillCall
import Proofs.Generated.SortUtil

namespace Proofs.SortVectorCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.StraightLine Proofs.Mod61Body Proofs.VecExpr Proofs.VecStraight Proofs.VecCall Proofs.VecKit
open Proofs.CppNestedFacts Proofs.IntSim Proofs.ScalarCall Proofs.VecWrite Proofs.VecWriteCall Proofs.VecKitW
open Proofs.VectorFillCall (VOKW take_P)
open Proofs.CppState (Cell)

abbrev sortS : NStmt := .sortVec (.local 0) s64
abbrev bodyCmdS : Command := .sequence (.primitive sortS) (.primitive .skip)

theorem body_eq : Proofs.SortUtilInstance.sort_vector_std_vector_long_long.body = bodyCmdS := rfl

theorem pstmt_sort (P : List Cell) (vec : List Int) :
    pstmtW s64 sortS ⟨P,[]⟩ vec = some ⟨⟨P,[]⟩,vec.mergeSort (fun x y => decide (x ≤ y)),none,3,P.length+3,
      Proofs.StlContracts.sortComparisons vec.length + vec.length⟩ := by
  simp [pstmtW]

theorem body_execS (P : List Cell) (vec : List Int) (fu : Nat) :
    ∃ r, pexecW s64 fu bodyCmdS ⟨P,[]⟩ vec = some r ∧ r.ps = ⟨P,[]⟩ ∧
      r.vec = vec.mergeSort (fun x y => decide (x ≤ y)) ∧ r.ret = none ∧ r.cost = 3 ∧ r.need = P.length+3 ∧
      r.wk = Proofs.StlContracts.sortComparisons vec.length + vec.length := by
  have a1 := (pexecW_prim s64 fu sortS _ _).trans (pstmt_sort P vec)
  have a2 := seqW_some a1 rfl (pexecW_skip s64 fu ⟨P,[]⟩ (vec.mergeSort (fun x y => decide (x ≤ y))))
  refine ⟨_, a2, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp

theorem prepare_sv (caller : NState) {vslot vb V vsc : Nat} {vbuf : Buffer Value}
    (ok : VOKW caller vslot vb V vsc vbuf) :
    ∃ Sinit, prepare caller Proofs.SortUtilInstance.sort_vector_std_vector_long_long.parameters [.vectorReference vslot] = some Sinit ∧
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
  have hp : Proofs.SortUtilInstance.sort_vector_std_vector_long_long.parameters = [.vector s64 true] := rfl
  rw [hp]
  simp [prepare,ok.valid,resolveAll,rvec]
  simp [bound,bindAll,bindOne,CppState.bindArgument,callerP,NState.observe,CppState.State.observe]
  exact ⟨charge_work caller 1 1,by simp [charge_scalar_peak]; exact Nat.le_max_left _ _⟩

set_option maxHeartbeats 4000000 in
theorem sort_vector_correct (caller : NState) {vslot vb V vsc : Nat} {vbuf : Buffer Value}
    (ok : VOKW caller vslot vb V vsc vbuf) (vec : List Int) (hitems : vbuf.items = vec.map Value.integer)
    (hbvalid : vbuf.Valid (accepts (.integer s64))) (hlimit : vbuf.limit = CppVectorBindings.sizeLimit s64)
    (howner : vbuf.owner = V) (hn : vec.length < 2147483648) :
    ∃ Sinit fuel res, prepare caller Proofs.SortUtilInstance.sort_vector_std_vector_long_long.parameters
        [.vectorReference vslot] = some Sinit ∧
      Proofs.SortUtilInstance.sort_vector_std_vector_long_long.callFuel fuel caller [.vectorReference vslot] =
        .finished (res,Ret.unit) ∧
      ScalarPost3 caller Sinit res 0 7 caller.scalars.memory
        (Proofs.StlContracts.sortComparisons vec.length + vec.length) V
        (vec.mergeSort (fun x y => decide (x ≤ y))) := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ := prepare_sv caller ok
  let vc : VCtx := ⟨s64,true,true,V,vsc,vbuf,vec,hitems,fun _ => rfl,by omega,caller.frame.state.liveSpace,
    caller.frame.state.storage.work,caller.scope+1,caller.frame.state.storage.objects.length⟩
  have fwS : FW vc vec vbuf 0 Sinit.frame := by
    rw [sFrame]
    refine ⟨ok.valid,ok.lengths,rfl,rfl,?_,rfl,rfl,ok.vtag,ok.vfound,ok.flag,hitems,hbvalid,hlimit,howner,by omega⟩
    intro owner k h
    have := ok.strict owner k h
    show k < caller.scope+1
    omega
  obtain ⟨r,hexec,hrps,hrvec,hret,hcost,hneed,hwk⟩ := body_execS (callerP caller) vec 1
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simpa using take_P caller []
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have hpost := call_vecw_unit vc true (fun _ => ⟨rfl,rfl⟩) caller Proofs.SortUtilInstance.sort_vector_std_vector_long_long [.vectorReference vslot] Sinit
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

/-- The result of `sort_vector` is ascending and a rearrangement of the input. -/
theorem sorted_result_spec (vec : List Int) :
    (vec.mergeSort (fun x y => decide (x ≤ y))).Pairwise (fun x y => x ≤ y) ∧
      (vec.mergeSort (fun x y => decide (x ≤ y))).Perm vec := by
  refine ⟨?_, List.mergeSort_perm _ _⟩
  have := List.pairwise_mergeSort (le := fun x y : Int => decide (x ≤ y))
    (fun a b c h1 h2 => by simp at h1 h2 ⊢; omega) (fun a b => by simp; omega) vec
  simpa using this

/-- Under the STL contract `sort_comparisons_bound`, the model work of `sort_vector` is O(n log n). -/
theorem sort_vector_work_bound :
    ∃ c : Nat, ∀ n : Nat, Proofs.StlContracts.sortComparisons n + n ≤ (c+1) * n * (Nat.log2 n + 1) := by
  obtain ⟨c, hc⟩ := Proofs.StlContracts.sort_comparisons_bound
  refine ⟨c, fun n => ?_⟩
  have h := hc n
  have : n ≤ n * (Nat.log2 n + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  calc _ ≤ c * n * (Nat.log2 n + 1) + n * (Nat.log2 n + 1) := by omega
    _ = (c+1) * n * (Nat.log2 n + 1) := by rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
