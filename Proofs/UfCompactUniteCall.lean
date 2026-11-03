import Proofs.UfCompactUniteBody
import Proofs.CppMoveCallBindings
import Proofs.UfFieldsUnite
namespace Proofs.UfCompactUniteCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppMoveContext Proofs.CppMoveHeaders Proofs.CppMovePreparedCall
open Proofs.CppMoveCallBindings Proofs.UfCompactRootBody
open Proofs.CppVector Proofs.CppNestedVectorStore Proofs.StraightLine
open Proofs.VecExpr Proofs.VecWrite Proofs.QuotientFrame
open Proofs.UfRootCall Proofs.UfCompression Proofs.DoublingNested
open Proofs.UfCompactUniteBody
open Proofs.CppState (Cell)

theorem set_types (P : List Cell) (counter : Nat) (groups next : Int)
    (found : P[counter]? = some ⟨i32,groups⟩) :
    (P.set counter ⟨i32,next⟩).map Cell.type = P.map Cell.type := by
  induction P generalizing counter with
  | nil => simp at found
  | cons head tail ih =>
    cases counter with
    | zero =>
      have eq : head = ⟨i32,groups⟩ := Option.some.inj found
      subst head
      rfl
    | succ counter =>
      change head.type::(tail.set counter ⟨i32,next⟩).map Cell.type = head.type::tail.map Cell.type
      rw [ih counter found]

theorem updated_types (P : List Cell) (counter : Nat) (groups : Int) (r1 r2 : Nat)
    (found : P[counter]? = some ⟨i32,groups⟩) :
    (Proofs.UfFieldsUnite.updatedMemory P counter groups r1 r2).map Cell.type = P.map Cell.type := by
  by_cases same : r1=r2
  · simp [Proofs.UfFieldsUnite.updatedMemory,same]
  · simpa only [Proofs.UfFieldsUnite.updatedMemory,ite_eq_right same] using set_types P counter groups (groups-1) found

theorem updated_length (P : List Cell) (counter : Nat) (groups : Int) (r1 r2 : Nat) :
    (Proofs.UfFieldsUnite.updatedMemory P counter groups r1 r2).length = P.length := by
  by_cases same : r1=r2 <;> simp [Proofs.UfFieldsUnite.updatedMemory,same]

theorem unite_call (caller prepared : Context) (initial : NState) (arguments : List Proofs.CppNestedCall.NArgument)
    (vc : VCtx) (vec : List Int) (rank : Nat → Nat) (groups : Int) (valid : Proofs.UfClassInvariant.Valid vec groups rank) (a b : Nat) (ha : a < vec.length) (hb : b < vec.length)
    (P : List Cell) (counter : Nat) (countFound : P[counter]? = some ⟨i32,groups⟩) (buf : Buffer Value) (ty : vc.ty = i32)
    (permission : vc.wV = true ∧ vc.flag = true)
    (preparedRun : prepareArguments caller i32 Proofs.UnionFindCandidateInstance.UnionFind_unite.parameters arguments = some prepared)
    (compacted : compact (project prepared i32) = some initial)
    (qs : QS initial [] initial.scalars.baseMemory initial.scope
      (Proofs.UfFieldsSame.fields P ⟨counter,true⟩ vec.length a b).mem
      (Proofs.UfFieldsSame.fields P ⟨counter,true⟩ vec.length a b).bs
      (sl1 (Proofs.UfFieldsSame.fields P ⟨counter,true⟩ vec.length a b).bs.length))
    (frame : FW vc vec buf 0 initial.frame)
    (baseline : initial.scalars.baseMemory ≤ P.length) (scope : vc.sc ≤ initial.scope)
    (prefixLength : caller.scalars.memory.length ≤ P.length)
    (prefixMemory : P.take caller.scalars.memory.length = caller.scalars.memory)
    (contexts : ∀ owner sc, (project caller i32).frame.state.forest.context owner = some sc → sc ≤ caller.scope)
    (covered : OwnsAll caller.objects.heap) :
    ∃ (fuel : Nat) (out : Context) (r1 r2 : Nat) (middle two final : List Int),
      callFuel Proofs.UnionFindCandidateInstance.UnionFind_unite fuel caller i32 arguments = .finished (out,.scalar (Proofs.UfUniteCall.uniteX two r1 r2 : Int)) ∧
      Compressed vec middle a r1 ∧ Compressed middle two b r2 ∧
      final = Proofs.UfUniteCall.uniteVec two r1 r2 ∧
      (∃ rank', Proofs.UfClassInvariant.Valid final (Proofs.UfFieldsUnite.countAfter groups r1 r2) rank') ∧
      (r1=r2 ↔ Proofs.UfFieldsSame.Connected vec a b) ∧
      work out ≤ work prepared+91*rank a+91*rank b+343 ∧
      out.scalars.memory = Proofs.UfFieldsUnite.updatedMemory caller.scalars.memory counter groups r1 r2 ∧
      out.scalars.peak ≤ max (max caller.scalars.peak (uniteScalarBudget initial P.length initial.scalars.baseMemory))
        (caller.scalars.memory.length-caller.scalars.baseMemory+caller.scalars.bindings.length) ∧
      out.objects.heap.peak ≤ storageBudget initial vc.L0 ∧
      out.peak ≤ max (max caller.peak (uniteScalarBudget initial P.length initial.scalars.baseMemory+storageBudget initial vc.L0))
        (max (max caller.scalars.peak (uniteScalarBudget initial P.length initial.scalars.baseMemory))
          (caller.scalars.memory.length-caller.scalars.baseMemory+caller.scalars.bindings.length)+storageBudget initial vc.L0) ∧
      ∃ buffer, (project out i32).frame.state.storage.lookup vc.R = some buffer ∧ buffer.items = final.map Value.integer := by
  obtain ⟨fuel,step,r1,r2,middle,two,final,ran,returned,breaking,c1,c2,finalEq,newValid,resultValid,connected,saved,cost,scalarPeak,heapPeak,outerPeak,live,baseEq,buffer,found,items⟩ :=
    unite_body initial vc vec rank groups valid a b ha hb P counter countFound buf ty permission qs frame baseline scope
  have stepEq : step = ⟨step.state,some (.scalar (Proofs.UfUniteCall.uniteX two r1 r2 : Int)),false⟩ := by
    cases step with
    | mk state ret brk => simp_all
  have run : Proofs.CppNestedProgram.runFuel fuel Proofs.UnionFindCandidateInstance.UnionFind_unite.body initial =
      .finished ⟨step.state,some (.scalar (Proofs.UfUniteCall.uniteX two r1 r2 : Int)),false⟩ := by rw [← stepEq]; exact ran
  have savedCaller : step.state.scalars.memory.take caller.scalars.memory.length =
      Proofs.UfFieldsUnite.updatedMemory caller.scalars.memory counter groups r1 r2 := by
    calc _ = (step.state.scalars.memory.take P.length).take caller.scalars.memory.length := by
           rw [List.take_take,Nat.min_eq_left prefixLength]
         _ = (Proofs.UfFieldsUnite.updatedMemory P counter groups r1 r2).take caller.scalars.memory.length := by rw [saved]
         _ = Proofs.UfFieldsUnite.updatedMemory caller.scalars.memory counter groups r1 r2 := by
           rw [Proofs.UfFieldsUnite.updated_take,prefixMemory]
  have fits : caller.scalars.memory.length ≤ step.state.scalars.memory.length := by
    have sizes := congrArg List.length savedCaller
    rw [updated_length] at sizes
    simp only [List.length_take] at sizes
    omega
  have types : (step.state.scalars.memory.take caller.scalars.memory.length).map Cell.type = caller.scalars.memory.map Cell.type := by
    calc _ = ((step.state.scalars.memory.take P.length).take caller.scalars.memory.length).map Cell.type := by
           rw [List.take_take,Nat.min_eq_left prefixLength]
         _ = ((Proofs.UfFieldsUnite.updatedMemory P counter groups r1 r2).take caller.scalars.memory.length).map Cell.type := by rw [saved]
         _ = (P.take caller.scalars.memory.length).map Cell.type := by
           simpa only [List.map_take] using congrArg (List.take caller.scalars.memory.length) (updated_types P counter groups r1 r2 countFound)
         _ = caller.scalars.memory.map Cell.type := by rw [prefixMemory]
  have compactData := compact_metadata (project prepared i32) initial compacted
  have prep := prepareArguments_effects caller prepared i32 Proofs.UnionFindCandidateInstance.UnionFind_unite.parameters arguments preparedRun
  have state : initial.frame.state = (project caller i32).frame.state := by
    rw [compactData.1]
    simp only [project,Proofs.CppMoveFrame.materialize,prep.1]
  have valid : (project caller i32).frame.state.wellFormed = true := by rw [← state]; exact frame.valid
  obtain ⟨out,actual,workEq,memoryEq,lookups,scalarEq,heapEq,peakEq⟩ := call_of_body
    Proofs.UnionFindCandidateInstance.UnionFind_unite fuel caller prepared initial i32 i32 arguments step.state (Proofs.UfUniteCall.uniteX two r1 r2 : Int)
    rfl (by decide) contexts covered valid preparedRun compacted run fits types resultValid
  have initialWork : initial.work = work prepared := by
    rw [← project_work prepared i32]
    unfold NState.work
    rw [compactData.1,compactData.2.2.1]
  have scalarBound : out.scalars.peak ≤ max (max caller.scalars.peak (uniteScalarBudget initial P.length initial.scalars.baseMemory))
      (caller.scalars.memory.length-caller.scalars.baseMemory+caller.scalars.bindings.length) := by
    rw [scalarEq]
    exact max_le_max (max_le_max (Nat.le_refl _) scalarPeak) (Nat.le_refl _)
  have heapBound : out.objects.heap.peak ≤ storageBudget initial vc.L0 := by
    rw [heapEq]
    apply Nat.max_le.mpr
    refine ⟨heapPeak,?_⟩
    rw [live,baseEq]
    exact Nat.le_trans (Nat.sub_le_sub_right (Nat.le_succ _) _) (Nat.le_max_right _ _)
  refine ⟨fuel,out,r1,r2,middle,two,final,actual,c1,c2,finalEq,newValid,connected,?_,memoryEq.trans savedCaller,scalarBound,heapBound,?_,buffer,?_,items⟩
  · rw [workEq]
    rw [initialWork] at cost
    omega
  · rw [peakEq]
    exact max_le_max (max_le_max (Nat.le_refl _) outerPeak) (Nat.add_le_add scalarBound heapBound)
  · rw [lookups]
    exact found

end Proofs.UfCompactUniteCall
