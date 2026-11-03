import Proofs.UfCompactCounterBody
import Proofs.CppMoveCallBindings
import Proofs.UfFieldsCounter
namespace Proofs.UfCompactCounterCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppMoveContext Proofs.CppMoveHeaders Proofs.CppMovePreparedCall
open Proofs.CppMoveCallBindings Proofs.UfCompactRootBody
open Proofs.CppVector Proofs.CppNestedVectorStore Proofs.StraightLine
open Proofs.VecExpr Proofs.VecWrite Proofs.QuotientFrame
open Proofs.UfRootCall Proofs.UfCompression Proofs.DoublingNested
open Proofs.UfCompactCounterBody
open Proofs.CppState (Cell)

theorem counter_call (caller prepared : Context) (initial : NState) (arguments : List Proofs.CppNestedCall.NArgument)
    (vc : VCtx) (vec : List Int) (P : List Cell) (counter : Nat) (n groups : Int)
    (countFound : P[counter]? = some ⟨i32,groups⟩) (valueValid : i32.valid groups = true)
    (buf : Buffer Value) (ty : vc.ty = i32)
    (preparedRun : prepareArguments caller i32 Proofs.UnionFindCandidateInstance.UnionFind_num_groups.parameters arguments = some prepared)
    (compacted : compact (project prepared i32) = some initial)
    (qs : QS initial [] initial.scalars.baseMemory initial.scope
      (Proofs.UfFieldsCounter.fields P counter n).mem
      (Proofs.UfFieldsCounter.fields P counter n).bs
      (sl1 (Proofs.UfFieldsCounter.fields P counter n).bs.length))
    (frame : FW vc vec buf 0 initial.frame)
    (baseline : initial.scalars.baseMemory ≤ P.length) (scope : vc.sc ≤ initial.scope)
    (prefixLength : caller.scalars.memory.length ≤ P.length)
    (prefixMemory : P.take caller.scalars.memory.length = caller.scalars.memory)
    (contexts : ∀ owner sc, (project caller i32).frame.state.forest.context owner = some sc → sc ≤ caller.scope)
    (covered : OwnsAll caller.objects.heap) :
    ∃ (fuel : Nat) (out : Context),
      callFuel Proofs.UnionFindCandidateInstance.UnionFind_num_groups fuel caller i32 arguments = .finished (out,.scalar groups) ∧
      work out ≤ work prepared+3 ∧
      out.scalars.memory = caller.scalars.memory ∧
      out.scalars.peak ≤ max (max caller.scalars.peak (counterScalarBudget initial P.length initial.scalars.baseMemory))
        (caller.scalars.memory.length-caller.scalars.baseMemory+caller.scalars.bindings.length) ∧
      out.objects.heap.peak ≤ storageBudget initial vc.L0 ∧
      out.peak ≤ max (max caller.peak (counterScalarBudget initial P.length initial.scalars.baseMemory+storageBudget initial vc.L0))
        (max (max caller.scalars.peak (counterScalarBudget initial P.length initial.scalars.baseMemory))
          (caller.scalars.memory.length-caller.scalars.baseMemory+caller.scalars.bindings.length)+storageBudget initial vc.L0) ∧
      ∃ buffer, (project out i32).frame.state.storage.lookup vc.R = some buffer ∧ buffer.items = vec.map Value.integer := by
  obtain ⟨fuel,step,ran,returned,breaking,memory,cost,scalarPeak,heapPeak,outerPeak,live,baseEq,buffer,found,items⟩ :=
    counter_body initial vc vec P counter n groups countFound valueValid buf ty qs frame baseline scope
  have stepEq : step = ⟨step.state,some (.scalar groups),false⟩ := by
    cases step with
    | mk state ret brk => simp_all
  have run : Proofs.CppNestedProgram.runFuel fuel Proofs.UnionFindCandidateInstance.UnionFind_num_groups.body initial =
      .finished ⟨step.state,some (.scalar groups),false⟩ := by rw [← stepEq]; exact ran
  have initialSaved : initial.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [qs.memory]
    change (P++[(⟨i32,n⟩ : Cell)]).take caller.scalars.memory.length = caller.scalars.memory
    simp only [List.take_append,Nat.sub_eq_zero_of_le prefixLength,List.take_zero,List.append_nil,prefixMemory]
  have savedCaller : step.state.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [memory,initialSaved]
  have fits : caller.scalars.memory.length ≤ step.state.scalars.memory.length := by
    have sizes := congrArg List.length savedCaller
    simp only [List.length_take] at sizes
    omega
  have compactData := compact_metadata (project prepared i32) initial compacted
  have prep := prepareArguments_effects caller prepared i32 Proofs.UnionFindCandidateInstance.UnionFind_num_groups.parameters arguments preparedRun
  have state : initial.frame.state = (project caller i32).frame.state := by
    rw [compactData.1]
    simp only [project,Proofs.CppMoveFrame.materialize,prep.1]
  have valid : (project caller i32).frame.state.wellFormed = true := by rw [← state]; exact frame.valid
  obtain ⟨out,actual,workEq,memoryEq,lookups,scalarEq,heapEq,peakEq⟩ := call_of_body
    Proofs.UnionFindCandidateInstance.UnionFind_num_groups fuel caller prepared initial i32 i32 arguments step.state groups
    rfl (by decide) contexts covered valid preparedRun compacted run fits (by rw [savedCaller]) valueValid
  have initialWork : initial.work = work prepared := by
    rw [← project_work prepared i32]
    unfold NState.work
    rw [compactData.1,compactData.2.2.1]
  have scalarBound : out.scalars.peak ≤ max (max caller.scalars.peak (counterScalarBudget initial P.length initial.scalars.baseMemory))
      (caller.scalars.memory.length-caller.scalars.baseMemory+caller.scalars.bindings.length) := by
    rw [scalarEq]
    exact max_le_max (max_le_max (Nat.le_refl _) scalarPeak) (Nat.le_refl _)
  have heapBound : out.objects.heap.peak ≤ storageBudget initial vc.L0 := by
    rw [heapEq]
    apply Nat.max_le.mpr
    refine ⟨heapPeak,?_⟩
    rw [live,baseEq]
    exact Nat.le_trans (Nat.sub_le_sub_right (Nat.le_succ _) _) (Nat.le_max_right _ _)
  refine ⟨fuel,out,actual,?_,memoryEq.trans savedCaller,scalarBound,heapBound,?_,buffer,?_,items⟩
  · rw [workEq]
    rw [initialWork] at cost
    omega
  · rw [peakEq]
    exact max_le_max (max_le_max (Nat.le_refl _) outerPeak) (Nat.add_le_add scalarBound heapBound)
  · rw [lookups]
    exact found

end Proofs.UfCompactCounterCall
