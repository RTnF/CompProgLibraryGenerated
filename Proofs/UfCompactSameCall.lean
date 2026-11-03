import Proofs.CppMoveCallBindings
import Proofs.UfCompactSameBody
namespace Proofs.UfCompactSameCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppMoveContext Proofs.CppMoveHeaders Proofs.CppMovePreparedCall
open Proofs.CppMoveCallBindings Proofs.UfCompactRootBody
open Proofs.CppVector Proofs.CppNestedVectorStore Proofs.StraightLine
open Proofs.VecExpr Proofs.VecWrite Proofs.QuotientFrame
open Proofs.UfRootCall Proofs.UfCompression Proofs.DoublingNested
open Proofs.UfCompactSameBody
open Proofs.CppState (Cell)

theorem same_call (caller prepared : Context) (initial : NState) (arguments : List Proofs.CppNestedCall.NArgument)
    (vc : VCtx) (vec : List Int) (rank : Nat → Nat) (forest : Forest vec rank)
    (length : vec.length < 2147483648) (a b : Nat) (ha : a < vec.length) (hb : b < vec.length)
    (P : List Cell) (counter : Proofs.CppState.Binding) (buf : Buffer Value) (ty : vc.ty = i32)
    (permission : vc.wV = true ∧ vc.flag = true)
    (preparedRun : prepareArguments caller i32 Proofs.UnionFindCandidateInstance.UnionFind_same.parameters arguments = some prepared)
    (compacted : compact (project prepared i32) = some initial)
    (qs : QS initial [] initial.scalars.baseMemory initial.scope
      (Proofs.UfFieldsSame.fields P counter vec.length a b).mem
      (Proofs.UfFieldsSame.fields P counter vec.length a b).bs
      (sl1 (Proofs.UfFieldsSame.fields P counter vec.length a b).bs.length))
    (frame : FW vc vec buf 0 initial.frame)
    (baseline : initial.scalars.baseMemory ≤ P.length) (scope : vc.sc ≤ initial.scope)
    (prefixLength : caller.scalars.memory.length ≤ P.length)
    (prefixMemory : P.take caller.scalars.memory.length = caller.scalars.memory)
    (contexts : ∀ owner sc, (project caller i32).frame.state.forest.context owner = some sc → sc ≤ caller.scope)
    (covered : OwnsAll caller.objects.heap) :
    ∃ (fuel : Nat) (out : Context) (r1 r2 : Nat) (middle final : List Int),
      callFuel Proofs.UnionFindCandidateInstance.UnionFind_same fuel caller i32 arguments = .finished (out,.scalar (if r1=r2 then 1 else 0)) ∧
      Compressed vec middle a r1 ∧ Compressed middle final b r2 ∧ Forest final rank ∧
      (r1=r2 ↔ Proofs.UfFieldsSame.Connected vec a b) ∧
      work out ≤ work prepared+91*rank a+91*rank b+181 ∧
      out.scalars.memory = caller.scalars.memory ∧
      out.scalars.peak ≤ max (max caller.scalars.peak (scalarBudget initial P.length initial.scalars.baseMemory))
        (caller.scalars.memory.length-caller.scalars.baseMemory+caller.scalars.bindings.length) ∧
      out.objects.heap.peak ≤ storageBudget initial vc.L0 ∧
      out.peak ≤ max (max caller.peak (scalarBudget initial P.length initial.scalars.baseMemory+storageBudget initial vc.L0))
        (max (max caller.scalars.peak (scalarBudget initial P.length initial.scalars.baseMemory))
          (caller.scalars.memory.length-caller.scalars.baseMemory+caller.scalars.bindings.length)+storageBudget initial vc.L0) ∧
      ∃ buffer, (project out i32).frame.state.storage.lookup vc.R = some buffer ∧ buffer.items = final.map Value.integer := by
  obtain ⟨fuel,step,r1,r2,middle,final,ran,returned,breaking,c1,c2,newForest,connected,saved,cost,scalarPeak,heapPeak,outerPeak,live,baseEq,buffer,found,items⟩ :=
    same_body initial vc vec rank forest length a b ha hb P counter buf ty permission qs frame baseline scope
  have stepEq : step = ⟨step.state,some (.scalar (if r1=r2 then 1 else 0)),false⟩ := by
    cases step with
    | mk state ret brk => simp_all
  have run : Proofs.CppNestedProgram.runFuel fuel Proofs.UnionFindCandidateInstance.UnionFind_same.body initial =
      .finished ⟨step.state,some (.scalar (if r1=r2 then 1 else 0)),false⟩ := by rw [← stepEq]; exact ran
  have savedCaller : step.state.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory := by
    calc _ = (step.state.scalars.memory.take P.length).take caller.scalars.memory.length := by
           rw [List.take_take,Nat.min_eq_left prefixLength]
         _ = caller.scalars.memory := by rw [saved,prefixMemory]
  have fits : caller.scalars.memory.length ≤ step.state.scalars.memory.length := by
    have sizes := congrArg List.length savedCaller
    simp only [List.length_take] at sizes
    omega
  have valueValid : Proofs.PrefixSumsCall.bT.valid (if r1=r2 then 1 else 0) = true := by
    by_cases eq : r1=r2 <;> simp [eq,Ty.valid]
  have compactData := compact_metadata (project prepared i32) initial compacted
  have prep := prepareArguments_effects caller prepared i32 Proofs.UnionFindCandidateInstance.UnionFind_same.parameters arguments preparedRun
  have state : initial.frame.state = (project caller i32).frame.state := by
    rw [compactData.1]
    simp only [project,Proofs.CppMoveFrame.materialize,prep.1]
  have valid : (project caller i32).frame.state.wellFormed = true := by rw [← state]; exact frame.valid
  obtain ⟨out,actual,workEq,memoryEq,lookups,scalarEq,heapEq,peakEq⟩ := call_of_body
    Proofs.UnionFindCandidateInstance.UnionFind_same fuel caller prepared initial i32 Proofs.PrefixSumsCall.bT arguments step.state (if r1=r2 then 1 else 0)
    rfl (by decide) contexts covered valid preparedRun compacted run fits (by rw [savedCaller]) valueValid
  have initialWork : initial.work = work prepared := by
    rw [← project_work prepared i32]
    unfold NState.work
    rw [compactData.1,compactData.2.2.1]
  have scalarBound : out.scalars.peak ≤ max (max caller.scalars.peak (scalarBudget initial P.length initial.scalars.baseMemory))
      (caller.scalars.memory.length-caller.scalars.baseMemory+caller.scalars.bindings.length) := by
    rw [scalarEq]
    exact max_le_max (max_le_max (Nat.le_refl _) scalarPeak) (Nat.le_refl _)
  have heapBound : out.objects.heap.peak ≤ storageBudget initial vc.L0 := by
    rw [heapEq]
    apply Nat.max_le.mpr
    refine ⟨heapPeak,?_⟩
    rw [live,baseEq]
    exact Nat.le_trans (Nat.sub_le_sub_right (Nat.le_succ _) _) (Nat.le_max_right _ _)
  refine ⟨fuel,out,r1,r2,middle,final,actual,c1,c2,newForest,connected,?_,memoryEq.trans savedCaller,scalarBound,heapBound,?_,buffer,?_,items⟩
  · rw [workEq]
    rw [initialWork] at cost
    omega
  · rw [peakEq]
    exact max_le_max (max_le_max (Nat.le_refl _) outerPeak) (Nat.add_le_add scalarBound heapBound)
  · rw [lookups]
    exact found

end Proofs.UfCompactSameCall
