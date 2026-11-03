import Proofs.UfCompactRootBody
import Proofs.UfFieldsCounter

namespace Proofs.UfCompactCounterBody
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppVector Proofs.CppNestedVectorStore
open Proofs.CppNestedVectorBindings Proofs.StraightLine Proofs.VecExpr Proofs.VecWrite
open Proofs.QuotientFrame Proofs.DoublingNested Proofs.UfCompactRootBody
open Proofs.CppState (Cell)

def counterScalarBudget (s : NState) (prefixLength base : Nat) : Nat :=
  max (max s.scalars.peak s.peak) (prefixLength+6-base)

theorem counter_body (s : NState) (vc : VCtx) (vec : List Int) (P : List Cell)
    (counter : Nat) (n groups : Int) (countFound : P[counter]? = some ⟨i32,groups⟩)
    (valueValid : i32.valid groups = true) (buf : Buffer Value) (ty : vc.ty = i32)
    (qs : QS s [] s.scalars.baseMemory s.scope (Proofs.UfFieldsCounter.fields P counter n).mem
      (Proofs.UfFieldsCounter.fields P counter n).bs (sl1 (Proofs.UfFieldsCounter.fields P counter n).bs.length))
    (frame : FW vc vec buf 0 s.frame) (baseline : s.scalars.baseMemory ≤ P.length) (scope : vc.sc ≤ s.scope) :
    ∃ fuel step, Proofs.CppNestedProgram.runFuel fuel Proofs.UnionFindCandidateInstance.UnionFind_num_groups.body s = .finished step ∧
      step.returned = some (.scalar groups) ∧ step.breaking = false ∧
      step.state.scalars.memory = s.scalars.memory ∧ step.state.work ≤ s.work+2 ∧
      step.state.scalars.peak ≤ counterScalarBudget s P.length s.scalars.baseMemory ∧
      step.state.frame.state.storage.peak ≤ storageBudget s vc.L0 ∧
      step.state.peak ≤ counterScalarBudget s P.length s.scalars.baseMemory+storageBudget s vc.L0 ∧
      step.state.frame.state.liveSpace = vc.L0 ∧
      step.state.frame.state.storage.baseSpace = s.frame.state.storage.baseSpace ∧
      ∃ buffer, step.state.frame.state.storage.lookup vc.R = some buffer ∧ buffer.items = vec.map Value.integer := by
  let res : PRW := ⟨Proofs.UfFieldsCounter.fields P counter n,vec,some groups,2,P.length+6,0⟩
  have run : pexecW vc.ty 0 Proofs.UnionFindCandidateInstance.UnionFind_num_groups.body
      (Proofs.UfFieldsCounter.fields P counter n) vec = some res := by
    rw [ty]
    exact Proofs.UfFieldsCounter.body_correct P counter n groups vec countFound valueValid 0
  let SPB := counterScalarBudget s P.length s.scalars.baseMemory
  let TPB := max s.frame.state.storage.peak (vc.L0+1)
  have scalarBound : s.scalars.peak ≤ SPB := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have outerBound : s.peak ≤ SPB := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have resident : P.length+6 ≤ SPB+s.scalars.baseMemory := by
    have bound : P.length+6-s.scalars.baseMemory ≤ SPB := Nat.le_max_right _ _
    omega
  have cq : Cq SPB TPB s.scalars.work s :=
    ⟨Nat.le_refl _,scalarBound,Nat.le_max_left _ _,by change s.peak ≤ SPB+TPB; omega⟩
  have actual := soundW vc false (by intro impossible; contradiction)
    Proofs.UnionFindCandidateInstance.UnionFind_num_groups.body (by decide) 0
    (Proofs.UfFieldsCounter.fields P counter n) vec res run s qs frame cq
    (by simp [Proofs.UfFieldsCounter.fields]; omega)
    (by simp [Proofs.UfFieldsCounter.fields]; omega)
    (by exact resident) scope (Nat.le_max_right _ _)
  obtain ⟨fuel,step,ran,ret,breaking,qsD,⟨buffer,frameD⟩,cqD⟩ := actual
  have contexts : ∀ owner sc, s.frame.state.forest.context owner = some sc → sc ≤ s.scope := by
    intro owner sc found
    have smaller := frame.strict owner sc found
    omega
  have storage := Proofs.CppStoragePeak.run_peak fuel Proofs.UnionFindCandidateInstance.UnionFind_num_groups.body s step
    (by decide) contexts ran
  have heapBound : step.state.frame.state.storage.peak ≤ storageBudget s vc.L0 := by
    simpa only [Proofs.CppStoragePeak.bound,storageBudget,frame.live] using storage.peak
  have growth := Proofs.CppPeakRun.run_grows fuel Proofs.UnionFindCandidateInstance.UnionFind_num_groups.body s step
    (by decide) contexts ran
  have outerBound := growth.growth.bound SPB (storageBudget s vc.L0) cqD.scalarPeak heapBound
  have outerSharp : step.state.peak ≤ SPB+storageBudget s vc.L0 :=
    Nat.le_trans outerBound (Nat.max_le.mpr ⟨by omega,Nat.le_refl _⟩)
  refine ⟨fuel,step,ran,ret,breaking,?_,?_,cqD.scalarPeak,heapBound,outerSharp,frameD.live,
    storage.base.headers.base,buffer,frameD.vfound,frameD.items⟩
  · exact qsD.memory.trans qs.memory.symm
  · have scalarWork := cqD.work
    have heapWork := frameD.work
    have initialWork := frame.work
    change step.state.scalars.work ≤ s.scalars.work+2 at scalarWork
    change step.state.frame.state.storage.work = vc.T0+0 at heapWork
    unfold NState.work
    omega

end Proofs.UfCompactCounterBody
