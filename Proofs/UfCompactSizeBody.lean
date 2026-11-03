import Proofs.UfFieldsSize
import Proofs.UfCompactRootBody
import Proofs.CppStoragePeak
import Proofs.CppPeakRun

namespace Proofs.UfCompactSizeBody
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedHoare Proofs.CppVector
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.StraightLine
open Proofs.VecExpr Proofs.VecWrite Proofs.QuotientFrame Proofs.VecStraight
open Proofs.UfRootCall Proofs.UfCompression Proofs.DoublingNested
open Proofs.CppState (Cell)

open Proofs.UfCompactRootBody

theorem size_body (s : NState) (vc : VCtx) (vec : List Int) (rank : Nat → Nat)
    (forest : Forest vec rank) (length : vec.length < 2147483648)
    (weights : Proofs.UfFieldsSize.Weights vec) (a : Nat) (inside : a < vec.length) (P : List Cell) (counter : Proofs.CppState.Binding)
    (buf : Buffer Value) (ty : vc.ty = i32)
    (permission : vc.wV = true ∧ vc.flag = true)
    (qs : QS s [] s.scalars.baseMemory s.scope
      (Proofs.UfFieldsRoot.fields P counter vec.length a).mem
      (Proofs.UfFieldsRoot.fields P counter vec.length a).bs
      (sl1 (Proofs.UfFieldsRoot.fields P counter vec.length a).bs.length))
    (frame : FW vc vec buf 0 s.frame)
    (baseline : s.scalars.baseMemory ≤ P.length) (scope : vc.sc ≤ s.scope) :
    ∃ (fuel : Nat) (step : NStep) (root : Nat) (weight : Int) (final : List Int),
      Proofs.CppNestedProgram.runFuel fuel Proofs.UnionFindCandidateInstance.UnionFind_size.body s = .finished step ∧
      step.returned = some (.scalar (-weight)) ∧ step.breaking = false ∧
      vec[root]? = some weight ∧ weight < 0 ∧ i32.valid (-weight) = true ∧
      Compressed vec final a root ∧ Forest final rank ∧ Proofs.UfFieldsSize.Weights final ∧
      step.state.scalars.memory.take P.length = P ∧
      step.state.work ≤ s.work+91*rank a+100 ∧
      step.state.scalars.peak ≤ scalarBudget s P.length s.scalars.baseMemory ∧
      step.state.frame.state.storage.peak ≤ storageBudget s vc.L0 ∧
      step.state.peak ≤ scalarBudget s P.length s.scalars.baseMemory+storageBudget s vc.L0 ∧
      step.state.frame.state.liveSpace = vc.L0 ∧
      step.state.frame.state.storage.baseSpace = s.frame.state.storage.baseSpace ∧
      ∃ buffer, step.state.frame.state.storage.lookup vc.R = some buffer ∧ buffer.items = final.map Value.integer := by
  obtain ⟨res,root,weight,executed,returned,atRoot,negative,valueValid,compressed,newForest,newWeights,saved,cost,need,writes⟩ :=
    Proofs.UfFieldsSize.body_correct P counter vec rank forest length weights a inside (rank a+2) (by omega)
  have run : pexecW vc.ty (rank a+2) Proofs.UnionFindCandidateInstance.UnionFind_size.body
      (Proofs.UfFieldsRoot.fields P counter vec.length a) vec = some res := by rw [ty]; exact executed
  let SPB := scalarBudget s P.length s.scalars.baseMemory
  let TPB := max s.frame.state.storage.peak (vc.L0+1)
  have scalarBound : s.scalars.peak ≤ SPB := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have outerBound : s.peak ≤ SPB := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have resident : P.length+80 ≤ SPB+s.scalars.baseMemory := by
    have bound : P.length+80-s.scalars.baseMemory ≤ SPB := Nat.le_max_right _ _
    omega
  have cq : Cq SPB TPB s.scalars.work s :=
    ⟨Nat.le_refl _,scalarBound,Nat.le_max_left _ _,by change s.peak ≤ SPB+TPB; omega⟩
  have actual := soundW vc true (fun _ => permission) Proofs.UnionFindCandidateInstance.UnionFind_size.body (by decide)
    (rank a+2) (Proofs.UfFieldsRoot.fields P counter vec.length a) vec res run s qs frame cq
    (by simp [Proofs.UfFieldsRoot.fields,Proofs.VecShift.pad,Proofs.PrefixSumsCall.stI]; omega)
    (by simp [Proofs.UfFieldsRoot.fields,Proofs.VecShift.pad,Proofs.PrefixSumsCall.stI]; omega)
    (by omega) scope (Nat.le_max_right _ _)
  obtain ⟨fuel,step,ran,ret,breaking,qsD,⟨buffer,frameD⟩,cqD⟩ := actual
  have contexts : ∀ owner sc, s.frame.state.forest.context owner = some sc → sc ≤ s.scope := by
    intro owner sc found
    have smaller := frame.strict owner sc found
    omega
  have storage := Proofs.CppStoragePeak.run_peak fuel Proofs.UnionFindCandidateInstance.UnionFind_size.body s step
    (by decide) contexts ran
  have heapBound : step.state.frame.state.storage.peak ≤ storageBudget s vc.L0 := by
    simpa only [Proofs.CppStoragePeak.bound,storageBudget,frame.live] using storage.peak
  have growth := Proofs.CppPeakRun.run_grows fuel Proofs.UnionFindCandidateInstance.UnionFind_size.body s step
    (by decide) contexts ran
  have outerBound := growth.growth.bound SPB (storageBudget s vc.L0) cqD.scalarPeak heapBound
  have outerSharp : step.state.peak ≤ SPB+storageBudget s vc.L0 := by
    apply Nat.le_trans outerBound
    apply Nat.max_le.mpr
    exact ⟨by omega,Nat.le_refl _⟩
  refine ⟨fuel,step,root,weight,res.vec,ran,?_,breaking,atRoot,negative,valueValid,compressed,newForest,newWeights,?_,?_,cqD.scalarPeak,heapBound,outerSharp,frameD.live,storage.base.headers.base,
    buffer,frameD.vfound,frameD.items⟩
  · rw [returned] at ret
    exact ret
  · rw [qsD.memory]
    exact saved
  · have scalarWork := cqD.work
    have heapWork := frameD.work
    have initialWork := frame.work
    unfold NState.work
    omega

end Proofs.UfCompactSizeBody
