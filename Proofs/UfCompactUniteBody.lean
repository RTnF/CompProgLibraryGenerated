import Proofs.UfCompactRootBody
import Proofs.UfFieldsUnite

namespace Proofs.UfCompactUniteBody
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedHoare Proofs.CppVector
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.StraightLine
open Proofs.VecExpr Proofs.VecWrite Proofs.QuotientFrame Proofs.VecStraight
open Proofs.UfRootCall Proofs.UfCompression Proofs.DoublingNested Proofs.UfCompactRootBody
open Proofs.CppState (Cell)

def uniteScalarBudget (s : NState) (prefixLength base : Nat) : Nat :=
  max (max s.scalars.peak s.peak) (prefixLength+100-base)

theorem unite_body (s : NState) (vc : VCtx) (vec : List Int) (rank : Nat → Nat)
    (groups : Int) (valid : Proofs.UfClassInvariant.Valid vec groups rank)
    (a b : Nat) (ha : a < vec.length) (hb : b < vec.length) (P : List Cell) (counter : Nat)
    (countFound : P[counter]? = some ⟨i32,groups⟩)
    (buf : Buffer Value) (ty : vc.ty = i32)
    (permission : vc.wV = true ∧ vc.flag = true)
    (qs : QS s [] s.scalars.baseMemory s.scope
      (Proofs.UfFieldsSame.fields P ⟨counter,true⟩ vec.length a b).mem
      (Proofs.UfFieldsSame.fields P ⟨counter,true⟩ vec.length a b).bs
      (sl1 (Proofs.UfFieldsSame.fields P ⟨counter,true⟩ vec.length a b).bs.length))
    (frame : FW vc vec buf 0 s.frame)
    (baseline : s.scalars.baseMemory ≤ P.length) (scope : vc.sc ≤ s.scope) :
    ∃ (fuel : Nat) (step : NStep) (r1 r2 : Nat) (middle two final : List Int),
      Proofs.CppNestedProgram.runFuel fuel Proofs.UnionFindCandidateInstance.UnionFind_unite.body s = .finished step ∧
      step.returned = some (.scalar (Proofs.UfUniteCall.uniteX two r1 r2 : Int)) ∧ step.breaking = false ∧
      Compressed vec middle a r1 ∧ Compressed middle two b r2 ∧
      final = Proofs.UfUniteCall.uniteVec two r1 r2 ∧
      (∃ rank', Proofs.UfClassInvariant.Valid final (Proofs.UfFieldsUnite.countAfter groups r1 r2) rank') ∧
      i32.valid (Proofs.UfUniteCall.uniteX two r1 r2 : Int) = true ∧
      (r1=r2 ↔ Proofs.UfFieldsSame.Connected vec a b) ∧
      step.state.scalars.memory.take P.length = Proofs.UfFieldsUnite.updatedMemory P counter groups r1 r2 ∧
      step.state.work ≤ s.work+91*rank a+91*rank b+342 ∧
      step.state.scalars.peak ≤ uniteScalarBudget s P.length s.scalars.baseMemory ∧
      step.state.frame.state.storage.peak ≤ storageBudget s vc.L0 ∧
      step.state.peak ≤ uniteScalarBudget s P.length s.scalars.baseMemory+storageBudget s vc.L0 ∧
      step.state.frame.state.liveSpace = vc.L0 ∧
      step.state.frame.state.storage.baseSpace = s.frame.state.storage.baseSpace ∧
      ∃ buffer, step.state.frame.state.storage.lookup vc.R = some buffer ∧ buffer.items = final.map Value.integer := by
  obtain ⟨res,r1,r2,middle,two,executed,returned,c1,c2,finalEq,newValid,saved,cost,need,writes⟩ :=
    Proofs.UfFieldsUnite.body_correct P counter groups vec rank valid countFound a b ha hb (max (rank a) (rank b)+2) (by omega) (by omega)
  have run : pexecW vc.ty (max (rank a) (rank b)+2) Proofs.UnionFindCandidateInstance.UnionFind_unite.body
      (Proofs.UfFieldsSame.fields P ⟨counter,true⟩ vec.length a b) vec = some res := by rw [ty]; exact executed
  let SPB := uniteScalarBudget s P.length s.scalars.baseMemory
  let TPB := max s.frame.state.storage.peak (vc.L0+1)
  have scalarBound : s.scalars.peak ≤ SPB := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have outerBound : s.peak ≤ SPB := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have resident : P.length+100 ≤ SPB+s.scalars.baseMemory := by
    have bound : P.length+100-s.scalars.baseMemory ≤ SPB := Nat.le_max_right _ _
    omega
  have cq : Cq SPB TPB s.scalars.work s :=
    ⟨Nat.le_refl _,scalarBound,Nat.le_max_left _ _,by change s.peak ≤ SPB+TPB; omega⟩
  have actual := soundW vc true (fun _ => permission) Proofs.UnionFindCandidateInstance.UnionFind_unite.body (by decide)
    (max (rank a) (rank b)+2) (Proofs.UfFieldsSame.fields P ⟨counter,true⟩ vec.length a b) vec res run s qs frame cq
    (by simp [Proofs.UfFieldsSame.fields]; omega)
    (by simp [Proofs.UfFieldsSame.fields]; omega)
    (by omega) scope (Nat.le_max_right _ _)
  obtain ⟨fuel,step,ran,ret,breaking,qsD,⟨buffer,frameD⟩,cqD⟩ := actual
  have contexts : ∀ owner sc, s.frame.state.forest.context owner = some sc → sc ≤ s.scope := by
    intro owner sc found
    have smaller := frame.strict owner sc found
    omega
  have storage := Proofs.CppStoragePeak.run_peak fuel Proofs.UnionFindCandidateInstance.UnionFind_unite.body s step
    (by decide) contexts ran
  have heapBound : step.state.frame.state.storage.peak ≤ storageBudget s vc.L0 := by
    simpa only [Proofs.CppStoragePeak.bound,storageBudget,frame.live] using storage.peak
  have growth := Proofs.CppPeakRun.run_grows fuel Proofs.UnionFindCandidateInstance.UnionFind_unite.body s step
    (by decide) contexts ran
  have outerBound := growth.growth.bound SPB (storageBudget s vc.L0) cqD.scalarPeak heapBound
  have outerSharp : step.state.peak ≤ SPB+storageBudget s vc.L0 := by
    apply Nat.le_trans outerBound
    apply Nat.max_le.mpr
    exact ⟨by omega,Nat.le_refl _⟩
  have length := valid.length
  have r1inside : r1 < two.length := by
    obtain ⟨w,found,_⟩ := c1.root
    have inside := (List.getElem?_eq_some_iff.mp found).1
    rw [c2.length,c1.length]
    exact inside
  have r2inside : r2 < two.length := by
    obtain ⟨w,found,_⟩ := c2.root
    have inside := (List.getElem?_eq_some_iff.mp found).1
    rw [c2.length]
    exact inside
  have rootInside := Proofs.UfUniteCall.uniteX_lt two r1 r2 r1inside r2inside
  have resultValid : i32.valid (Proofs.UfUniteCall.uniteX two r1 r2 : Int) = true :=
    Proofs.VectorSumCall.i32_valid _ (by omega) (by rw [c2.length,c1.length] at rootInside; omega)
  obtain ⟨w2,root2,neg2⟩ := c2.root
  have oldRoot2 : vec[r2]? = some w2 := (negative_entry c1 w2 neg2).mp root2
  refine ⟨fuel,step,r1,r2,middle,two,res.vec,ran,?_,breaking,c1,c2,finalEq,newValid,resultValid,?_,?_,?_,cqD.scalarPeak,heapBound,
    outerSharp,frameD.live,storage.base.headers.base,buffer,frameD.vfound,frameD.items⟩
  · rw [returned] at ret
    exact ret
  · exact Proofs.UfFieldsSame.roots_connected vec a b r1 r2 c1.reach (reach_backward c1 c2.reach) c1.root ⟨w2,oldRoot2,neg2⟩
  · rw [qsD.memory]
    exact saved
  · have scalarWork := cqD.work
    have heapWork := frameD.work
    have initialWork := frame.work
    unfold NState.work
    omega

end Proofs.UfCompactUniteBody
