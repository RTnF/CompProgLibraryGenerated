import Proofs.UfReadPrograms
import Proofs.CppStoragePeak
import Proofs.CppPeakRun

namespace Proofs.UfReadBody
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppVector Proofs.CppNestedVectorStore
open Proofs.CppNestedVectorBindings Proofs.StraightLine Proofs.VecExpr Proofs.VecWrite
open Proofs.QuotientFrame Proofs.VecStraight Proofs.DoublingNested
open Proofs.CppState (Cell)

def scalarBudget (s : NState) (prefixLength : Nat) : Nat :=
  max s.scalars.peak (prefixLength+48-s.scalars.baseMemory)
def heapBudget (s : NState) (live : Nat) : Nat :=
  max s.frame.state.storage.peak (live+1-s.frame.state.storage.baseSpace)

theorem execute (s : NState) (vc : VCtx) (command : Command) (ps : PS) (vec : List Int)
    (fuel : Nat) (res : PRW) (prefixLength : Nat) (buf : Buffer Value)
    (ty : vc.ty = i32) (readOnly : WrV false command = true)
    (allowed : Proofs.CppNoResizeScope.Allowed command = true)
    (run : pexecW i32 fuel command ps vec = some res)
    (unchanged : res.vec = vec) (noWrites : res.wk = 0)
    (qs : QS s [] s.scalars.baseMemory s.scope ps.mem ps.bs (sl1 ps.bs.length))
    (frame : FW vc vec buf 0 s.frame)
    (baseline : s.scalars.baseMemory ≤ ps.mem.length)
    (resident : ps.mem.length+ps.bs.length ≤ prefixLength+48)
    (need : res.need ≤ prefixLength+48) (scope : vc.sc ≤ s.scope) :
    ∃ (fuel : Nat) (step : NStep), runFuel fuel command s = .finished step ∧
      step.returned = res.ret.map Ret.scalar ∧ step.breaking = false ∧
      step.state.scalars.memory = res.ps.mem ∧ step.state.work ≤ s.work+res.cost ∧
      step.state.scalars.peak ≤ scalarBudget s prefixLength ∧
      step.state.frame.state.storage.peak ≤ heapBudget s vc.L0 ∧
      step.state.peak ≤ max s.peak (scalarBudget s prefixLength+heapBudget s vc.L0) ∧
      step.state.frame.state.liveSpace = vc.L0 ∧
      step.state.frame.state.storage.baseSpace = s.frame.state.storage.baseSpace ∧
      ∃ buffer, step.state.frame.state.storage.lookup vc.R = some buffer ∧ buffer.items = vec.map Value.integer := by
  let SPB := scalarBudget s prefixLength
  let TPB := max (max s.frame.state.storage.peak (vc.L0+1)) s.peak
  have scalarBound : s.scalars.peak ≤ SPB := Nat.le_max_left _ _
  have outerBound : s.peak ≤ TPB := Nat.le_max_right _ _
  have bound : prefixLength+48-s.scalars.baseMemory ≤ SPB := Nat.le_max_right _ _
  have cq : Cq SPB TPB s.scalars.work s :=
    ⟨Nat.le_refl _,scalarBound,Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _),by change s.peak ≤ SPB+TPB; omega⟩
  have flatRun : pexecW vc.ty fuel command ps vec = some res := by rw [ty]; exact run
  have actual := soundW vc false (by intro impossible; contradiction) command readOnly fuel ps vec res flatRun s qs frame cq
    baseline (by omega) (by omega) scope (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
  obtain ⟨fuel,step,ran,returned,breaking,qsD,⟨buffer,frameD⟩,cqD⟩ := actual
  have contexts : ∀ owner sc, s.frame.state.forest.context owner = some sc → sc ≤ s.scope := by
    intro owner sc found
    have smaller := frame.strict owner sc found
    omega
  have storage := Proofs.CppStoragePeak.run_peak fuel command s step allowed contexts ran
  have heapBound : step.state.frame.state.storage.peak ≤ heapBudget s vc.L0 := by
    simpa only [Proofs.CppStoragePeak.bound,heapBudget,frame.live] using storage.peak
  have growth := Proofs.CppPeakRun.run_grows fuel command s step allowed contexts ran
  have outer := growth.growth.bound SPB (heapBudget s vc.L0) cqD.scalarPeak heapBound
  have outerSharp : step.state.peak ≤ max s.peak (SPB+heapBudget s vc.L0) := outer
  refine ⟨fuel,step,ran,returned,breaking,qsD.memory,?_,cqD.scalarPeak,heapBound,outerSharp,
    frameD.live,storage.base.headers.base,buffer,frameD.vfound,?_⟩
  · have scalarWork := cqD.work
    have heapWork := frameD.work
    have initialWork := frame.work
    rw [noWrites] at heapWork
    unfold NState.work
    omega
  · rw [unchanged] at frameD
    exact frameD.items

end Proofs.UfReadBody
