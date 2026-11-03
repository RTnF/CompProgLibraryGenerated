import Proofs.QuotientCall

namespace Proofs.ScalarCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.CppState (Cell)

-- The caller's state after a call that returned a scalar from the callee state `R`.
def finS (caller R : NState) : NState :=
  let scalars : CppState.State := {caller.scalars with
    memory := R.scalars.memory.take caller.scalars.memory.length,
    work := R.scalars.work+1,peak := max caller.scalars.peak R.scalars.peak}
  let frame : Frame := {noopRetired R.frame with bindings := caller.frame.bindings}
  (⟨scalars.observe 0,frame,caller.slots,caller.scope,max caller.peak R.peak⟩ : NState).observe

theorem finish_scalar (caller R : NState) (ty : Ty) (c : Int) (hc : ty.valid c = true)
    (cond : caller.scalars.memory.length ≤ R.scalars.memory.length ∧
      (R.scalars.memory.take caller.scalars.memory.length).map Cell.type = caller.scalars.memory.map Cell.type)
    (valid : R.frame.state.wellFormed = true) (fresh : ∀ owner, R.frame.state.forest.context owner ≠ some R.scope) :
    finish caller R (.scalar ty) (some (.scalar c)) = some (finS caller R,.scalar c) := by
  have retired := retireScope_fresh R.frame R.scope valid fresh
  unfold finish
  rw [if_pos cond]
  simp only [hc,if_true,retired,Bind.bind,Option.bind]
  rfl


theorem peak_final3 (SPB TPB cp tp tsp tlive tst rsp rst : Nat) (h1 : tp ≤ SPB+TPB) (h2 : tsp ≤ SPB)
    (h3 : tlive ≤ SPB) (h4 : tst ≤ TPB) (h5 : rsp ≤ SPB) (h6 : rst ≤ TPB) :
    max (max cp tp) (rsp+rst) ≤ max cp (SPB+TPB) := by omega

-- What a call to a scalar-only function leaves behind in the caller's state.
structure ScalarPost (caller Sinit res : NState) (kn extra : Nat) : Prop where
  valid : res.frame.state.wellFormed = true
  objects : res.frame.state.storage.objects.length = caller.frame.state.storage.objects.length
  live : res.frame.state.liveSpace = caller.frame.state.liveSpace
  storageWork : res.frame.state.storage.work = caller.frame.state.storage.work
  rwLength : res.frame.rootWritable.length = caller.frame.state.storage.objects.length
  slots : res.slots = caller.slots
  scope : res.scope = caller.scope
  bindings : res.frame.bindings = caller.frame.bindings
  scalarMemory : res.scalars.memory = caller.scalars.memory
  storagePeak : res.frame.state.storage.peak ≤ max caller.frame.state.storage.peak caller.frame.state.liveSpace
  scalarWork : res.scalars.work ≤ caller.scalars.work+kn+extra
  scalarPeak : res.scalars.peak ≤ max (max Sinit.scalars.peak Sinit.peak)
    ((callerP caller).length+12-caller.scalars.baseMemory+100)
  outerPeak : res.peak ≤ max caller.peak (max (max Sinit.scalars.peak Sinit.peak)
      ((callerP caller).length+12-caller.scalars.baseMemory+100) +
    max caller.frame.state.storage.peak caller.frame.state.liveSpace)

theorem scalar_post (caller Sinit R : NState) (kn extra W : Nat) {cells : List Cell} {nb SPB TPB : Nat}
    (hSPB : SPB = max (max Sinit.scalars.peak Sinit.peak) ((callerP caller).length+12-caller.scalars.baseMemory+100))
    (hTPB : TPB = max caller.frame.state.storage.peak caller.frame.state.liveSpace)
    (hmem : R.scalars.memory = callerP caller ++ cells) (hbl : R.scalars.bindings.length = nb)
    (hnb : nb ≤ 60) (hcells : cells.length ≤ 60) (hbase : R.scalars.baseMemory = caller.scalars.baseMemory)
    (hbm : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (spC : caller.scalars.peak ≤ Sinit.scalars.peak)
    (fa : FA R.frame caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope+1)
      caller.frame.state.storage.objects.length)
    (cq : Cq SPB TPB W R) (hw : R.scalars.work+1 ≤ caller.scalars.work+kn+extra) :
    ScalarPost caller Sinit (finS caller R) kn extra := by
  have same := noopRetired_same R.frame
  have take : R.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hmem]; simp only [callerP,List.append_assoc]; exact List.take_left
  have lenP : (callerP caller).length = caller.scalars.memory.length+
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeLen : (R.scalars.memory.take caller.scalars.memory.length).length = caller.scalars.memory.length := by
    rw [take]
  have spR : R.scalars.peak ≤ SPB := cq.scalarPeak
  have stR : R.frame.state.storage.peak ≤ TPB := cq.storagePeak
  have opR : R.peak ≤ SPB+TPB := cq.outerPeak
  have resSp : (finS caller R).scalars.peak =
      max (max caller.scalars.peak R.scalars.peak)
        ((R.scalars.memory.take caller.scalars.memory.length).length-caller.scalars.baseMemory+
          caller.scalars.bindings.length+0) := rfl
  have spRes : (finS caller R).scalars.peak ≤ SPB := by
    rw [resSp,takeLen]
    have h2 : caller.scalars.peak ≤ SPB := by rw [hSPB]; omega
    have h4 : caller.scalars.memory.length-caller.scalars.baseMemory+caller.scalars.bindings.length+0 ≤ SPB := by
      rw [hSPB]; omega
    omega
  have stRes : (finS caller R).frame.state.storage.peak ≤ TPB := by
    show max R.frame.state.storage.peak (R.frame.state.liveSpace-R.frame.state.storage.baseSpace) ≤ TPB
    rw [hTPB] at stR ⊢
    have := fa.live
    omega
  have resPeak : (finS caller R).peak = max (max caller.peak R.peak)
      ((finS caller R).scalars.peak + (finS caller R).frame.state.storage.peak) := rfl
  have wf := (wellFormed_parts _ fa.valid).1
  refine ⟨?_,?_,?_,?_,?_,rfl,rfl,rfl,?_,?_,?_,?_,?_⟩
  · show (noopRetired R.frame).state.wellFormed = true
    rw [same.wellFormed]; exact fa.valid
  · show (noopRetired R.frame).state.storage.objects.length = _
    rw [same.2.1]; exact fa.count
  · show (noopRetired R.frame).state.liveSpace = _
    rw [same.liveSpace]; exact fa.live
  · show R.frame.state.storage.work = _
    exact fa.work
  · show R.frame.rootWritable.length = _
    have := fa.lengths
    have := fa.count
    omega
  · show R.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory
    exact take
  · rw [hTPB] at stRes; exact stRes
  · show R.scalars.work+1 ≤ _
    exact hw
  · rw [hSPB] at spRes; exact spRes
  · rw [resPeak]
    have key : max (max caller.peak R.peak) ((finS caller R).scalars.peak + (finS caller R).frame.state.storage.peak)
        ≤ max caller.peak (SPB+TPB) := peak_final3 SPB TPB _ _ _ _ _ _ _ opR spR spR stR spRes stRes
    rw [hSPB,hTPB] at key
    exact key

-- What a call to a scalar-only function leaves behind in the caller's state.
structure ScalarPost2 (caller Sinit res : NState) (kn extra : Nat) (mem : List Cell) : Prop where
  valid : res.frame.state.wellFormed = true
  objects : res.frame.state.storage.objects.length = caller.frame.state.storage.objects.length
  live : res.frame.state.liveSpace = caller.frame.state.liveSpace
  storageWork : res.frame.state.storage.work = caller.frame.state.storage.work
  rwLength : res.frame.rootWritable.length = caller.frame.state.storage.objects.length
  slots : res.slots = caller.slots
  scope : res.scope = caller.scope
  bindings : res.frame.bindings = caller.frame.bindings
  scalarMemory : res.scalars.memory = mem
  storagePeak : res.frame.state.storage.peak ≤ max caller.frame.state.storage.peak caller.frame.state.liveSpace
  scalarWork : res.scalars.work ≤ caller.scalars.work+kn+extra
  scalarPeak : res.scalars.peak ≤ max (max Sinit.scalars.peak Sinit.peak)
    ((callerP caller).length+12-caller.scalars.baseMemory+100)
  outerPeak : res.peak ≤ max caller.peak (max (max Sinit.scalars.peak Sinit.peak)
      ((callerP caller).length+12-caller.scalars.baseMemory+100) +
    max caller.frame.state.storage.peak caller.frame.state.liveSpace)

theorem scalar_post2 (caller Sinit R : NState) (kn extra W : Nat) {mem : List Cell} {SPB TPB : Nat}
    (hSPB : SPB = max (max Sinit.scalars.peak Sinit.peak) ((callerP caller).length+12-caller.scalars.baseMemory+100))
    (hTPB : TPB = max caller.frame.state.storage.peak caller.frame.state.liveSpace)
    (htake : R.scalars.memory.take caller.scalars.memory.length = mem) (hmemLen : mem.length = caller.scalars.memory.length)
    (hbase : R.scalars.baseMemory = caller.scalars.baseMemory)
    (hbm : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (spC : caller.scalars.peak ≤ Sinit.scalars.peak)
    (fa : FA R.frame caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope+1)
      caller.frame.state.storage.objects.length)
    (cq : Cq SPB TPB W R) (hw : R.scalars.work+1 ≤ caller.scalars.work+kn+extra) :
    ScalarPost2 caller Sinit (finS caller R) kn extra mem := by
  have same := noopRetired_same R.frame
  have lenP : (callerP caller).length = caller.scalars.memory.length+
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeLen : (R.scalars.memory.take caller.scalars.memory.length).length = caller.scalars.memory.length := by
    rw [htake]; exact hmemLen
  have spR : R.scalars.peak ≤ SPB := cq.scalarPeak
  have stR : R.frame.state.storage.peak ≤ TPB := cq.storagePeak
  have opR : R.peak ≤ SPB+TPB := cq.outerPeak
  have resSp : (finS caller R).scalars.peak =
      max (max caller.scalars.peak R.scalars.peak)
        ((R.scalars.memory.take caller.scalars.memory.length).length-caller.scalars.baseMemory+
          caller.scalars.bindings.length+0) := rfl
  have spRes : (finS caller R).scalars.peak ≤ SPB := by
    rw [resSp,takeLen]
    have h2 : caller.scalars.peak ≤ SPB := by rw [hSPB]; omega
    have h4 : caller.scalars.memory.length-caller.scalars.baseMemory+caller.scalars.bindings.length+0 ≤ SPB := by
      rw [hSPB]; omega
    omega
  have stRes : (finS caller R).frame.state.storage.peak ≤ TPB := by
    show max R.frame.state.storage.peak (R.frame.state.liveSpace-R.frame.state.storage.baseSpace) ≤ TPB
    rw [hTPB] at stR ⊢
    have := fa.live
    omega
  have resPeak : (finS caller R).peak = max (max caller.peak R.peak)
      ((finS caller R).scalars.peak + (finS caller R).frame.state.storage.peak) := rfl
  have wf := (wellFormed_parts _ fa.valid).1
  refine ⟨?_,?_,?_,?_,?_,rfl,rfl,rfl,?_,?_,?_,?_,?_⟩
  · show (noopRetired R.frame).state.wellFormed = true
    rw [same.wellFormed]; exact fa.valid
  · show (noopRetired R.frame).state.storage.objects.length = _
    rw [same.2.1]; exact fa.count
  · show (noopRetired R.frame).state.liveSpace = _
    rw [same.liveSpace]; exact fa.live
  · show R.frame.state.storage.work = _
    exact fa.work
  · show R.frame.rootWritable.length = _
    have := fa.lengths
    have := fa.count
    omega
  · show R.scalars.memory.take caller.scalars.memory.length = mem
    exact htake
  · rw [hTPB] at stRes; exact stRes
  · show R.scalars.work+1 ≤ _
    exact hw
  · rw [hSPB] at spRes; exact spRes
  · rw [resPeak]
    have key : max (max caller.peak R.peak) ((finS caller R).scalars.peak + (finS caller R).frame.state.storage.peak)
        ≤ max caller.peak (SPB+TPB) := peak_final3 SPB TPB _ _ _ _ _ _ _ opR spR spR stR spRes stRes
    rw [hSPB,hTPB] at key
    exact key


end Proofs.ScalarCall
