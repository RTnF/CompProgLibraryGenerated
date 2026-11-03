import Proofs.DynamicStmt

namespace Proofs.DynamicScalarSteps
open Proofs.CppScalar Proofs.CppMixedInvoke Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedSim
open Proofs.MultiVecDynamic Proofs.DynamicContents Proofs.DynamicExpr Proofs.DynamicRealizes

@[simp] theorem snapshot_charge (s : NState) (w p : Nat) : snapshot (s.charge w p) = snapshot s := rfl
@[simp] theorem snapshot_release (s before : NState) : snapshot (s.release before) = snapshot s := rfl
@[simp] theorem snapshot_declared (s : NState) (ty : Ty) (writable : Bool) (v : Int) :
    snapshot (s.declared ty writable v) = DynamicStmt.declared (snapshot s) ty writable v := rfl

theorem snapshot_cell (s : NState) (slot : Nat) (ty : Ty) :
    DynamicStmt.scalarCell (snapshot s) slot ty = s.scalarCell slot ty := by
  simp only [DynamicStmt.scalarCell,snapshot,NState.scalarCell,NState.scalarSlot]
  cases found : s.slots[slot]? with
  | none => rfl
  | some location => cases location <;> rfl

theorem relocate (params : List Parameter) (l l' : Locals) (h : ContentsHeap)
    (s t : NState) (realizes : Realizes params l h s)
    (frame : t.frame = s.frame) (locals : snapshot t = l') : Realizes params l' h t := by
  obtain ⟨heap,m,family,he⟩ := realizes.heap
  exact ⟨locals,heap,m,by rw [frame]; exact family,he⟩

-- The declaration creates one scalar cell and one scalar binding. The upper
-- bound allows their live-space increase in addition to expression temporaries.
theorem declaration (params : List Parameter) (l : Locals) (h : ContentsHeap)
    (s t : NState) (realizes : Realizes params l h s) (e : NExpr) (v v' : Int)
    (extra : List Binding) (w p : Nat) (ev : Ev s e t v extra w p)
    (ty : Ty) (writable : Bool) (converted : ty.convert v = some v') :
    ∃ out, (NStmt.declare ty writable e).run s = some ⟨out,none,false⟩ ∧
      Realizes params (DynamicStmt.declared l ty writable v') h out ∧
      out.work ≤ s.work+w+1 ∧ out.peak ≤ max s.peak
        (max s.scalars.peak (liveS s+p+2)+s.frame.state.storage.peak) := by
  let out := ((t.release s).declared ty writable v').charge 1 0
  obtain ⟨mid,_,work,_⟩ := ev_preserves params l h s t realizes e v extra w p ev
  have snapped : snapshot t = l := by simpa using mid.locals
  have finalLocals : snapshot out = DynamicStmt.declared l ty writable v' := by
    simp only [out,snapshot_charge,snapshot_declared,snapshot_release,snapped]
  have after : Realizes params (DynamicStmt.declared l ty writable v') h out :=
    relocate params l _ h ((t.release s).charge 1 0) out mid rfl finalLocals
  have sameWork : out.work = ((t.release s).charge 1 0).work := rfl
  obtain ⟨state,_,_,_,memory,bindings,base,_,_,_,scalarPeak,_,peak⟩ := ev.2.1
  have innerLive := liveS_of_memory memory bindings base
  have oldStorage : t.frame.state.storage.peak = s.frame.state.storage.peak := by rw [state]
  have outPeak : out.peak = max t.peak
      (max t.scalars.peak ((t.scalars.memory.length+1)-t.scalars.baseMemory+(t.scalars.bindings.length+1))+
        s.frame.state.storage.peak) := by
    simp [out,NState.declared,NState.release,charge_peak,oldStorage]
  rw [oldStorage] at peak
  have liveBound : (t.scalars.memory.length+1)-t.scalars.baseMemory+(t.scalars.bindings.length+1) ≤ liveS s+2 := by
    change t.scalars.memory.length-t.scalars.baseMemory+t.scalars.bindings.length = liveS s at innerLive
    omega
  refine ⟨out,declare_ev e ty writable s t v v' extra w p ev converted,after,?_,?_⟩
  · rw [sameWork]; exact work
  · omega

theorem assignment (params : List Parameter) (l : Locals) (h : ContentsHeap)
    (s t : NState) (realizes : Realizes params l h s) (e : NExpr) (v v' : Int)
    (extra : List Binding) (w p : Nat) (ev : Ev s e t v extra w p) (slot : Nat) (ty : Ty)
    (binding : Proofs.CppState.Binding) (cell : Proofs.CppState.Cell)
    (found : DynamicStmt.scalarCell l slot ty = some (binding,cell)) (writable : binding.writable = true)
    (converted : ty.convert v = some v') :
    ∃ out, (NStmt.assign slot ty e).run s = some ⟨out,none,false⟩ ∧
      Realizes params (DynamicStmt.assigned l binding cell v') h out ∧
      out.work ≤ s.work+w+1 ∧ out.peak ≤ max s.peak
        (max s.scalars.peak (liveS s+p)+s.frame.state.storage.peak) := by
  let out := ({t.release s with scalars := {(t.release s).scalars with
    memory := (t.release s).scalars.memory.set binding.address ⟨cell.type,v'⟩}} : NState).charge 1 0
  obtain ⟨mid,_,work,peak⟩ := ev_preserves params l h s t realizes e v extra w p ev
  have snapped : snapshot t = l := by simpa using mid.locals
  have resolved : (t.release s).scalarCell slot ty = some (binding,cell) := by
    rw [← snapshot_cell,snapshot_release,snapped]
    exact found
  have finalLocals : snapshot out = DynamicStmt.assigned l binding cell v' := by
    change DynamicStmt.assigned (snapshot t) binding cell v' = _
    rw [snapped]
  have after := relocate params l _ h ((t.release s).charge 1 0) out mid rfl finalLocals
  have sameWork : out.work = ((t.release s).charge 1 0).work := rfl
  have samePeak : out.peak = ((t.release s).charge 1 0).peak := by
    simp [out,NState.release,charge_peak]
  exact ⟨out,assign_run e slot ty s t v v' binding cell ev.1 resolved writable converted,
    after,by rw [sameWork]; exact work,by rw [samePeak]; exact peak⟩

end Proofs.DynamicScalarSteps
