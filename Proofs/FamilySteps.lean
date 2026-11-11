import Proofs.AppendCapacity
import Proofs.DynamicExprAuto
import Proofs.DynamicConstructCore

/-!
Scalar statements over an arbitrary expression (which may read vectors) on a `MultiVecDynamic.Family`.

The pure denotation `DynamicExpr.denote` of the expression yields its actual evaluation
(`DynamicExprAuto.sound`); these lemmas turn it into the run of a `declare`, an `assign` or a branch
condition, with the Family kept and the scalar work and peaks bounded.
-/

namespace Proofs.FamilySteps
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppNestedEval Proofs.CppNestedSim Proofs.CppNestedStmt
open Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic Proofs.DynamicExpr Proofs.DynamicContents

/-- The actual evaluation of an expression whose pure denotation over the Family's contents succeeds. -/
theorem eval_of_denote {params : List Parameter} {h : Heap} {m : Resources} {s : NState}
    (family : Family params h s.frame m) (e : NExpr) (v : Int)
    (pure : denote params (snapshot s) (eraseHeap h) e = some v) :
    ∃ t extra, Ev s e t v extra (2*e.nodes) (2*e.nodes) :=
  (DynamicExprAuto.sound params (snapshot s) (eraseHeap h) e v pure s
    (DynamicRealizes.of_family params h m s family)).2

/-- After evaluating an expression and releasing its temporaries. -/
structure Released (s u : NState) (w p : Nat) : Prop where
  state : u.frame.state = s.frame.state
  rights : u.frame.rootWritable = s.frame.rootWritable
  bindings : u.frame.bindings = s.frame.bindings
  slots : u.slots = s.slots
  scope : u.scope = s.scope
  memory : u.scalars.memory = s.scalars.memory
  scalarBindings : u.scalars.bindings = s.scalars.bindings
  base : u.scalars.baseMemory = s.scalars.baseMemory
  workLower : s.scalars.work ≤ u.scalars.work
  workUpper : u.scalars.work ≤ s.scalars.work+w
  peakLower : s.scalars.peak ≤ u.scalars.peak
  peakUpper : u.scalars.peak ≤ max s.scalars.peak (liveS s+p)
  outerLower : s.peak ≤ u.peak
  outerUpper : u.peak ≤ max s.peak (u.scalars.peak+u.frame.state.storage.peak)

theorem released_of_ev {s t : NState} {e : NExpr} {v : Int} {extra : List Binding} {w p : Nat}
    (ev : Ev s e t v extra w p) : Released s ((t.release s).charge 1 0) (w+1) p := by
  obtain ⟨_,⟨state,rights,slots,scope,memory,bindings,base,wl,wu,pl,pu,ql,qu⟩,frameBindings⟩ := ev
  have live : liveS t = liveS s := liveS_of_memory memory bindings base
  have hp := charge_release_peak t s 1 0
  refine ⟨by simpa using state,by simpa using rights,?_,by simpa using slots,by simpa using scope,
    by simpa using memory,by simpa using bindings,by simpa using base,?_,?_,?_,?_,?_,?_⟩
  · simp [frameBindings]
  · simp [charge_work]; omega
  · simp [charge_work]; omega
  · simp only [charge_scalar_peak,release_scalars]; omega
  · simp only [charge_scalar_peak,release_scalars]
    simp only [liveS] at live pu ⊢
    omega
  · rw [hp]; omega
  · rw [hp]
    have st : t.frame.state.storage.peak = s.frame.state.storage.peak := by rw [state]
    simp only [charge_storage,release_state]
    rw [st] at qu
    have : t.scalars.peak ≤ ((t.release s).charge 1 0).scalars.peak := by
      simp only [charge_scalar_peak,release_scalars]; omega
    omega

theorem Released.family {params : List Parameter} {h : Heap} {m : Resources} {s u : NState} {w p : Nat}
    (family : Family params h s.frame m) (r : Released s u w p) : Family params h u.frame m :=
  family.transport u.frame r.state r.rights (by intro q hq; rw [r.bindings]; exact family.bindings q hq)

/-- A branch or loop condition: its evaluation and the released state that continues. -/
theorem condition {params : List Parameter} {h : Heap} {m : Resources} {s : NState}
    (family : Family params h s.frame m) (e : NExpr) (v : Int)
    (pure : denote params (snapshot s) (eraseHeap h) e = some v) :
    ∃ next, e.eval s = some (next,v) ∧ Released s ((next.release s).charge 1 0) (2*e.nodes+1) (2*e.nodes) := by
  obtain ⟨t,extra,ev⟩ := eval_of_denote family e v pure
  exact ⟨t,ev.1,released_of_ev ev⟩

/-- Declaring a scalar local initialised by an arbitrary expression. -/
theorem declare {params : List Parameter} {h : Heap} {m : Resources} {s : NState}
    (family : Family params h s.frame m) (e : NExpr) (ty : Ty) (wr : Bool) (v v' : Int)
    (pure : denote params (snapshot s) (eraseHeap h) e = some v) (converted : ty.convert v = some v') :
    ∃ u, (NStmt.declare ty wr e).run s = some ⟨u,none,false⟩ ∧ Family params h u.frame m ∧
      u.frame.state = s.frame.state ∧ u.frame.rootWritable = s.frame.rootWritable ∧
      u.frame.bindings = s.frame.bindings ∧
      u.slots = s.slots ++ [.scalar s.scalars.bindings.length] ∧ u.scope = s.scope ∧
      u.scalars.memory = s.scalars.memory ++ [⟨ty,v'⟩] ∧
      u.scalars.bindings = s.scalars.bindings ++ [⟨s.scalars.memory.length,wr⟩] ∧
      u.scalars.baseMemory = s.scalars.baseMemory ∧
      s.scalars.work ≤ u.scalars.work ∧ u.scalars.work ≤ s.scalars.work+2*e.nodes+1 ∧
      s.scalars.peak ≤ u.scalars.peak ∧ u.scalars.peak ≤ max s.scalars.peak (liveS s+2*e.nodes+2) ∧
      s.peak ≤ u.peak ∧ u.peak ≤ max s.peak (u.scalars.peak+u.frame.state.storage.peak) := by
  obtain ⟨t,extra,ev⟩ := eval_of_denote family e v pure
  have run := declare_ev e ty wr s t v v' extra _ _ ev converted
  obtain ⟨_,⟨state,rights,slots,scope,memory,bindings,base,wl,wu,pl,pu,ql,qu⟩,frameBindings⟩ := ev
  have relFamily : Family params h (t.release s).frame m :=
    DynamicConstructCore.release_family family ⟨state,rights,slots,scope,memory,bindings,base,wl,wu,pl,pu,ql,qu⟩
      extra frameBindings
  refine ⟨_,run,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [NState.declared] using relFamily
  · simp [NState.declared,state]
  · simp [NState.declared,rights]
  · simp [NState.declared,frameBindings]
  · simp [NState.declared,slots,bindings]
  · simp [NState.declared,scope]
  · simp [NState.declared,memory]
  · simp [NState.declared,bindings,memory]
  · simp [NState.declared,base]
  · simp [NState.declared,charge_work]; omega
  · simp [NState.declared,charge_work]; omega
  · simp [NState.declared,charge_scalar_peak]; omega
  · simp [NState.declared,charge_scalar_peak,liveS,memory,bindings,base]
    unfold liveS at pu; omega
  · simp [NState.declared,charge_peak]; omega
  · simp [NState.declared,charge_peak,charge_scalar_peak,state]
    have st : t.frame.state.storage.peak = s.frame.state.storage.peak := by rw [state]
    rw [st] at qu
    omega

/-- Assigning an arbitrary expression to a writable scalar local. -/
theorem assign {params : List Parameter} {h : Heap} {m : Resources} {s : NState}
    (family : Family params h s.frame m) (e : NExpr) (slot idx : Nat) (ty : Ty) (v v' : Int)
    (binding : CppState.Binding) (cell : CppState.Cell)
    (pure : denote params (snapshot s) (eraseHeap h) e = some v) (converted : ty.convert v = some v')
    (hs : s.slots[slot]? = some (.scalar idx)) (hb : s.scalars.bindings[idx]? = some binding)
    (hm : s.scalars.memory[binding.address]? = some cell) (ctype : cell.type = ty)
    (cvalid : ty.valid cell.value = true) (writable : binding.writable = true) :
    ∃ u, (NStmt.assign slot ty e).run s = some ⟨u,none,false⟩ ∧ Family params h u.frame m ∧
      u.frame.state = s.frame.state ∧ u.frame.rootWritable = s.frame.rootWritable ∧
      u.frame.bindings = s.frame.bindings ∧ u.slots = s.slots ∧ u.scope = s.scope ∧
      u.scalars.memory = s.scalars.memory.set binding.address ⟨ty,v'⟩ ∧
      u.scalars.bindings = s.scalars.bindings ∧ u.scalars.baseMemory = s.scalars.baseMemory ∧
      s.scalars.work ≤ u.scalars.work ∧ u.scalars.work ≤ s.scalars.work+2*e.nodes+1 ∧
      s.scalars.peak ≤ u.scalars.peak ∧ u.scalars.peak ≤ max s.scalars.peak (liveS s+2*e.nodes) ∧
      s.peak ≤ u.peak ∧ u.peak ≤ max s.peak (u.scalars.peak+u.frame.state.storage.peak) := by
  obtain ⟨t,extra,ev⟩ := eval_of_denote family e v pure
  obtain ⟨ran,⟨state,rights,slots,scope,memory,bindings,base,wl,wu,pl,pu,ql,qu⟩,frameBindings⟩ := ev
  have relFamily : Family params h (t.release s).frame m :=
    DynamicConstructCore.release_family family ⟨state,rights,slots,scope,memory,bindings,base,wl,wu,pl,pu,ql,qu⟩
      extra frameBindings
  have cellFound : (t.release s).scalarCell slot ty = some (binding,cell) := by
    simp [NState.scalarCell,NState.scalarSlot,slots,bindings,memory,hs,hb,hm,ctype,cvalid]
  have run := assign_run e slot ty s t v v' binding cell ran cellFound writable converted
  refine ⟨_,run,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa using relFamily
  · simp [state]
  · simp [rights]
  · simp [frameBindings]
  · simp [slots]
  · simp [scope]
  · simp [memory,ctype]
  · simp [bindings]
  · simp [base]
  · simp [charge_work]; omega
  · simp [charge_work]; omega
  · simp [charge_scalar_peak]; omega
  · simp [charge_scalar_peak]
    have tl : t.scalars.memory.length = s.scalars.memory.length := by rw [memory]
    unfold liveS at pu ⊢
    rw [tl,bindings,base]
    omega
  · simp [charge_peak]; omega
  · simp [charge_peak,charge_scalar_peak,state]
    have st : t.frame.state.storage.peak = s.frame.state.storage.peak := by rw [state]
    rw [st] at qu
    omega

end Proofs.FamilySteps
