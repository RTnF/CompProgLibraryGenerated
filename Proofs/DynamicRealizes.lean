import Proofs.DynamicExpr
import Proofs.DynamicRowsRead

namespace Proofs.DynamicRealizes
open Proofs.CppScalar Proofs.CppMixedInvoke Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedSim
open Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic
open Proofs.DynamicContents Proofs.DynamicExpr

-- Allocation metadata is existential: logical execution keeps scalar locals
-- and contents, while Family supplies the concrete ownership and resources.
structure Realizes (params : List Parameter) (locals : Locals) (contents : ContentsHeap) (s : NState) : Prop where
  locals : snapshot s = locals
  heap : ∃ h m, Family params h s.frame m ∧ eraseHeap h = contents

theorem of_family (params : List Parameter) (h : Heap) (m : Resources) (s : NState)
    (family : Family params h s.frame m) : Realizes params (snapshot s) (eraseHeap h) s :=
  ⟨rfl,h,m,family,rfl⟩

theorem scalar_denote (params : List Parameter) (locals : Locals) (contents : ContentsHeap)
    (s : NState) (realizes : Realizes params locals contents s) (e : NExpr)
    (scalar : e.scalarOnly = true) : DynamicExpr.denote params locals contents e = e.denote (envOf s) := by
  rw [DynamicExpr.denote_scalar params locals contents e scalar,← realizes.locals,snapshot_env]

-- Evaluating and releasing an expression preserves the logical state. Work
-- and peak remain linked to the actual execution rather than to ghost IDs.
theorem ev_preserves (params : List Parameter) (locals : Locals) (contents : ContentsHeap)
    (s t : NState) (realizes : Realizes params locals contents s) (e : NExpr) (v : Int)
    (extra : List Binding) (w p : Nat) (ev : Ev s e t v extra w p) :
    Realizes params locals contents ((t.release s).charge 1 0) ∧
      s.work ≤ ((t.release s).charge 1 0).work ∧
      ((t.release s).charge 1 0).work ≤ s.work+w+1 ∧
      ((t.release s).charge 1 0).peak ≤ max s.peak
        (max s.scalars.peak (liveS s+p)+s.frame.state.storage.peak) := by
  obtain ⟨h,m,family,he⟩ := realizes.heap
  obtain ⟨state,rights,slots,scope,memory,bindings,base,lower,upper,pl,pu,ql,qu⟩ := ev.2.1
  have frameBindings : ((t.release s).charge 1 0).frame.bindings = s.frame.bindings := by
    simp [NState.release,ev.2.2]
  have afterFamily : Family params h ((t.release s).charge 1 0).frame m :=
    family.transport _ (by simpa [NState.release] using state) (by simpa [NState.release] using rights)
      (by intro q hq; rw [frameBindings]; exact family.bindings q hq)
  have snapshotEq : snapshot ((t.release s).charge 1 0) = snapshot s := by
    simp [snapshot,NState.release,memory,bindings,slots]
  have workEq : ((t.release s).charge 1 0).work = t.scalars.work+1+s.frame.state.storage.work := by
    simp [NState.work,NState.release,charge_work,state]
  have scalarPeak : ((t.release s).charge 1 0).scalars.peak ≤ max s.scalars.peak (liveS s+p) := by
    have live := liveS_of_memory memory bindings base
    simp only [charge_scalar_peak,release_scalars]
    change max t.scalars.peak (liveS t+0) ≤ _
    rw [live]
    omega
  have finalPeak := charge_release_peak t s 1 0
  rw [state] at qu finalPeak
  refine ⟨⟨snapshotEq.trans realizes.locals,h,m,afterFamily,he⟩,?_,?_,?_⟩
  · change s.scalars.work+s.frame.state.storage.work ≤ ((t.release s).charge 1 0).work
    rw [workEq]
    omega
  · change _ ≤ (s.scalars.work+s.frame.state.storage.work)+w+1
    rw [workEq]
    omega
  · omega

end Proofs.DynamicRealizes
