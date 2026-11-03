import Proofs.CppRowsGraph
import Proofs.CppNestedStmt

namespace Proofs.CppRowsStmt
open Proofs.CppScalar Proofs.CppMixedInvoke Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedSim Proofs.CppNestedEval
open Proofs.CppVector Proofs.CppNestedFacts Proofs.CppNestedConstruct Proofs.CppNestedStmt
open Proofs.CppRowsGraph

theorem eval_row (s : NState) (slot rb : Nat) (idx : NExpr) (k R sc epoch owner : Nat) (ids : List Nat) (ty : Ty)
    (scalar : idx.scalarOnly = true) (value : idx.denote (envOf s) = some (k : Int))
    (hslot : s.vectorSlot slot = some rb)
    (binding : s.frame.bindings[rb]? = some ⟨R,.vector (.integer ty),true,.root sc⟩)
    (g : Rows s.frame.state R ty sc ids epoch)
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (flag : s.frame.rootWritable[R]? = some true) (lookup : ids[k]? = some owner) :
    ∃ t, (Container.row (.local slot) (.integer ty) idx).eval s = some (t,s.frame.bindings.length) ∧
      GoodF s t (idx.nodes+2) (idx.nodes+2) ∧ t.frame.bindings = s.frame.bindings ++ [CppRowsGraph.binding R ty epoch k owner true] := by
  have parent := eval_local (s.charge 0 ((Container.local slot).nodes+idx.nodes+1)) slot rb
    (by simpa [NState.vectorSlot] using hslot)
  have env : envOf ((s.charge 0 ((Container.local slot).nodes+idx.nodes+1)).charge 1 1) = envOf s :=
    envOf_core (Core.trans (core_charge _ _ _) (core_charge _ _ _))
  obtain ⟨t1,hidx,good1⟩ := scalar_eval idx _ k scalar (by rw [env]; exact value)
  have frame1 : t1.frame = s.frame := by
    have := good1.1.1
    simpa using this
  have chi := CppRowsGraph.child_row s.frame rb R ty sc ids epoch k owner g lookup true true binding lengths flag (fun h => h)
  simp only [Frame.addBinding] at chi
  refine ⟨({t1 with frame := {s.frame with bindings := s.frame.bindings ++ [CppRowsGraph.binding R ty epoch k owner true]}} : NState).charge 1 1,?_,?_,?_⟩
  · have hv : (s.charge 0 ((Container.local slot).nodes+idx.nodes+1)).vectorSlot slot = some rb := by
      simpa [NState.vectorSlot] using hslot
    simp [Container.eval,hv,hidx,chi,frame1]
  · have a := (GoodF.charge s 0 ((Container.local slot).nodes+idx.nodes+1)).trans
      ((GoodF.charge _ 1 1).trans good1.toF)
    have b := a.withFrame {s.frame with bindings := s.frame.bindings ++ [CppRowsGraph.binding R ty epoch k owner true]}
      (by simp [frame1]) (by simp [frame1])
    have c := b.trans (GoodF.charge ({t1 with frame := {s.frame with bindings := s.frame.bindings ++ [CppRowsGraph.binding R ty epoch k owner true]}} : NState) 1 1)
    refine c.mono ?_ ?_ <;> simp [Container.nodes] <;> omega
  · simp

end Proofs.CppRowsStmt
