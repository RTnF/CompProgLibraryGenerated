import Proofs.CppConstructorPeak

namespace Proofs.CppScalarComponents
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedEval Proofs.CppNestedStmt

-- Component bounds avoid charging the resident vector a second time when
-- combining consecutive scalar field initializers.
theorem declare_components (s out : NState) (ty : Ty) (wr : Bool) (e : NExpr) (v x : Int)
    (scalar : e.scalarOnly = true) (value : e.denote (envOf s) = some v)
    (converted : ty.convert v = some x)
    (actual : (NStmt.declare ty wr e).run s = some ⟨out,none,false⟩) :
    out.frame = s.frame ∧ out.scalars.baseMemory = s.scalars.baseMemory ∧
    out.scalars.memory.length = s.scalars.memory.length+1 ∧
    out.scalars.bindings.length = s.scalars.bindings.length+1 ∧
    out.scalars.peak ≤ max s.scalars.peak (liveS s+e.nodes+2) := by
  obtain ⟨t,ran,good⟩ := scalar_eval e s v scalar value
  obtain ⟨⟨frame,slots,scope,memory,bindings,base⟩,_,_,_,_,scalarPeak,_,_⟩ := good
  simp only [NStmt.run,ran,Bind.bind,Option.bind,converted] at actual
  have same := congrArg NStep.state (Option.some.inj actual)
  change _ = out at same
  subst out
  refine ⟨?_,base,?_,?_,?_⟩
  · simp [NState.charge,NState.observe,NState.release,frame]
  · simp [NState.charge,NState.observe,Proofs.CppState.State.observe,NState.release,memory]
  · simp [NState.charge,NState.observe,Proofs.CppState.State.observe,NState.release,bindings]
  · simp only [NState.charge,NState.observe,Proofs.CppState.State.observe,NState.release,
      List.length_append,List.length_singleton,Nat.add_zero,memory,bindings,base]
    unfold liveS at scalarPeak ⊢
    omega

theorem check_components (s out : NState) (e : NExpr) (v : Int)
    (scalar : e.scalarOnly = true) (value : e.denote (envOf s) = some v) (nonzero : v ≠ 0)
    (actual : (NStmt.check e).run s = some ⟨out,none,false⟩) :
    Core s out ∧ out.scalars.peak ≤ max s.scalars.peak (liveS s+e.nodes) := by
  obtain ⟨t,ran,good⟩ := scalar_eval e s v scalar value
  have core := good.1
  obtain ⟨frame,slots,scope,memory,bindings,base⟩ := core
  have scalarPeak := good.2.2.2.2.2.1
  simp only [NStmt.run,ran,Bind.bind,Option.bind,beq_iff_eq,if_neg nonzero] at actual
  have same := congrArg NStep.state (Option.some.inj actual)
  change _ = out at same
  subst out
  refine ⟨?_,?_⟩
  · simp [Core,NState.charge,NState.observe,Proofs.CppState.State.observe,NState.release,
      frame,slots,scope,memory,bindings,base]
  · simp only [NState.charge,NState.observe,Proofs.CppState.State.observe,NState.release,
      Nat.add_zero,memory,bindings,base]
    unfold liveS at scalarPeak ⊢
    omega

theorem fill_components (s out : NState) (ty : Ty) (wr : Bool) (count value : NExpr) (n x : Int)
    (countScalar : count.scalarOnly = true) (valueScalar : value.scalarOnly = true)
    (countValue : count.denote (envOf s) = some n) (fillValue : value.denote (envOf s) = some x)
    (nonnegative : 0 ≤ n)
    (actual : (NStmt.fillVector ty wr count value).run s = some ⟨out,none,false⟩) :
    out.scalars.baseMemory = s.scalars.baseMemory ∧
    out.scalars.memory = s.scalars.memory ∧ out.scalars.bindings = s.scalars.bindings ∧
    out.scalars.peak ≤ max s.scalars.peak (liveS s+max count.nodes value.nodes) := by
  obtain ⟨a,ra,ga⟩ := scalar_eval count s n countScalar countValue
  obtain ⟨b,rb,gb⟩ := scalar_eval value a x valueScalar (by rw [envOf_core ga.1]; exact fillValue)
  have good := ga.trans gb
  obtain ⟨⟨frame,slots,scope,memory,bindings,base⟩,_,_,_,_,scalarPeak,_,_⟩ := good
  simp only [NStmt.run,ra,rb,Bind.bind,Option.bind,if_pos nonnegative] at actual
  obtain ⟨next,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ actual
  obtain ⟨pair,_,same⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  obtain ⟨installed,index⟩ := pair
  have eq := congrArg NStep.state (Option.some.inj same)
  change _ = out at eq
  subst out
  refine ⟨base,memory,bindings,?_⟩
  simp only [NState.charge,NState.observe,Proofs.CppState.State.observe,NState.release,
    Nat.add_zero,memory,bindings,base]
  unfold liveS at scalarPeak ⊢
  omega

theorem empty_components (s out : NState) (ty : Ty) (wr : Bool)
    (actual : (NStmt.declareVector ty wr).run s = some ⟨out,none,false⟩) :
    out.scalars.baseMemory = s.scalars.baseMemory ∧
    out.scalars.memory = s.scalars.memory ∧ out.scalars.bindings = s.scalars.bindings ∧
    out.scalars.peak = max s.scalars.peak (liveS s) := by
  unfold NStmt.run at actual
  obtain ⟨next,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ actual
  obtain ⟨pair,_,same⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  obtain ⟨installed,index⟩ := pair
  have eq := congrArg NStep.state (Option.some.inj same)
  change _ = out at eq
  subst out
  exact ⟨rfl,rfl,rfl,by simp [NState.charge,NState.observe,Proofs.CppState.State.observe,liveS]⟩

theorem declare_owned_components (st next : Proofs.DynamicOwnedState.State) (s out : NState)
    (real : Proofs.DynamicOwnedState.Realizes st s) (ty : Ty) (wr : Bool) (e : NExpr)
    (scalar : e.scalarOnly = true)
    (pureRun : Proofs.DynamicOwnedControl.primitive (.declare ty wr e) st = some ⟨next,none,false⟩)
    (actual : (NStmt.declare ty wr e).run s = some ⟨out,none,false⟩) :
    out.frame = s.frame ∧ out.scalars.baseMemory = s.scalars.baseMemory ∧
    out.scalars.memory.length = s.scalars.memory.length+1 ∧
    out.scalars.bindings.length = s.scalars.bindings.length+1 ∧
    out.scalars.peak ≤ max s.scalars.peak (liveS s+e.nodes+2) := by
  simp only [Proofs.DynamicOwnedControl.primitive] at pureRun
  obtain ⟨result,ran,_⟩ := Proofs.DynamicResultValid.bind_some _ _ _ pureRun
  simp only [Proofs.DynamicStmt.run] at ran
  obtain ⟨v,value,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ ran
  obtain ⟨x,converted,_⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  have actualValue : e.denote (envOf s) = some v := by
    rw [← Proofs.DynamicRealizes.scalar_denote _ _ _ s real.data e scalar]
    exact value
  exact declare_components s out ty wr e v x scalar actualValue converted actual

theorem check_owned_components (st next : Proofs.DynamicOwnedState.State) (s out : NState)
    (real : Proofs.DynamicOwnedState.Realizes st s) (e : NExpr) (scalar : e.scalarOnly = true)
    (pureRun : Proofs.DynamicOwnedControl.primitive (.check e) st = some ⟨next,none,false⟩)
    (actual : (NStmt.check e).run s = some ⟨out,none,false⟩) :
    Core s out ∧ out.scalars.peak ≤ max s.scalars.peak (liveS s+e.nodes) := by
  simp only [Proofs.DynamicOwnedControl.primitive] at pureRun
  obtain ⟨result,ran,_⟩ := Proofs.DynamicResultValid.bind_some _ _ _ pureRun
  simp only [Proofs.DynamicStmt.run] at ran
  obtain ⟨v,value,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ ran
  have actualValue : e.denote (envOf s) = some v := by
    rw [← Proofs.DynamicRealizes.scalar_denote _ _ _ s real.data e scalar]
    exact value
  split at rest
  · rename_i nonzero
    exact check_components s out e v scalar actualValue nonzero actual
  · simp at rest

end Proofs.CppScalarComponents
