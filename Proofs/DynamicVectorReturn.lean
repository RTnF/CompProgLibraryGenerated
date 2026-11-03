import Proofs.DynamicVectorScope

namespace Proofs.DynamicVectorReturn
open Proofs.CppNestedProgram Proofs.DynamicExpr Proofs.DynamicOwnedState Proofs.MultiVecDynamic

-- Match the generator's owned-local move profile. A returned row, foreign
-- scope root or const local is outside this profile and fails explicitly.
def run (st : State) (slot : Nat) : Option Ret := do
  let p ← DynamicStmt.parameter st.params st.core.locals slot
  let view ← st.core.contents p.owner
  if p.writable = true ∧ p.maximum = true ∧ p.scope = st.scope ∧
      view.scope = p.scope ∧ view.element = p.element then
    some (.vector p.owner p.element)
  else none

theorem sound (st : State) (s : NState) (real : Realizes st s) (slot : Nat) (value : Ret)
    (pureRun : run st slot = some value) :
    (NStmt.retVector slot).run s = some ⟨s.charge 1 0,some value,false⟩ ∧
      Realizes st (s.charge 1 0) ∧ (s.charge 1 0).work = s.work+1 := by
  obtain ⟨p,parameter,viewRest⟩ := DynamicResultValid.bind_some _ _ _ pureRun
  obtain ⟨view,_,returnRest⟩ := DynamicResultValid.bind_some _ _ _ viewRest
  split at returnRest
  · have same := Option.some.inj returnRest
    subst value
    obtain ⟨location,selected⟩ := DynamicAppendSound.parameter_found st.params st.core.locals slot p parameter
    obtain ⟨heap,m,family,he⟩ := real.data.heap
    have vectorSlot := DynamicSizeSound.vector_slot st.params st.core.locals st.core.contents s real.data slot p.slot location
    have binding := family.bindings p (List.mem_of_find?_eq_some selected)
    refine ⟨?_,⟨⟨real.data.locals,real.data.heap⟩,real.owner,real.binding,real.scopedState⟩,?_⟩
    · simp [NStmt.run,vectorSlot,binding,Parameter.binding]
    · simp [NState.work,NState.charge,NState.observe,Proofs.CppState.State.observe,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  · contradiction

end Proofs.DynamicVectorReturn
