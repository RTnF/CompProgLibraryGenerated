import Proofs.DynamicOwnedLayout

namespace Proofs.DynamicOwnedState
open Proofs.CppScalar Proofs.CppVectorOwnership Proofs.CppNestedProgram Proofs.MultiVecDynamic
open Proofs.DynamicExpr Proofs.DynamicContents

-- Allocation cursors count all objects, including tombstones and roots not
-- registered in the logical heap. Reference indices likewise allow gaps.
structure State where
  core : DynamicStmt.State
  params : List Parameter
  nextOwner : Nat
  nextBinding : Nat
  scope : Nat

structure Realizes (st : State) (s : NState) : Prop where
  data : DynamicRealizes.Realizes st.params st.core.locals st.core.contents s
  owner : s.frame.state.storage.objects.length = st.nextOwner
  binding : s.frame.bindings.length = st.nextBinding
  scopedState : s.scope = st.scope

theorem of_real (params : List Parameter) (core : DynamicStmt.State) (s : NState)
    (real : DynamicRealizes.Realizes params core.locals core.contents s) :
    Realizes ⟨core,params,s.frame.state.storage.objects.length,s.frame.bindings.length,s.scope⟩ s := ⟨real,rfl,rfl,rfl⟩

def newParameter (st : State) (element : Element) (wr : Bool) : Parameter :=
  ⟨st.nextBinding,st.nextOwner,element,st.scope,wr,wr⟩

def allocated (st : State) (element : Element) (wr : Bool) (view : Contents) (objects : Nat) : State :=
  ⟨⟨DynamicConstructCore.appended st.core.locals st.nextBinding,putContents st.core.contents st.nextOwner view⟩,
    st.params ++ [newParameter st element wr],st.nextOwner+objects,st.nextBinding+1,st.scope⟩

-- The successful constructor profile is explicit; other statement forms
-- are handled by the existing pure interpreter until ownership is composed.
def runConstruct (stmt : NStmt) (st : State) : Option State := match stmt with
  | .declareVector ty wr =>
      if Proofs.CppVectorBindings.supported ty then
        some (allocated st (.integer ty) wr (.flat ty st.scope []) 1)
      else none
  | .constructRows ty wr count => do
      let n ← denote st.params st.core.locals st.core.contents count
      if 0 ≤ n ∧ Proofs.CppVectorBindings.supported ty ∧ n.toNat ≤ Proofs.CppNestedConstruct.rowLimit then
        some (allocated st (.vector (.integer ty)) wr (.rows ty st.scope (List.replicate n.toNat [])) (1+n.toNat))
      else none
  | .fillVector ty wr count value => do
      let n ← denote st.params st.core.locals st.core.contents count
      let x ← denote st.params st.core.locals st.core.contents value
      if 0 ≤ n ∧ Proofs.CppVectorBindings.supported ty ∧ n.toNat ≤ Proofs.CppVectorBindings.sizeLimit ty ∧ ty.valid x = true then
        some (allocated st (.integer ty) wr (.flat ty st.scope (List.replicate n.toNat x)) 1)
      else none
  | _ => none

end Proofs.DynamicOwnedState
