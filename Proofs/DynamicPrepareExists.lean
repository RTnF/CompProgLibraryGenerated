import Proofs.DynamicBindExists

namespace Proofs.DynamicPrepareExists
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppRowsFrame Proofs.CppRootModel
open Proofs.MultiVecDynamic Proofs.DynamicExpr Proofs.DynamicRealizes Proofs.DynamicFamilyInit Proofs.DynamicBoundArguments

-- Pure argument success now constructs the actual prepare result. Scalar
-- addresses stay in the caller prefix while value bindings append cells.
theorem prepare (params : List Parameter) (st : DynamicStmt.State) (caller : NState)
    (real : Realizes params st.locals st.contents caller)
    (parameters : List Proofs.CppVectorBindings.Parameter) (arguments : List NArgument) (rs : List Resolved)
    (pure : DynamicArguments.resolveAll params st parameters arguments = some rs) :
    ∃ callee, CppNestedCall.prepare caller parameters arguments = some callee ∧
      Realizes (describe caller.frame.rootWritable 0 rs) (snapshot callee) st.contents callee ∧
      callee.frame.state = caller.frame.state ∧ callee.frame.rootWritable = caller.frame.rootWritable ∧
      callee.scope = caller.scope+1 ∧ ∃ extra, callee.scalars.memory = caller.scalars.memory ++ extra := by
  obtain ⟨h,m,family,erased⟩ := real.heap
  obtain ⟨last,resolved,good,ext,lastFamily,compatible,lastReal⟩ :=
    DynamicResolve.all_sound params st h m caller family real parameters arguments rs pure
  have bounded := DynamicBoundArguments.all params st h m caller family real parameters arguments rs pure
  let start := DynamicPrepare.initial caller last parameters
  have startFamily := DynamicPrepare.initial_family caller last parameters lastFamily
  have flags : start.frame.rootWritable = caller.frame.rootWritable := ext.2.1
  have memory : last.scalars.memory = caller.scalars.memory := good.2.2.2.2.1
  have startMemory : ∃ extra, start.scalars.memory = caller.scalars.memory ++ extra := by
    refine ⟨List.replicate ((last.release caller).scalars.bindings.length+(last.release caller).frame.bindings.length) ⟨⟨1,false,true⟩,0⟩,?_⟩
    change last.scalars.memory ++ _ = caller.scalars.memory ++ _
    rw [memory]
  have startBound : ∀ r ∈ rs, Boundable h start r := by
    intro r member
    exact transport (bounded r member) flags startMemory ext.1
  obtain ⟨callee,bound,_,_,_,tail,tailMemory⟩ := DynamicBindExists.all_exists startFamily rs startBound
  have prepared : CppNestedCall.prepare caller parameters arguments = some callee := by
    rw [DynamicPrepare.prepare_eq caller last parameters arguments rs family.valid resolved]
    exact bound
  obtain ⟨_,_,_,_,_,_,_,calleeReal,state,rights,scope⟩ :=
    DynamicCallPrepare.sound params st caller callee real parameters arguments rs pure prepared
  obtain ⟨reserved,startMemory⟩ := startMemory
  refine ⟨callee,prepared,calleeReal,state,rights,scope,reserved ++ tail,?_⟩
  rw [tailMemory,startMemory,List.append_assoc]

end Proofs.DynamicPrepareExists
