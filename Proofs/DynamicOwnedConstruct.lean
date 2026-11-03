import Proofs.DynamicOwnedState

namespace Proofs.DynamicOwnedConstruct
open Proofs.CppScalar Proofs.CppVectorOwnership Proofs.CppNestedProgram Proofs.MultiVecDynamic
open Proofs.CppRootModel Proofs.DynamicExpr Proofs.DynamicContents Proofs.DynamicOwnedState

theorem sound (st : State) (s : NState) (real : Realizes st s) (stmt : NStmt) (final : State)
    (pure : runConstruct stmt st = some final) :
    ∃ out, stmt.run s = some ⟨out,none,false⟩ ∧ Realizes final out := by
  obtain ⟨h,m,family,erased⟩ := real.data.heap
  have before : DynamicRealizes.Realizes st.params st.core.locals (eraseHeap h) s := by rw [erased]; exact real.data
  have descriptor (element : Element) (wr : Bool) : DynamicConstructCore.parameter s element wr = newParameter st element wr := by
    simp only [DynamicConstructCore.parameter,newParameter,real.owner,real.binding,real.scopedState]
  cases stmt with
  | declareVector ty wr =>
    simp only [runConstruct] at pure
    split at pure
    · rename_i supported
      have same := Option.some.inj pure
      subst final
      obtain ⟨out,ran,_,matched,scope,_⟩ := DynamicDeclareOwned.sound st.params h m s family ty wr supported
      obtain ⟨bindingCount,ownerCount,snapshotOut⟩ := DynamicOwnedLayout.empty s ty wr ⟨out,none,false⟩ ran
      have parameterEq : DynamicDeclareOwned.parameter s ty wr = newParameter st (.integer ty) wr := by
        simp only [DynamicDeclareOwned.parameter,newParameter,real.owner,real.binding,real.scopedState]
      rw [snapshotOut,real.data.locals] at matched
      simp only [parameterEq,real.owner,real.binding,real.scopedState,erased] at matched
      refine ⟨out,ran,⟨matched,?_,?_,scope.trans real.scopedState⟩⟩
      · simpa only [allocated,real.owner] using ownerCount
      · simpa only [allocated,real.binding] using bindingCount
    · contradiction
  | constructRows ty wr count =>
    cases value : denote st.params st.core.locals st.core.contents count with
    | none => simp [runConstruct,value] at pure
    | some n =>
      simp only [runConstruct,value,Bind.bind,Option.bind] at pure
      split at pure
      · rename_i good
        have same := Option.some.inj pure
        subst final
        obtain ⟨out,ran,_,matched,scope,_,_,bindingCount,ownerCount⟩ := DynamicConstructRows.sound_full st.params h m st.core.locals s family before ty wr count n (by rw [erased]; exact value) good.1 good.2.1 good.2.2
        simp only [descriptor,real.owner,real.binding,real.scopedState,erased] at matched
        refine ⟨out,ran,⟨matched,?_,?_,scope.trans real.scopedState⟩⟩
        · simpa only [allocated,real.owner,Nat.add_assoc] using ownerCount
        · simpa only [allocated,real.binding] using bindingCount
      · contradiction
  | fillVector ty wr count value =>
    cases nval : denote st.params st.core.locals st.core.contents count with
    | none => simp [runConstruct,nval] at pure
    | some n =>
      cases xval : denote st.params st.core.locals st.core.contents value with
      | none => simp [runConstruct,nval,xval] at pure
      | some x =>
        simp only [runConstruct,nval,xval,Bind.bind,Option.bind] at pure
        split at pure
        · rename_i good
          have same := Option.some.inj pure
          subst final
          obtain ⟨out,ran,_,matched,scope,_,_,bindingCount,ownerCount⟩ := DynamicConstructFill.sound_full st.params h m st.core.locals s family before ty wr count value n x (by rw [erased]; exact nval) (by rw [erased]; exact xval) good.1 good.2.1 good.2.2.1 good.2.2.2
          simp only [descriptor,real.owner,real.binding,real.scopedState,erased] at matched
          refine ⟨out,ran,⟨matched,?_,?_,scope.trans real.scopedState⟩⟩
          · simpa only [allocated,real.owner] using ownerCount
          · simpa only [allocated,real.binding] using bindingCount
        · contradiction
  | _ => simp [runConstruct] at pure

end Proofs.DynamicOwnedConstruct
