import Proofs.DynamicScalarSteps

namespace Proofs.DynamicScalarSound
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedSim
open Proofs.MultiVecDynamic Proofs.DynamicContents Proofs.DynamicExpr Proofs.DynamicRealizes
open Proofs.DynamicExprCertified Proofs.DynamicExprDerive Proofs.DynamicScalarSteps

def ScalarReady (params : List Parameter) (st : DynamicStmt.State) : NStmt → Prop
  | .skip => True
  | .declare _ _ e | .assign _ _ e | .ret e | .check e => Ready params st.locals st.contents e
  | _ => False

def workBound : NStmt → Nat
  | .declare _ _ e | .assign _ _ e | .ret e | .check e => 2*e.nodes+1
  | _ => 0

def tempBound : NStmt → Nat
  | .declare _ _ e => 2*e.nodes+2
  | .assign _ _ e | .ret e | .check e => 2*e.nodes
  | _ => 0

structure Matches (params : List Parameter) (pure : DynamicStmt.Step) (actual : NStep) : Prop where
  state : Realizes params pure.state.locals pure.state.contents actual.state
  returned : actual.returned = pure.returned.map Ret.scalar
  breaking : actual.breaking = false

-- The successful pure step supplies all value and conversion premises. Only
-- the expression's lookup certificates and the initial Realizes remain inputs.
theorem sound (params : List Parameter) (st : DynamicStmt.State) (s : NState)
    (realizes : Realizes params st.locals st.contents s) (stmt : NStmt)
    (ready : ScalarReady params st stmt) (result : DynamicStmt.Step)
    (run : DynamicStmt.run params stmt st = some result) :
    ∃ actual, stmt.run s = some actual ∧ Matches params result actual ∧
      actual.state.work ≤ s.work+workBound stmt ∧ actual.state.peak ≤ max s.peak
        (max s.scalars.peak (liveS s+tempBound stmt)+s.frame.state.storage.peak) := by
  cases stmt with
  | skip =>
    simp only [DynamicStmt.run,Option.some.injEq] at run
    subst result
    exact ⟨⟨s,none,false⟩,rfl,⟨realizes,rfl,rfl⟩,by simp [workBound],Nat.le_max_left _ _⟩
  | declare ty writable e =>
    cases value : denote params st.locals st.contents e with
    | none => simp [DynamicStmt.run,value] at run
    | some v =>
      cases converted : ty.convert v with
      | none => simp [DynamicStmt.run,value,converted] at run
      | some v' =>
        simp only [DynamicStmt.run,value,Bind.bind,Option.bind,converted,Option.some.injEq] at run
        subst result
        obtain ⟨_,t,extra,ev⟩ := DynamicExprCertified.sound (derive ready v value) s realizes
        obtain ⟨out,ran,after,work,peak⟩ := declaration params st.locals st.contents s t realizes e v v' extra _ _ ev ty writable converted
        exact ⟨⟨out,none,false⟩,ran,⟨after,rfl,rfl⟩,work,by simpa [tempBound,Nat.add_assoc] using peak⟩
  | assign slot ty e =>
    cases value : denote params st.locals st.contents e with
    | none => simp [DynamicStmt.run,value] at run
    | some v =>
      cases found : DynamicStmt.scalarCell st.locals slot ty with
      | none => simp [DynamicStmt.run,value,found] at run
      | some pair =>
        obtain ⟨binding,cell⟩ := pair
        cases writable : binding.writable with
        | false => simp [DynamicStmt.run,value,found,writable] at run
        | true =>
          cases converted : ty.convert v with
          | none => simp [DynamicStmt.run,value,found,writable,converted] at run
          | some v' =>
            simp only [DynamicStmt.run,value,Bind.bind,Option.bind,found,writable,if_true,converted,Option.some.injEq] at run
            subst result
            obtain ⟨_,t,extra,ev⟩ := DynamicExprCertified.sound (derive ready v value) s realizes
            obtain ⟨out,ran,after,work,peak⟩ := assignment params st.locals st.contents s t realizes e v v' extra _ _ ev slot ty binding cell found writable converted
            exact ⟨⟨out,none,false⟩,ran,⟨after,rfl,rfl⟩,work,peak⟩
  | ret e =>
    cases value : denote params st.locals st.contents e with
    | none => simp [DynamicStmt.run,value] at run
    | some v =>
      simp only [DynamicStmt.run,value,Bind.bind,Option.bind,Option.some.injEq] at run
      subst result
      obtain ⟨_,t,extra,ev⟩ := DynamicExprCertified.sound (derive ready v value) s realizes
      obtain ⟨after,_,work,peak⟩ := ev_preserves params st.locals st.contents s t realizes e v extra _ _ ev
      exact ⟨⟨(t.release s).charge 1 0,some (.scalar v),false⟩,
        by simp [NStmt.run,ev.1],⟨after,rfl,rfl⟩,work,peak⟩
  | check e =>
    cases value : denote params st.locals st.contents e with
    | none => simp [DynamicStmt.run,value] at run
    | some v =>
      by_cases nonzero : v ≠ 0
      · simp only [DynamicStmt.run,value,Bind.bind,Option.bind,if_pos nonzero,Option.some.injEq] at run
        subst result
        obtain ⟨_,t,extra,ev⟩ := DynamicExprCertified.sound (derive ready v value) s realizes
        obtain ⟨after,_,work,peak⟩ := ev_preserves params st.locals st.contents s t realizes e v extra _ _ ev
        exact ⟨⟨(t.release s).charge 1 0,none,false⟩,check_run e s t v ev.1 nonzero,⟨after,rfl,rfl⟩,work,peak⟩
      · simp [DynamicStmt.run,value,nonzero] at run
  | _ => simp [ScalarReady] at ready

end Proofs.DynamicScalarSound
