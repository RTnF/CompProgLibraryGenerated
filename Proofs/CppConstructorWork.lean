import Proofs.DynamicOwnedControl
import Proofs.CppConstructorFinish
import Proofs.CppConstructionRetire

namespace Proofs.CppConstructorWork
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings Proofs.CppNestedVectorStore
open Proofs.CppVectorOwnership Proofs.CppNestedConstruct Proofs.CppRootModel
open Proofs.DynamicExpr Proofs.DynamicContents Proofs.DynamicOwnedState Proofs.DynamicResultValid
open Proofs.CppConstructorFinish

theorem scalar_work (st next : Proofs.DynamicOwnedState.State) (s t : NState) (real : Realizes st s) (stmt : NStmt)
    (form : Proofs.DynamicStmtAuto.ScalarForm stmt)
    (pureRun : Proofs.DynamicOwnedControl.primitive stmt st = some ⟨next,none,false⟩)
    (actual : stmt.run s = some ⟨t,none,false⟩) : t.work ≤ s.work + Proofs.DynamicScalarSound.workBound stmt := by
  cases stmt <;> try {simp [Proofs.DynamicStmtAuto.ScalarForm] at form}
  all_goals
    simp only [Proofs.DynamicOwnedControl.primitive] at pureRun
    obtain ⟨result,scalar,_⟩ := bind_some _ _ _ pureRun
    obtain ⟨out,ran,matched,ret,br,work,peak⟩ := Proofs.DynamicOwnedScalar.sound st s real _ form result scalar
    have same := Option.some.inj (ran.symm.trans actual)
    rw [same] at work
    exact work

theorem fill_work (st : Proofs.DynamicOwnedState.State) (s t : NState) (real : Realizes st s)
    (ty : Ty) (wr : Bool) (count value : NExpr) (n x : Int)
    (countPure : denote st.params st.core.locals st.core.contents count = some n)
    (valuePure : denote st.params st.core.locals st.core.contents value = some x)
    (nonnegative : 0 ≤ n) (supported : Proofs.CppVectorBindings.supported ty)
    (limit : n.toNat ≤ Proofs.CppVectorBindings.sizeLimit ty) (accepted : ty.valid x = true)
    (actual : (NStmt.fillVector ty wr count value).run s = some ⟨t,none,false⟩) :
    t.work ≤ s.work+2*count.nodes+2*value.nodes+n.toNat+4 := by
  obtain ⟨h,m,family,erased⟩ := real.data.heap
  have before : Proofs.DynamicRealizes.Realizes st.params st.core.locals (eraseHeap h) s := by rw [erased]; exact real.data
  obtain ⟨out,ran,_,_,_,work,_⟩ := Proofs.DynamicConstructFill.sound_full st.params h m st.core.locals s family before
    ty wr count value n x (by rw [erased]; exact countPure) (by rw [erased]; exact valuePure)
    nonnegative supported limit accepted
  have same := congrArg NStep.state (Option.some.inj (ran.symm.trans actual))
  change out = t at same
  rwa [same] at work

theorem empty_work (st : Proofs.DynamicOwnedState.State) (s t : NState) (real : Realizes st s)
    (ty : Ty) (wr : Bool) (supported : Proofs.CppVectorBindings.supported ty)
    (actual : (NStmt.declareVector ty wr).run s = some ⟨t,none,false⟩) : t.work = s.work+2 := by
  obtain ⟨h,m,family,erased⟩ := real.data.heap
  obtain ⟨out,ran,_,_,_,work⟩ := Proofs.DynamicDeclareOwned.sound st.params h m s family ty wr supported
  have same := congrArg NStep.state (Option.some.inj (ran.symm.trans actual))
  change out = t at same
  rwa [same] at work

theorem declared_transferred (f : Forest) (ty : Ty) (fromScope toScope : Nat) :
    (f.declareRoot ty fromScope).transferred f.objects.length toScope (flatTag ty fromScope) =
      f.declareRoot ty toScope := by
  simp [Forest.declareRoot,Forest.transferred,flatTag]

theorem declared_scope_bound (f : Forest) (ty : Ty) (scope : Nat)
    (strict : ∀ owner k, f.context owner = some k → k ≤ scope) :
    ∀ owner k, (f.declareRoot ty scope).context owner = some k → k ≤ scope := by
  intro owner k found
  have inside : owner < (f.declareRoot ty scope).objects.length := by
    by_cases inside : owner < (f.declareRoot ty scope).objects.length
    · exact inside
    have missing := lookup_past_end (f.declareRoot ty scope) owner (by omega)
    have rootMissing : (f.declareRoot ty scope).rootOwner owner = none := by rw [Forest.rootOwner]; simp [missing]
    simp [Forest.context,rootMissing] at found
  have length : (f.declareRoot ty scope).objects.length = f.objects.length+1 := by simp [Forest.declareRoot]
  by_cases old : owner < f.objects.length
  · have same := Proofs.CppConstructionRetire.context_prefix f (f.declareRoot ty scope) f.objects.length
      (fun i bound => declareRoot_old f ty scope i bound) owner old
    rw [same] at found
    exact strict owner k found
  · have same : owner = f.objects.length := by omega
    subst owner
    have root := root_runs (f.declareRoot ty scope) f.objects.length (flatTag ty scope) (declareRoot_new f ty scope) rfl
    simp [Forest.context,root,declareRoot_new,flatTag] at found
    omega

theorem finish_scalar_work (caller callee out : NState) (vslot : Nat) (element : Element)
    (fields : List ScalarField) (values : List ScalarValue) (object : ObjectRef)
    (captured : captureAll callee fields = some values)
    (actual : Proofs.CppConstructorFinish.finish caller callee vslot element fields = some (out,object)) :
    out.scalars.work = callee.scalars.work+values.length+1 := by
  unfold Proofs.CppConstructorFinish.finish at actual
  split at actual
  · obtain ⟨index,_,rest⟩ := bind_some _ _ _ actual
    obtain ⟨binding,_,rest⟩ := bind_some _ _ _ rest
    split at rest
    · obtain ⟨actualValues,found,rest⟩ := bind_some _ _ _ rest
      have valuesEq : actualValues = values := Option.some.inj (found.symm.trans captured)
      subst actualValues
      obtain ⟨moved,_,rest⟩ := bind_some _ _ _ rest
      obtain ⟨retired,_,same⟩ := bind_some _ _ _ rest
      have eq := (Prod.mk.inj (Option.some.inj same)).1
      subst out
      rfl
    · simp at rest
  · simp at actual

end Proofs.CppConstructorWork
