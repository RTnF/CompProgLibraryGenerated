import Proofs.CppMoveArgumentPeak

namespace Proofs.CppMoveArgumentOuter
open Proofs.CppMoveContext Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.CppMoveArgumentWork Proofs.CppMoveArgumentFacts Proofs.DynamicResultValid

structure Effects (s out : Context) : Prop where
  scalar : s.scalars.peak ≤ out.scalars.peak
  heap : out.objects.heap = s.objects.heap
  outer : out.peak ≤ max s.peak (out.scalars.peak+s.objects.heap.peak)

theorem Effects.refl (s : Context) : Effects s s := ⟨Nat.le_refl _,rfl,Nat.le_max_left _ _⟩

theorem Effects.trans {s middle out : Context} (first : Effects s middle) (second : Effects middle out) : Effects s out := by
  refine ⟨first.scalar.trans second.scalar,second.heap.trans first.heap,?_⟩
  have one := first.outer
  have two := second.outer
  rw [first.heap] at two
  have grows := second.scalar
  clear * - one two grows
  omega

theorem eval_effects (s out : Context) (ty : Ty) (expression : NExpr) (value : Int)
    (pure : expression.scalarOnly = true) (run : evalExpression s ty expression = some (out,value)) : Effects s out := by
  unfold evalExpression at run
  obtain ⟨pair,actual,last⟩ := bind_some _ _ _ run
  rcases pair with ⟨after,result⟩
  have equal := Prod.mk.inj (Option.some.inj last)
  rw [← equal.1]
  obtain ⟨core,lowWork,upWork,storage,lowScalar,upScalar,lowOuter,upOuter⟩ :=
    Proofs.CppNestedEval.eval_scalar expression (project s ty) after result pure actual
  refine ⟨lowScalar,rfl,?_⟩
  rw [storage] at upOuter
  exact upOuter

theorem charge_effects (s : Context) (amount temporaries : Nat) : Effects s (charge s amount temporaries) := by
  exact ⟨Nat.le_max_left _ _,rfl,Nat.le_refl _⟩

theorem resolve_argument_effects (s out : Context) (ty : Ty) (parameter : Proofs.CppVectorBindings.Parameter)
    (argument : NArgument) (saved : SavedArgument) (pure : argumentPure argument)
    (run : resolveArgument s ty parameter argument = some (out,saved)) :
    Effects s out := by
  cases argument with
  | value expression =>
    cases parameter with
    | nested element writable => simp [resolveArgument] at run
    | vector expected writable => simp [resolveArgument] at run
    | scalar expected reference writable =>
      cases reference with
      | true => simp [resolveArgument] at run
      | false =>
        simp only [resolveArgument] at run
        split at run
        · obtain ⟨pair,evaluated,last⟩ := bind_some _ _ _ run
          rcases pair with ⟨next,value⟩
          have equal := Prod.mk.inj (Option.some.inj last)
          rw [← equal.1]
          exact eval_effects s next ty expression value pure evaluated
        · simp at run
  | scalarReference slot =>
    cases parameter with
    | nested element writable => simp [resolveArgument] at run
    | vector expected writable => simp [resolveArgument] at run
    | scalar expected reference writable =>
      cases reference with
      | false => simp [resolveArgument] at run
      | true =>
        simp only [resolveArgument] at run
        obtain ⟨argument,found,last⟩ := bind_some _ _ _ run
        have equal := Prod.mk.inj (Option.some.inj last)
        rw [← equal.1]
        exact charge_effects s 1 1
  | vectorReference slot =>
    cases parameter with
    | nested element writable => simp [resolveArgument] at run
    | scalar expected reference writable => simp [resolveArgument] at run
    | vector expected writable =>
      simp only [resolveArgument] at run
      split at run
      · obtain ⟨argument,found,last⟩ := bind_some _ _ _ run
        have equal := Prod.mk.inj (Option.some.inj last)
        rw [← equal.1]
        exact charge_effects s 1 1
      · simp at run

theorem resolve_arguments_effects (s out : Context) (ty : Ty) (parameters : List Proofs.CppVectorBindings.Parameter)
    (arguments : List NArgument) (saved : List SavedArgument) (pure : ∀ argument ∈ arguments, argumentPure argument)
    (run : resolveArguments s ty parameters arguments = some (out,saved)) : Effects s out := by
  induction parameters generalizing s out arguments saved with
  | nil =>
    cases arguments with
    | nil =>
      have equal := Prod.mk.inj (Option.some.inj run)
      rw [← equal.1]
      exact Effects.refl s
    | cons argument tail => simp [resolveArguments] at run
  | cons parameter parameters ih =>
    cases arguments with
    | nil => simp [resolveArguments] at run
    | cons argument arguments =>
      unfold resolveArguments at run
      obtain ⟨pair,first,rest⟩ := bind_some _ _ _ run
      rcases pair with ⟨next,head⟩
      obtain ⟨pair,tail,last⟩ := bind_some _ _ _ rest
      rcases pair with ⟨final,savedTail⟩
      have equal := Prod.mk.inj (Option.some.inj last)
      rw [← equal.1]
      have one := resolve_argument_effects s next ty parameter argument head (pure _ (by simp)) first
      have two := ih next final arguments savedTail (fun arg member => pure arg (by simp [member])) tail
      exact one.trans two

theorem bind_saved_effects (s out : Context) (argument : SavedArgument) (actual : bindSaved s argument = some out) : Effects s out := by
  have counters := bindSaved_peak s out argument actual
  refine ⟨?_,(bindSaved_effects s out argument actual).1,Nat.le_of_eq counters.2⟩
  rw [counters.1]
  exact Nat.le_max_left _ _

theorem bind_all_effects (s out : Context) (arguments : List SavedArgument)
    (actual : bindSavedAll s arguments = some out) : Effects s out := by
  induction arguments generalizing s with
  | nil =>
    have same := Option.some.inj actual
    subst out
    exact Effects.refl s
  | cons argument tail ih =>
    unfold bindSavedAll at actual
    obtain ⟨next,first,rest⟩ := bind_some _ _ _ actual
    exact (bind_saved_effects s next argument first).trans (ih next rest)

theorem prepare_base_effects (s : Context) (count : Nat) : Effects s (prepareBase s count) := by
  exact ⟨Nat.le_max_left _ _,rfl,Nat.le_refl _⟩

theorem prepare_saved_effects (s out : Context) (arguments : List SavedArgument)
    (actual : prepareSaved s arguments = some out) : Effects s out :=
  (prepare_base_effects s arguments.length).trans (bind_all_effects _ out arguments actual)

theorem prepare_effects (s out : Context) (ty : Ty) (parameters : List Proofs.CppVectorBindings.Parameter)
    (arguments : List NArgument) (pure : ∀ argument ∈ arguments, argumentPure argument)
    (actual : prepareArguments s ty parameters arguments = some out) : Effects s out := by
  unfold prepareArguments at actual
  obtain ⟨pair,resolved,prepared⟩ := bind_some _ _ _ actual
  rcases pair with ⟨last,saved⟩
  exact (resolve_arguments_effects s last ty parameters arguments saved pure resolved).trans
    (prepare_saved_effects last out saved prepared)

end Proofs.CppMoveArgumentOuter
