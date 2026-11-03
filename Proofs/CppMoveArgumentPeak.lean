import Proofs.CppMoveArgumentWork

namespace Proofs.CppMoveArgumentPeak
open Proofs.CppMoveContext Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.CppMoveArgumentWork Proofs.CppMoveArgumentFacts Proofs.DynamicResultValid

theorem scalar_live_stable (s out : Context) (stable : Stable s out) : scalarLive out = scalarLive s := by
  simp only [scalarLive,stable.memory,stable.bindings,stable.baseline]

theorem eval_peak (s out : Context) (ty : Ty) (expression : NExpr) (value : Int)
    (pure : expression.scalarOnly = true) (run : evalExpression s ty expression = some (out,value)) :
    out.scalars.peak ≤ max s.scalars.peak (scalarLive s+expression.nodes) := by
  unfold evalExpression at run
  obtain ⟨pair,actual,last⟩ := bind_some _ _ _ run
  rcases pair with ⟨after,result⟩
  have equal := Prod.mk.inj (Option.some.inj last)
  rw [← equal.1]
  have good := Proofs.CppNestedEval.eval_scalar expression (project s ty) after result pure actual
  have upper := good.2.2.2.2.2.1
  exact upper

theorem charge_peak (s : Context) (amount temporaries : Nat) :
    (charge s amount temporaries).scalars.peak = max s.scalars.peak (scalarLive s+temporaries) := rfl

theorem resolve_argument_peak (s out : Context) (ty : Ty) (parameter : Proofs.CppVectorBindings.Parameter)
    (argument : NArgument) (saved : SavedArgument) (pure : argumentPure argument)
    (run : resolveArgument s ty parameter argument = some (out,saved)) :
    out.scalars.peak ≤ max s.scalars.peak (scalarLive s+argumentWork argument) := by
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
          exact eval_peak s next ty expression value pure evaluated
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
        rw [charge_peak]
        exact Nat.le_refl _
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
        rw [charge_peak]
        exact Nat.le_refl _
      · simp at run

theorem resolve_arguments_peak (s out : Context) (ty : Ty) (parameters : List Proofs.CppVectorBindings.Parameter)
    (arguments : List NArgument) (saved : List SavedArgument) (pure : ∀ argument ∈ arguments, argumentPure argument)
    (run : resolveArguments s ty parameters arguments = some (out,saved)) :
    out.scalars.peak ≤ max s.scalars.peak (scalarLive s+argumentsWork arguments) := by
  induction parameters generalizing s out arguments saved with
  | nil =>
    cases arguments with
    | nil =>
      have equal := Prod.mk.inj (Option.some.inj run)
      rw [← equal.1]
      exact Nat.le_max_left _ _
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
      have one := resolve_argument_peak s next ty parameter argument head (pure _ (by simp)) first
      have two := ih next final arguments savedTail (fun arg member => pure arg (by simp [member])) tail
      have stable := resolveArgument_stable s next ty parameter argument head first
      rw [scalar_live_stable s next stable] at two
      have sum : argumentsWork (argument::arguments) = argumentWork argument+argumentsWork arguments := by
        simp [argumentsWork]
      rw [sum]
      clear * - one two
      omega

-- No assumption that the baseline lies inside the original caller memory.
theorem prepare_live_raw (caller out : Context) (arguments : List SavedArgument)
    (prepared : prepareSaved caller arguments = some out) :
    scalarLive out ≤ (caller.scalars.memory.length+caller.slots.length+2*arguments.length-caller.scalars.baseMemory)+2*arguments.length := by
  have resources := prepareSaved_resources caller out arguments prepared
  have footprint := arguments_footprint arguments
  unfold scalarLive
  rw [resources.1,resources.2.1,resources.2.2.2]
  omega

theorem prepare_peak (s out : Context) (ty : Ty) (parameters : List Proofs.CppVectorBindings.Parameter)
    (arguments : List NArgument) (pure : ∀ argument ∈ arguments, argumentPure argument)
    (actual : prepareArguments s ty parameters arguments = some out) :
    out.scalars.peak ≤ max (max s.scalars.peak (scalarLive s+argumentsWork arguments))
      ((s.scalars.memory.length+s.slots.length+2*parameters.length-s.scalars.baseMemory)+2*parameters.length) := by
  unfold prepareArguments at actual
  obtain ⟨pair,resolved,prepared⟩ := bind_some _ _ _ actual
  rcases pair with ⟨last,saved⟩
  have before := resolve_arguments_peak s last ty parameters arguments saved pure resolved
  have bound := (prepareSaved_peak last out saved prepared).1
  have footprint := prepare_live_raw last out saved prepared
  have stable := resolveArguments_stable s last ty parameters arguments saved resolved
  have lengths := resolveArguments_lengths s last ty parameters arguments saved resolved
  rw [stable.memory,stable.slots,stable.baseline,lengths.1] at footprint
  clear * - before bound footprint
  omega

end Proofs.CppMoveArgumentPeak
