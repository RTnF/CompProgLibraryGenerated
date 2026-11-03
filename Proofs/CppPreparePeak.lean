import Proofs.CppEvalPeak
import Proofs.CppCallFrame

namespace Proofs.CppPreparePeak
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppNestedVectorBindings
open Proofs.CppVectorOwnership Proofs.DynamicResultValid Proofs.CppPeakComponents

theorem scalar_bind_peak (s t : Proofs.CppState.State) (p : Proofs.CppState.Parameter) (arg : Proofs.CppState.Argument)
    (actual : Proofs.CppState.bindArgument s p arg = some t) : s.peak ≤ t.peak := by
  cases arg with
  | value x =>
    unfold Proofs.CppState.bindArgument at actual
    dsimp only at actual
    split at actual
    · simp at actual
    · have eq := Option.some.inj actual
      rw [← eq]
      exact Nat.le_max_left _ _
  | reference address =>
    unfold Proofs.CppState.bindArgument at actual
    obtain ⟨cell,_,rest⟩ := bind_some _ _ _ actual
    try dsimp only at rest
    split at rest
    · simp at rest
    · have eq := Option.some.inj rest
      rw [← eq]
      exact Nat.le_max_left _ _

theorem resolve_peak (s t : NState) (p : Proofs.CppVectorBindings.Parameter) (arg : NArgument) (r : Resolved)
    (actual : resolve s p arg = some (t,r)) : Grows s t := by
  cases p with
  | scalar ty address wr =>
    cases address with
    | false =>
      cases arg with
      | value e =>
        unfold resolve at actual
        try dsimp only at actual
        split at actual
        · obtain ⟨⟨q,v⟩,ev,rest⟩ := bind_some _ _ _ actual
          have eq := congrArg Prod.fst (Option.some.inj rest)
          change q = t at eq
          subst t
          exact Proofs.CppEvalPeak.expression_peak e s q v ev
        · simp at actual
      | _ => simp [resolve] at actual
    | true =>
      cases arg with
      | scalarReference slot =>
        unfold resolve at actual
        obtain ⟨⟨binding,cell⟩,_,rest⟩ := bind_some _ _ _ actual
        try dsimp only at rest
        split at rest
        · have eq := congrArg Prod.fst (Option.some.inj rest)
          change _ = t at eq
          subst t
          exact charge s 1 1
        · simp at rest
      | _ => simp [resolve] at actual
  | vector ty wr | nested ty wr =>
    cases arg with
    | vectorReference slot =>
      unfold resolve at actual
      obtain ⟨index,_,rest⟩ := bind_some _ _ _ actual
      obtain ⟨binding,_,rest⟩ := bind_some _ _ _ rest
      obtain ⟨pair,_,rest⟩ := bind_some _ _ _ rest
      try dsimp only at rest
      cases header : binding.header with
      | child address =>
        simp only [header] at rest
        first
        | contradiction
        | split at rest
          · have eq := congrArg Prod.fst (Option.some.inj rest)
            change _ = t at eq
            subst t
            exact charge s 1 1
          · simp at rest
      | root scope =>
        simp only [header] at rest
        split at rest
        · have eq := congrArg Prod.fst (Option.some.inj rest)
          change _ = t at eq
          subst t
          exact charge s 1 1
        · simp at rest
    | _ => simp [resolve] at actual

theorem resolve_all_peak (s t : NState) (ps : List Proofs.CppVectorBindings.Parameter)
    (args : List NArgument) (rs : List Resolved) (actual : resolveAll s ps args = some (t,rs)) : Grows s t := by
  induction ps generalizing s args t rs with
  | nil =>
    cases args with
    | nil =>
      have eq := congrArg Prod.fst (Option.some.inj actual)
      change s = t at eq
      subst t
      exact Grows.refl s
    | cons a args => simp [resolveAll] at actual
  | cons p ps ih =>
    cases args with
    | nil => simp [resolveAll] at actual
    | cons a args =>
      unfold resolveAll at actual
      obtain ⟨⟨q,r⟩,resolved,rest⟩ := bind_some _ _ _ actual
      obtain ⟨⟨u,us⟩,tail,rest⟩ := bind_some _ _ _ rest
      have eq := congrArg Prod.fst (Option.some.inj rest)
      change u = t at eq
      subst t
      exact (resolve_peak s q p a r resolved).trans (ih q u args us tail)

theorem bind_one_peak (s t : NState) (r : Resolved) (actual : bindOne s r = some t) : Grows s t := by
  cases r with
  | scalar ty wr value | scalarAddress ty address wr =>
    unfold bindOne at actual
    obtain ⟨scalars,bound,rest⟩ := bind_some _ _ _ actual
    have peak := scalar_bind_peak s.scalars scalars _ _ bound
    have eq := Option.some.inj rest
    subst t
    exact ⟨peak,Nat.le_refl _,Nat.le_refl _⟩
  | vectorChild owner address ty wr =>
    unfold bindOne at actual
    obtain ⟨pair,_,rest⟩ := bind_some _ _ _ actual
    have eq := Option.some.inj rest
    subst t
    exact ⟨Nat.le_refl _,Nat.le_refl _,Nat.le_refl _⟩
  | vector owner scope ty wr | nestedRoot owner scope ty wr =>
    unfold bindOne at actual
    obtain ⟨⟨frame,index⟩,ran,rest⟩ := bind_some _ _ _ actual
    have same := Proofs.CppCallFrame.root_frame s.frame frame owner scope _ wr index ran
    have eq := Option.some.inj rest
    subst t
    refine ⟨Nat.le_refl _,?_,Nat.le_refl _⟩
    change s.frame.state.storage.peak ≤ frame.state.storage.peak
    rw [same.1]
    exact Nat.le_refl _

theorem bind_all_peak (s t : NState) (rs : List Resolved) (actual : bindAll s rs = some t) : Grows s t := by
  induction rs generalizing s t with
  | nil => have eq := Option.some.inj actual; subst t; exact Grows.refl _
  | cons r rs ih =>
    unfold bindAll at actual
    obtain ⟨q,head,tail⟩ := bind_some _ _ _ actual
    exact (bind_one_peak s q r head).trans (ih q t tail)

theorem prepare_peak (s t : NState) (ps : List Proofs.CppVectorBindings.Parameter) (args : List NArgument)
    (actual : prepare s ps args = some t) : Grows s t := by
  unfold prepare at actual
  split at actual
  · obtain ⟨⟨q,rs⟩,resolved,rest⟩ := bind_some _ _ _ actual
    dsimp only at rest
    let released := q.release s
    let cells : Proofs.CppState.State := {released.scalars with
      memory := released.scalars.memory++List.replicate
        (released.scalars.bindings.length+released.frame.bindings.length) ⟨⟨1,false,true⟩,0⟩
      bindings := []
      work := released.scalars.work+1+ps.length}
    let initial : NState := ⟨cells,{released.frame with bindings := []},[],s.scope+1,released.peak⟩
    change bindAll initial.observe rs = some t at rest
    have raw : Grows released initial := uncharged _ _ (Nat.le_refl _) (Nat.le_refl _) rfl
    exact (resolve_all_peak s q ps args rs resolved).trans
      ((release q s).trans (raw.trans ((observe initial).trans (bind_all_peak _ t rs rest))))
  · simp at actual

end Proofs.CppPreparePeak
