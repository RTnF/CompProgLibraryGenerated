import Proofs.VecKit

namespace Proofs.VecPrepare
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppNestedVectorBindings
open Proofs.CppVectorOwnership Proofs.CppNestedVectorStore

def IsScalarRes : Resolved → Prop
  | .vector .. | .vectorChild .. => False
  | .nestedRoot .. => False
  | _ => True

theorem bindOne_scalar_frame (s s' : NState) (r : Resolved) (hr : IsScalarRes r) (h : bindOne s r = some s') :
    s'.frame = s.frame := by
  cases r with
  | scalar ty w v =>
    simp only [bindOne, Bind.bind, Option.bind] at h
    cases hb : CppState.bindArgument s.scalars ⟨ty,false,w⟩ (.value v) with
    | none => simp [hb] at h
    | some sc => simp [hb] at h; subst h; rfl
  | vector o sc ty w | vectorChild o sc ty w => exact hr.elim
  | nestedRoot o sc ty w => exact hr.elim
  | scalarAddress ty a w =>
    simp only [bindOne, Bind.bind, Option.bind] at h
    cases hb : CppState.bindArgument s.scalars ⟨ty,true,w⟩ (.reference a) with
    | none => simp [hb] at h
    | some sc => simp [hb] at h; subst h; rfl

theorem bindAll_scalar_frame (rs : List Resolved) (hr : ∀ r ∈ rs, IsScalarRes r) :
    ∀ (s s' : NState), bindAll s rs = some s' → s'.frame = s.frame := by
  induction rs with
  | nil => intro s s' h; simp [bindAll] at h; subst h; rfl
  | cons r rs ih =>
    intro s s' h
    simp only [bindAll, Bind.bind, Option.bind] at h
    cases hb : bindOne s r with
    | none => simp [hb] at h
    | some n =>
      simp only [hb] at h
      rw [ih (fun x hx => hr x (List.mem_cons_of_mem _ hx)) n s' h,
        bindOne_scalar_frame s n r (hr r List.mem_cons_self) hb]

theorem bindOne_vector_frame (s s' : NState) (owner scope : Nat) (ty : Ty) (w : Bool)
    (h : bindOne s (.vector owner scope ty w) = some s') :
    s'.frame = ⟨s.frame.state, s.frame.rootWritable, s.frame.bindings ++ [⟨owner,.integer ty,w,.root scope⟩]⟩ := by
  simp only [bindOne, Bind.bind, Option.bind] at h
  cases hb : s.frame.bindRoot owner (.integer ty) scope w with
  | none => simp [hb] at h
  | some p =>
    obtain ⟨fr, idx⟩ := p
    have hfr : fr = ⟨s.frame.state, s.frame.rootWritable, s.frame.bindings ++ [⟨owner,.integer ty,w,.root scope⟩]⟩ := by
      simp only [Frame.bindRoot, Bind.bind, Option.bind] at hb
      cases ho : s.frame.object owner (.integer ty) with
      | none => simp [ho] at hb
      | some o =>
        cases hm : s.frame.maximum owner with
        | none => simp [ho, hm] at hb
        | some mx =>
          simp only [ho, hm] at hb
          by_cases c : o.2.parent = none ∧ o.2.scope = some scope ∧ (w = true → mx = true)
          · rw [if_pos c] at hb
            have := (Option.some.inj hb)
            have h1 := congrArg Prod.fst this
            simp only [Frame.addBinding] at h1
            exact h1.symm
          · simp [c] at hb
    simp only [hb] at h
    have h2 := Option.some.inj h
    rw [← h2]
    exact hfr

def vectorResolved (owner : Nat) (header : Header) (ty : Ty) (writable : Bool) : Resolved :=
  match header with
  | .root scope => .vector owner scope ty writable
  | .child address => .vectorChild owner address ty writable

theorem bindOne_vector_header_frame (s s' : NState) (owner : Nat) (header : Header) (ty : Ty) (w : Bool)
    (h : bindOne s (vectorResolved owner header ty w) = some s') :
    s'.frame = ⟨s.frame.state,s.frame.rootWritable,s.frame.bindings++[⟨owner,.integer ty,w,header⟩]⟩ := by
  cases header with
  | root scope => exact bindOne_vector_frame s s' owner scope ty w h
  | child address =>
    cases checked : (s.frame.addBinding ⟨owner,.integer ty,w,.child address⟩).1.resolve
        (s.frame.addBinding ⟨owner,.integer ty,w,.child address⟩).2 (.integer ty) with
    | none => simp [vectorResolved,bindOne,checked] at h
    | some pair =>
      simp only [vectorResolved,bindOne,checked,Bind.bind,Option.bind,Option.some.injEq] at h
      subst s'
      rfl

theorem resolve_scalar_res (caller : NState) (p : CppVectorBindings.Parameter) (a : NArgument)
    (hp : ∃ ty r w, p = .scalar ty r w) (n : NState) (r : Resolved) (h : resolve caller p a = some (n, r)) :
    IsScalarRes r := by
  obtain ⟨ty, rf, w, rfl⟩ := hp
  cases a with
  | value e =>
    cases rf with
    | false =>
      simp only [resolve, Bind.bind, Option.bind] at h
      by_cases c : e.resultType = ty
      · rw [if_pos c] at h
        cases he : e.eval caller with
        | none => simp [he] at h
        | some q => simp [he] at h; obtain ⟨_, rfl⟩ := h; trivial
      · rw [if_neg c] at h; simp at h
    | true => simp [resolve] at h
  | vectorReference s => simp [resolve] at h
  | scalarReference s =>
    cases rf with
    | false => simp [resolve] at h
    | true =>
      simp only [resolve, Bind.bind, Option.bind] at h
      cases hc : caller.scalarCell s ty with
      | none => simp [hc] at h
      | some q =>
        simp only [hc] at h
        by_cases c : (w = true → q.1.writable = true)
        · rw [if_pos c] at h; simp at h; obtain ⟨_, rfl⟩ := h; trivial
        · rw [if_neg c] at h; simp at h

theorem resolveAll_scalar_res : ∀ (ps : List CppVectorBindings.Parameter) (args : List NArgument) (caller l : NState)
    (rs : List Resolved), (∀ p ∈ ps, ∃ ty r w, p = .scalar ty r w) → resolveAll caller ps args = some (l, rs) →
    ∀ r ∈ rs, IsScalarRes r := by
  intro ps
  induction ps with
  | nil =>
    intro args caller l rs _ h
    cases args with
    | nil => simp [resolveAll] at h; obtain ⟨_, rfl⟩ := h; simp
    | cons a as => simp [resolveAll] at h
  | cons p ps ih =>
    intro args caller l rs hp h
    cases args with
    | nil => simp [resolveAll] at h
    | cons a as =>
      simp only [resolveAll, Bind.bind, Option.bind] at h
      cases h1 : resolve caller p a with
      | none => simp [h1] at h
      | some q =>
        obtain ⟨nx, first⟩ := q
        simp only [h1] at h
        cases h2 : resolveAll nx ps as with
        | none => simp [h2] at h
        | some q2 =>
          obtain ⟨last, rest⟩ := q2
          simp only [h2] at h
          obtain ⟨rfl, rfl⟩ := Option.some.inj h |> Prod.mk.inj
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact resolve_scalar_res caller p a (hp p List.mem_cons_self) nx r h1
          · exact ih as nx last rest (fun x hx => hp x (List.mem_cons_of_mem _ hx)) h2 r hr

theorem resolve_vector_res (caller : NState) (ty : Ty) (a : NArgument) (n : NState) (r : Resolved)
    (h : resolve caller (.vector ty false) a = some (n, r)) : ∃ o header, r = vectorResolved o header ty false := by
  cases a with
  | value e => simp [resolve] at h
  | scalarReference s => simp [resolve] at h
  | vectorReference s =>
    simp only [resolve, Bind.bind, Option.bind] at h
    cases h1 : caller.vectorSlot s with
    | none => simp [h1] at h
    | some idx =>
      simp only [h1] at h
      cases h2 : caller.frame.bindings[idx]? with
      | none => simp [h2] at h
      | some b =>
        simp only [h2] at h
        cases h3 : caller.frame.resolve idx (.integer ty) with
        | none => simp [h3] at h
        | some q =>
          simp only [h3] at h
          cases hh : b.header with
          | child address =>
            simp only [hh] at h
            by_cases c : b.element = .integer ty
            · rw [if_pos ⟨c, nofun⟩] at h
              simp at h
              obtain ⟨_, rfl⟩ := h
              exact ⟨b.owner,.child address,rfl⟩
            · rw [if_neg (fun hh => c hh.1)] at h
              simp at h
          | root sc =>
            simp only [hh] at h
            by_cases c : b.element = .integer ty
            · rw [if_pos ⟨c, nofun⟩] at h
              simp at h
              obtain ⟨_, rfl⟩ := h
              exact ⟨b.owner,.root sc,rfl⟩
            · rw [if_neg (fun hh => c hh.1)] at h
              simp at h

theorem prepare_vec_frame (caller : NState) (ty : Ty) (rest : List CppVectorBindings.Parameter) (args : List NArgument)
    (Sinit : NState) (hrest : ∀ p ∈ rest, ∃ ty r w, p = .scalar ty r w)
    (h : prepare caller (.vector ty false :: rest) args = some Sinit) :
    ∃ last owner header, ∃ rs, resolveAll caller (.vector ty false :: rest) args = some (last, vectorResolved owner header ty false :: rs) ∧
      Sinit.frame = ⟨last.frame.state, last.frame.rootWritable, [⟨owner,.integer ty,false,header⟩]⟩ := by
  simp only [prepare, Bind.bind, Option.bind] at h
  by_cases wf : caller.frame.state.wellFormed = true
  · simp only [wf, if_true] at h
    cases hr : resolveAll caller (.vector ty false :: rest) args with
    | none => simp [hr] at h
    | some q =>
      obtain ⟨last, resolved⟩ := q
      simp only [hr] at h
      cases args with
      | nil => simp [resolveAll] at hr
      | cons a as =>
        simp only [resolveAll, Bind.bind, Option.bind] at hr
        cases h1 : resolve caller (.vector ty false) a with
        | none => simp [h1] at hr
        | some q1 =>
          obtain ⟨nx, first⟩ := q1
          simp only [h1] at hr
          cases h2 : resolveAll nx rest as with
          | none => simp [h2] at hr
          | some q2 =>
            obtain ⟨l2, rest2⟩ := q2
            simp only [h2] at hr
            obtain ⟨rfl, rfl⟩ := Option.some.inj hr |> Prod.mk.inj
            obtain ⟨o, sc, rfl⟩ := resolve_vector_res caller ty a nx first h1
            have hsc := resolveAll_scalar_res rest as nx l2 rest2 hrest h2
            simp only [bindAll, Bind.bind, Option.bind] at h
            refine ⟨l2, o, sc, rest2, ?_, ?_⟩
            · simp only [resolveAll, Bind.bind, Option.bind, h1, h2]
            · split at h
              · cases h
              · rename_i f n1 hb1
                have h' : bindAll n1 rest2 = some Sinit := h
                rw [bindAll_scalar_frame rest2 hsc n1 Sinit h',
                  bindOne_vector_header_frame _ n1 o sc ty false hb1]
                rfl
  · simp [wf] at h

end Proofs.VecPrepare
