import Proofs.BeatsBindingCycle

namespace Proofs.BeatsBindingCycle
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppNestedVectorStore Proofs.CppVectorOwnership Proofs.CppVector
open Proofs.BeatsSlotCycle (uncycle)

universe u v

private theorem bind_some {α : Type u} {β : Type v} (o : Option α) (f : α → Option β) (v : β)
    (ran : o.bind f = some v) : ∃ a, o = some a ∧ f a = some v := Option.bind_eq_some_iff.mp ran

theorem bindChild (f : Frame) (long : 16 ≤ f.bindings.length) (i : Nat)
    (el : Element) (index : Int) (wr : Bool) :
    (rebind f).bindChild (uncycle i) el index wr =
      (f.bindChild i el index wr).map (fun p => (rebind p.1,p.2)) := by
  simp only [Frame.bindChild,resolve f long,object,Bind.bind,Option.map_bind,Function.comp_def]
  cases f.resolve i (.vector el) with
  | none => rfl
  | some pair =>
    dsimp only [Option.bind_some]
    split
    · cases CppVector.elementRef pair.2 (accepts (.vector el)) index with
      | none => rfl
      | some address =>
        dsimp only [Option.bind_some]
        cases readRef pair.2 (accepts (.vector el)) address with
        | none => rfl
        | some result =>
          dsimp only [Option.bind_some]
          cases result.value with
          | integer value => rfl
          | child owner =>
            dsimp only
            cases f.object owner el with
            | none => rfl
            | some childPair =>
              dsimp only [Option.bind_some]
              split
              · simp only [Option.map_some,addBinding f long]
              · rfl
    · rfl

theorem bindChild_growth (f out : Frame) (i : Nat) (el : Element) (index : Int) (wr : Bool) (j : Nat)
    (ran : f.bindChild i el index wr = some (out,j)) :
    out.bindings.length = f.bindings.length+1 ∧ j = f.bindings.length := by
  unfold Frame.bindChild at ran
  obtain ⟨pair,_,rest⟩ := bind_some _ _ _ ran
  obtain ⟨origin,parent⟩ := pair
  dsimp only at rest
  split at rest
  · obtain ⟨address,_,rest⟩ := bind_some _ _ _ rest
    obtain ⟨result,_,rest⟩ := bind_some _ _ _ rest
    cases choice : result.value with
    | integer value => simp [choice] at rest
    | child owner =>
      simp only [choice] at rest
      obtain ⟨childPair,_,rest⟩ := bind_some _ _ _ rest
      obtain ⟨buffer,tag⟩ := childPair
      dsimp only at rest
      split at rest
      · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj rest)
        simp only [List.length_append,List.length_singleton,and_self]
      · simp at rest
  · simp at rest

theorem child (f : Frame) (long : 16 ≤ f.bindings.length) (i : Nat) (el : Element) (index : Int) :
    (rebind f).child (uncycle i) el index = (f.child i el index).map (fun p => (rebind p.1,uncycle p.2)) := by
  simp only [Frame.child,resolve f long,Bind.bind,Option.map_bind,Function.comp_def]
  cases found : f.resolve i (.vector el) with
  | none => rfl
  | some pair =>
    dsimp only [Option.bind_some]
    rw [bindChild f long]
    cases ran : f.bindChild i el index pair.1.writable with
    | none => rfl
    | some result =>
      have next := (bindChild_growth f result.1 i el index pair.1.writable result.2 ran).2
      have unchanged : uncycle result.2 = result.2 := by
        rw [next]
        simp only [Proofs.BeatsSlotCycle.uncycle,show f.bindings.length ≠ 0 by omega,
          show ¬ f.bindings.length < 16 by omega,ite_false]
      simp only [Option.map_some,unchanged]

theorem child_growth (f out : Frame) (i : Nat) (el : Element) (index : Int) (j : Nat)
    (ran : f.child i el index = some (out,j)) : f.bindings.length ≤ out.bindings.length := by
  unfold Frame.child at ran
  obtain ⟨pair,_,rest⟩ := bind_some _ _ _ ran
  have growth := (bindChild_growth f out i el index pair.1.writable j rest).1
  omega

private theorem checked_frame (f : Frame) (v : Int) (ok : Bool) :
    (if ok then some (rebind f,v) else none) =
      (if ok then some (f,v) else none).map (fun p => (rebind p.1,p.2)) := by
  cases ok <;> rfl

theorem size (f : Frame) (long : 16 ≤ f.bindings.length) (i : Nat) (el : Element) :
    (rebind f).size (uncycle i) el = (f.size i el).map (fun p => (rebind p.1,p.2)) := by
  simp only [Frame.size,resolve f long,Bind.bind,Option.map_bind,Function.comp_def]
  apply congrArg (fun k => (f.resolve i el).bind k)
  funext pair
  exact checked_frame f (pair.2.items.length : Int) ((⟨64,false,false⟩ : Ty).valid (pair.2.items.length : Int))


private theorem checked_growth (f out : Frame) (v value : Int) (ok : Bool)
    (ran : (if ok then some (f,v) else none) = some (out,value)) : f.bindings.length ≤ out.bindings.length := by
  cases ok with
  | false => contradiction
  | true => cases ran; exact Nat.le_refl _

theorem size_growth (f out : Frame) (i : Nat) (el : Element) (value : Int)
    (ran : f.size i el = some (out,value)) : f.bindings.length ≤ out.bindings.length := by
  unfold Frame.size at ran
  obtain ⟨pair,_,rest⟩ := bind_some _ _ _ ran
  exact checked_growth f out (pair.2.items.length : Int) value _ rest

def readValue (f : Frame) (i : Nat) (ty : Ty) (index : Int) : Option (Frame × Int) := do
  let ref ← f.elementRef i ty index
  let value ← f.read ref
  some (f,value)

theorem readValue_map (f : Frame) (long : 16 ≤ f.bindings.length) (i : Nat) (ty : Ty) (index : Int) :
    readValue (rebind f) (uncycle i) ty index = (readValue f i ty index).map (fun p => (rebind p.1,p.2)) := by
  unfold readValue
  rw [elementRef f long]
  simp only [Bind.bind,Option.map_bind,Function.comp_def]
  cases f.elementRef i ty index with
  | none => rfl
  | some ref =>
    dsimp only [Option.map_some,Option.bind_some]
    rw [read f long]

theorem readValue_growth (f out : Frame) (i : Nat) (ty : Ty) (index value : Int)
    (ran : readValue f i ty index = some (out,value)) : f.bindings.length ≤ out.bindings.length := by
  unfold readValue at ran
  obtain ⟨ref,_,rest⟩ := bind_some _ _ _ ran
  obtain ⟨v,_,rest⟩ := bind_some _ _ _ rest
  cases rest
  exact Nat.le_refl _

-- Container results are binding indices, so their output uses uncycle;
-- integer results use id. Growth retains the precondition across row bindings.
structure EvalRel (ρ : α → α) (f g : NState → Option (NState × α)) : Prop where
  commute : ∀ s, 16 ≤ s.frame.bindings.length →
    (f s).map (fun p => (view p.1,ρ p.2)) = g (view s)
  growth : ∀ s t a, f s = some (t,a) → s.frame.bindings.length ≤ t.frame.bindings.length

theorem EvalRel.bind {ρ : α → α} {σ : β → β} {f g : NState → Option (NState × α)}
    {h k : α → NState → Option (NState × β)} (first : EvalRel ρ f g)
    (next : ∀ a, EvalRel σ (h a) (k (ρ a))) :
    EvalRel σ (fun s => (f s).bind fun (t,a) => h a t) (fun s => (g s).bind fun (t,a) => k a t) := by
  constructor
  · intro s long
    have equal := first.commute s long
    cases ran : f s with
    | none => simp only [ran,Option.map_none] at equal; simp [equal.symm]
    | some pair =>
      obtain ⟨t,a⟩ := pair
      have wide : 16 ≤ t.frame.bindings.length := Nat.le_trans long (first.growth s t a ran)
      simp only [ran,Option.map_some] at equal
      simp only [← equal,Option.bind_some]
      exact (next a).commute t wide
  · intro s u b ran
    cases firstRun : f s with
    | none => simp [firstRun] at ran
    | some pair =>
      obtain ⟨t,a⟩ := pair
      simp only [firstRun,Option.bind_some] at ran
      exact Nat.le_trans (first.growth s t a firstRun) ((next a).growth t u b ran)

theorem EvalRel.bind_id {σ : β → β} {f g : NState → Option (NState × α)}
    {h k : α → NState → Option (NState × β)} (first : EvalRel id f g)
    (next : ∀ a, EvalRel σ (h a) (k a)) :
    EvalRel σ (fun s => (f s).bind fun (t,a) => h a t) (fun s => (g s).bind fun (t,a) => k a t) :=
  first.bind next

theorem EvalRel.precharge {ρ : α → α} {f g : NState → Option (NState × α)}
    (related : EvalRel ρ f g) (w p : Nat) :
    EvalRel ρ (fun s => f (s.charge w p)) (fun s => g (s.charge w p)) := by
  constructor
  · intro s long
    exact related.commute (s.charge w p) long
  · intro s t a ran
    exact related.growth (s.charge w p) t a ran

abbrev finish := @Proofs.BeatsSlotCycle.finish
abbrev logicalTail := Proofs.BeatsSlotCycle.logicalTail
abbrev frameStep := @Proofs.BeatsSlotCycle.frameStep

theorem finish_related (q : Option α) (w p : Nat) : EvalRel id (finish q w p) (finish q w p) := by
  constructor
  · intro s _
    cases q <;> rfl
  · intro s t a ran
    cases q with
    | none => simp [finish,Proofs.BeatsSlotCycle.finish] at ran
    | some value => cases ran; exact Nat.le_refl _

theorem frameStep_related (ρ : α → α) (f g : Frame → Option (Frame × α))
    (commute : ∀ frame, 16 ≤ frame.bindings.length →
      (f frame).map (fun p => (rebind p.1,ρ p.2)) = g (rebind frame))
    (growth : ∀ frame next a, f frame = some (next,a) → frame.bindings.length ≤ next.bindings.length)
    (w p : Nat) : EvalRel ρ (frameStep f w p) (frameStep g w p) := by
  constructor
  · intro s long
    have equal := commute s.frame long
    cases found : f s.frame with
    | none => simp only [found,Option.map_none] at equal; simp [frameStep,Proofs.BeatsSlotCycle.frameStep,view,equal.symm,found]
    | some pair =>
      obtain ⟨frame,a⟩ := pair
      simp only [found,Option.map_some] at equal
      simp [frameStep,Proofs.BeatsSlotCycle.frameStep,view,← equal,found]
      rfl
  · intro s t a ran
    unfold frameStep Proofs.BeatsSlotCycle.frameStep at ran
    obtain ⟨pair,found,rest⟩ := bind_some _ _ _ ran
    cases rest
    exact growth s.frame pair.1 pair.2 found

theorem local_related (i : Nat) : EvalRel uncycle (fun s => (Container.local i).eval s) (fun s => (Container.local i).eval s) := by
  constructor
  · intro s _
    simp only [Container.eval,vectorSlot,Bind.bind,Option.map_bind,Function.comp_def]
    cases s.vectorSlot i <;> rfl
  · intro s t a ran
    unfold Container.eval at ran
    obtain ⟨index,_,rest⟩ := bind_some _ _ _ ran
    cases rest
    exact Nat.le_refl _

theorem literal_related (ty : Ty) (v : Int) :
    EvalRel id (fun s => (NExpr.literal ty v).eval s) (fun s => (NExpr.literal ty v).eval s) := by
  constructor
  · intro s _
    simp only [NExpr.eval]
    split <;> rfl
  · intro s t a ran
    simp only [NExpr.eval] at ran
    split at ran
    · cases ran; exact Nat.le_refl _
    · simp at ran

theorem variable_related (ty : Ty) (i : Nat) :
    EvalRel id (fun s => (NExpr.variable ty i).eval s) (fun s => (NExpr.variable ty i).eval s) := by
  constructor
  · intro s _
    simp only [NExpr.eval,scalarCell]
    cases s.scalarCell i ty <;> rfl
  · intro s t a ran
    unfold NExpr.eval at ran
    obtain ⟨pair,_,rest⟩ := bind_some _ _ _ ran
    obtain ⟨binding,cell⟩ := pair
    cases rest
    exact Nat.le_refl _

theorem logicalTail_related (conjunction : Bool) (a : Int)
    {f g : NState → Option (NState × Int)} (related : EvalRel id f g) :
    EvalRel id (logicalTail conjunction a f) (logicalTail conjunction a g) := by
  unfold logicalTail Proofs.BeatsSlotCycle.logicalTail
  cases conjunction <;> cases zero : (a == 0) <;>
    simp only [Bool.false_eq_true,ite_false,ite_true] <;>
    first
    | exact finish_related _ 1 1
    | exact related.bind (h := fun b => finish (some (if b == 0 then 0 else 1)) 1 1)
        (k := fun b => finish (some (if b == 0 then 0 else 1)) 1 1)
        (fun b => finish_related (some (if b == 0 then 0 else 1)) 1 1)

mutual
theorem container_related : ∀ (c : Container), EvalRel uncycle (fun s => c.eval s) (fun s => c.eval s)
  | .local i => local_related i
  | .row parent el index => by
      have all := ((container_related parent).precharge 0 (parent.nodes+index.nodes+1)).bind
        (k := fun owner s => (index.eval s).bind fun (t,position) =>
          frameStep (fun frame => frame.child owner el position) 1 1 t)
        (fun owner => (expr_related index).bind_id (fun position =>
          frameStep_related uncycle (fun frame => frame.child owner el position)
            (fun frame => frame.child (uncycle owner) el position)
            (fun f long => (child f long owner el position).symm)
            (fun f out j ran => child_growth f out owner el position j ran) 1 1))
      simpa only [Bind.bind,Container.eval,frameStep,Proofs.BeatsSlotCycle.frameStep,id_eq] using all
theorem expr_related : ∀ (e : NExpr), EvalRel id (fun s => e.eval s) (fun s => e.eval s)
  | .literal ty v => literal_related ty v
  | .variable ty i => variable_related ty i
  | .cast ty e => by
      have all := ((expr_related e).precharge 0 (e.nodes+1)).bind_id
        (fun value => finish_related (ty.convert value) 1 1)
      simpa only [Bind.bind,NExpr.eval,finish,Proofs.BeatsSlotCycle.finish,id_eq] using all
  | .targetCast ty e => by
      have all := ((expr_related e).precharge 0 (e.nodes+1)).bind_id
        (fun value => finish_related (ty.targetConvert value) 1 1)
      simpa only [Bind.bind,NExpr.eval,finish,Proofs.BeatsSlotCycle.finish,id_eq] using all
  | .unary ty op e => by
      have all := ((expr_related e).precharge 0 (e.nodes+1)).bind_id
        (fun value => finish_related (ty.convert (unaryValue op value)) 1 1)
      simpa only [Bind.bind,NExpr.eval,finish,Proofs.BeatsSlotCycle.finish,id_eq] using all
  | .binary ty op left right => by
      have all := ((expr_related left).precharge 0 (left.nodes+right.nodes+1)).bind_id
        (fun a => (expr_related right).bind_id (fun b => finish_related (ty.convert (binaryValue op a b)) 1 1))
      simpa only [Bind.bind,NExpr.eval,finish,Proofs.BeatsSlotCycle.finish,id_eq] using all
  | .divrem ty remainder left right => by
      have all := ((expr_related left).precharge 0 (left.nodes+right.nodes+1)).bind_id
        (fun a => (expr_related right).bind_id (fun b => finish_related (checkedDivRem ty remainder a b) 1 1))
      simpa only [Bind.bind,NExpr.eval,finish,Proofs.BeatsSlotCycle.finish,id_eq] using all
  | .logical conjunction left right => by
      have all := ((expr_related left).precharge 0 (left.nodes+right.nodes+1)).bind_id
        (fun a => logicalTail_related conjunction a (expr_related right))
      simpa only [Bind.bind,NExpr.eval,logicalTail,Proofs.BeatsSlotCycle.logicalTail,
        finish,Proofs.BeatsSlotCycle.finish,Option.bind_some,id_eq] using all
  | .size el c => by
      have all := ((container_related c).precharge 0 (c.nodes+2)).bind
        (k := fun owner => frameStep (fun frame => frame.size owner el) 1 2)
        (fun owner => frameStep_related id (fun frame => frame.size owner el)
          (fun frame => frame.size (uncycle owner) el)
          (fun f long => (size f long owner el).symm)
          (fun f out value ran => size_growth f out owner el value ran) 1 2)
      simpa only [Bind.bind,NExpr.eval,frameStep,Proofs.BeatsSlotCycle.frameStep,id_eq] using all
  | .read ty c index => by
      have all := ((container_related c).precharge 0 (c.nodes+index.nodes+2)).bind
        (k := fun owner s => (index.eval s).bind fun (t,position) =>
          frameStep (fun frame => readValue frame owner ty position) 1 2 t)
        (fun owner => (expr_related index).bind_id (fun position =>
          frameStep_related id (fun frame => readValue frame owner ty position)
            (fun frame => readValue frame (uncycle owner) ty position)
            (fun f long => (readValue_map f long owner ty position).symm)
            (fun f out value ran => readValue_growth f out owner ty position value ran) 1 2))
      simpa only [Bind.bind,NExpr.eval,frameStep,Proofs.BeatsSlotCycle.frameStep,readValue,
        Option.bind_assoc,Option.bind_some,id_eq] using all
end

theorem expr_eval_view (s : NState) (long : 16 ≤ s.frame.bindings.length) (e : NExpr) :
    (e.eval s).map (fun p => (view p.1,p.2)) = e.eval (view s) := (expr_related e).commute s long

theorem container_eval_view (s : NState) (long : 16 ≤ s.frame.bindings.length) (c : Container) :
    (c.eval s).map (fun p => (view p.1,uncycle p.2)) = c.eval (view s) := (container_related c).commute s long

theorem expr_fault_view (s : NState) (long : 16 ≤ s.frame.bindings.length) (e : NExpr) :
    e.eval s = none ↔ e.eval (view s) = none := by
  rw [← expr_eval_view s long e]
  cases e.eval s <;> simp

theorem expr_binding_growth (s t : NState) (e : NExpr) (v : Int) (ran : e.eval s = some (t,v)) :
    s.frame.bindings.length ≤ t.frame.bindings.length := (expr_related e).growth s t v ran

end Proofs.BeatsBindingCycle
