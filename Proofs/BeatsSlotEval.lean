import Proofs.BeatsSlotCycle

namespace Proofs.BeatsSlotCycle
open Proofs.CppNestedProgram Proofs.CppMixedInvoke Proofs.CppScalar
open Proofs.CppSlotRename

-- Correspondence includes failure and keeps the table needed by later steps.
structure EvalRel (f g : NState → Option (NState × α)) : Prop where
  commute : ∀ s, 16 ≤ s.slots.length →
    (f s).map (fun p => (permute p.1,p.2)) = g (permute s)
  slots : ∀ s t a, f s = some (t,a) → t.slots = s.slots

theorem EvalRel.bind {f g : NState → Option (NState × α)}
    {h k : α → NState → Option (NState × β)}
    (first : EvalRel f g) (next : ∀ a, EvalRel (h a) (k a)) :
    EvalRel
      (fun s => (f s).bind fun (t,a) => h a t)
      (fun s => (g s).bind fun (t,a) => k a t) := by
  constructor
  · intro s long
    have equal := first.commute s long
    cases ran : f s with
    | none => simp only [ran,Option.map_none] at equal; simp [equal.symm]
    | some pair =>
      obtain ⟨t,a⟩ := pair
      have wide : 16 ≤ t.slots.length := by rw [first.slots s t a ran]; exact long
      simp only [ran,Option.map_some] at equal
      simp only [← equal,Option.bind_some]
      exact (next a).commute t wide
  · intro s u b ran
    cases firstRun : f s with
    | none => simp [firstRun] at ran
    | some pair =>
      obtain ⟨t,a⟩ := pair
      simp only [firstRun,Option.bind_some] at ran
      exact ((next a).slots t u b ran).trans (first.slots s t a firstRun)

theorem EvalRel.precharge {f g : NState → Option (NState × α)}
    (related : EvalRel f g) (w p : Nat) :
    EvalRel (fun s => f (s.charge w p)) (fun s => g (s.charge w p)) := by
  constructor
  · intro s long
    exact related.commute (s.charge w p) long
  · intro s t a ran
    exact related.slots (s.charge w p) t a ran

def finish (q : Option α) (w p : Nat) (s : NState) : Option (NState × α) := do
  let a ← q
  some (s.charge w p,a)

theorem finish_related (q : Option α) (w p : Nat) : EvalRel (finish q w p) (finish q w p) := by
  constructor
  · intro s _
    cases q <;> rfl
  · intro s t a ran
    cases q with
    | none => simp [finish] at ran
    | some value => cases ran; rfl

def frameStep (f : Proofs.CppNestedVectorBindings.Frame →
    Option (Proofs.CppNestedVectorBindings.Frame × α)) (w p : Nat) (s : NState) :
    Option (NState × α) := do
  let (frame,a) ← f s.frame
  some (({s with frame := frame} : NState).charge w p,a)

theorem frameStep_related (f : Proofs.CppNestedVectorBindings.Frame →
    Option (Proofs.CppNestedVectorBindings.Frame × α)) (w p : Nat) :
    EvalRel (frameStep f w p) (frameStep f w p) := by
  constructor
  · intro s _
    cases found : f s.frame with
    | none => simp [frameStep,permute,found]
    | some pair => obtain ⟨frame,a⟩ := pair; simp [frameStep,permute,found]; rfl
  · intro s t a ran
    cases found : f s.frame with
    | none => simp [frameStep,found] at ran
    | some pair =>
      obtain ⟨frame,v⟩ := pair
      simp [frameStep,found] at ran
      rw [← ran.1]
      rfl

theorem local_related (i : Nat) :
    EvalRel (fun s => (Container.local (cycle i)).eval s) (fun s => (Container.local i).eval s) := by
  constructor
  · exact fun s long => local_eval_permute s long i
  · intro s t a ran
    cases found : s.vectorSlot (cycle i) with
    | none => simp [Container.eval,found] at ran
    | some v => simp [Container.eval,found] at ran; rw [← ran.1]; rfl

theorem literal_related (ty : Ty) (v : Int) :
    EvalRel (fun s => (NExpr.literal ty v).eval s) (fun s => (NExpr.literal ty v).eval s) := by
  constructor
  · exact fun s _ => literal_eval_permute s ty v
  · intro s t a ran
    simp only [NExpr.eval] at ran
    split at ran
    · cases ran; rfl
    · simp at ran

theorem variable_related (ty : Ty) (i : Nat) :
    EvalRel (fun s => (NExpr.variable ty (cycle i)).eval s) (fun s => (NExpr.variable ty i).eval s) := by
  constructor
  · exact fun s long => variable_eval_permute s long i ty
  · intro s t a ran
    cases found : s.scalarCell (cycle i) ty with
    | none => simp [NExpr.eval,found] at ran
    | some pair => obtain ⟨binding,cell⟩ := pair; simp [NExpr.eval,found] at ran; rw [← ran.1]; rfl

def logicalTail (conjunction : Bool) (a : Int) (f : NState → Option (NState × Int))
    (s : NState) : Option (NState × Int) :=
  if conjunction then
    if a == 0 then finish (some 0) 1 1 s
    else (f s).bind fun (t,b) => finish (some (if b == 0 then 0 else 1)) 1 1 t
  else
    if a == 0 then (f s).bind fun (t,b) => finish (some (if b == 0 then 0 else 1)) 1 1 t
    else finish (some 1) 1 1 s

theorem logicalTail_related (conjunction : Bool) (a : Int)
    {f g : NState → Option (NState × Int)} (related : EvalRel f g) :
    EvalRel (logicalTail conjunction a f) (logicalTail conjunction a g) := by
  unfold logicalTail
  cases conjunction <;> cases zero : (a == 0) <;>
    simp only [Bool.false_eq_true,ite_false,ite_true] <;>
    first
    | exact finish_related _ 1 1
    | exact related.bind (fun b => finish_related (some (if b == 0 then 0 else 1)) 1 1)

mutual
theorem container_related : ∀ c,
    EvalRel (fun s => (container cycle c).eval s) (fun s => c.eval s)
  | .local i => local_related i
  | .row parent el index => by
      have all := ((container_related parent).precharge 0 (parent.nodes+index.nodes+1)).bind
        (fun owner => (expr_related index).bind (fun position =>
          frameStep_related (fun frame => frame.child owner el position) 1 1))
      simpa only [Bind.bind,container,Container.eval,container_nodes,expr_nodes,frameStep] using all
theorem expr_related : ∀ e,
    EvalRel (fun s => (expr cycle e).eval s) (fun s => e.eval s)
  | .literal ty v => literal_related ty v
  | .variable ty i => variable_related ty i
  | .cast ty e => by
      have all := ((expr_related e).precharge 0 (e.nodes+1)).bind
        (fun value => finish_related (ty.convert value) 1 1)
      simpa only [Bind.bind,expr,NExpr.eval,expr_nodes,finish] using all
  | .targetCast ty e => by
      have all := ((expr_related e).precharge 0 (e.nodes+1)).bind
        (fun value => finish_related (ty.targetConvert value) 1 1)
      simpa only [Bind.bind,expr,NExpr.eval,expr_nodes,finish] using all
  | .unary ty op e => by
      have all := ((expr_related e).precharge 0 (e.nodes+1)).bind
        (fun value => finish_related (ty.convert (unaryValue op value)) 1 1)
      simpa only [Bind.bind,expr,NExpr.eval,expr_nodes,finish] using all
  | .binary ty op left right => by
      have all := ((expr_related left).precharge 0 (left.nodes+right.nodes+1)).bind
        (fun a => (expr_related right).bind (fun b =>
          finish_related (ty.convert (binaryValue op a b)) 1 1))
      simpa only [Bind.bind,expr,NExpr.eval,expr_nodes,finish] using all
  | .divrem ty remainder left right => by
      have all := ((expr_related left).precharge 0 (left.nodes+right.nodes+1)).bind
        (fun a => (expr_related right).bind (fun b =>
          finish_related (checkedDivRem ty remainder a b) 1 1))
      simpa only [Bind.bind,expr,NExpr.eval,expr_nodes,finish] using all
  | .logical conjunction left right => by
      have all := ((expr_related left).precharge 0 (left.nodes+right.nodes+1)).bind
        (fun a => logicalTail_related conjunction a (expr_related right))
      simpa only [Bind.bind,expr,NExpr.eval,expr_nodes,logicalTail,finish,Option.bind_some] using all
  | .size el c => by
      have all := ((container_related c).precharge 0 (c.nodes+2)).bind
        (fun owner => frameStep_related (fun frame => frame.size owner el) 1 2)
      simpa only [Bind.bind,expr,NExpr.eval,container_nodes,frameStep] using all
  | .read ty c index => by
      have all := ((container_related c).precharge 0 (c.nodes+index.nodes+2)).bind
        (fun owner => (expr_related index).bind (fun position =>
          frameStep_related (fun frame => do
            let reference ← frame.elementRef owner ty position
            let value ← frame.read reference
            some (frame,value)) 1 2))
      simpa only [Bind.bind,expr,NExpr.eval,container_nodes,expr_nodes,frameStep,Option.bind_assoc,
        Option.bind_some] using all
end

theorem container_eval_permute (s : NState) (long : 16 ≤ s.slots.length) (c : Container) :
    ((container cycle c).eval s).map (fun p => (permute p.1,p.2)) = c.eval (permute s) :=
  (container_related c).commute s long

theorem expr_eval_permute (s : NState) (long : 16 ≤ s.slots.length) (e : NExpr) :
    ((expr cycle e).eval s).map (fun p => (permute p.1,p.2)) = e.eval (permute s) :=
  (expr_related e).commute s long

theorem expr_fault_permute (s : NState) (long : 16 ≤ s.slots.length) (e : NExpr) :
    (expr cycle e).eval s = none ↔ e.eval (permute s) = none := by
  rw [← expr_eval_permute s long e]
  cases (expr cycle e).eval s <;> simp

end Proofs.BeatsSlotCycle
