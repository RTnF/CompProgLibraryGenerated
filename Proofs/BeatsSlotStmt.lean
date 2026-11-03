import Proofs.BeatsSlotEval
import Proofs.CppNestedStmt

namespace Proofs.BeatsSlotCycle
open Proofs.CppNestedProgram Proofs.CppMixedInvoke Proofs.CppScalar
open Proofs.CppSlotRename

theorem rotate_append (xs ys : List α) (long : 16 ≤ xs.length) :
    rotate (xs++ys) = rotate xs++ys := by
  apply List.ext_getElem?
  intro i
  rw [rotate_lookup _ (by simp only [List.length_append]; omega)]
  by_cases inside : i < xs.length
  · have mapped : cycle i < xs.length := by
      unfold cycle
      split <;> (try split) <;> omega
    simp only [List.getElem?_append,rotate_length xs long,ite_eq_left inside,
      ite_eq_left mapped,rotate_lookup xs long]
  · have tail : cycle i = i := cycle_ge i (by omega)
    simp only [List.getElem?_append,rotate_length xs long,tail,ite_eq_right inside]

theorem release_permute (after before : NState) :
    permute (after.release before) = (permute after).release (permute before) := rfl

theorem declared_permute (s : NState) (long : 16 ≤ s.slots.length) (ty : Ty)
    (writable : Bool) (value : Int) :
    permute (s.declared ty writable value) = (permute s).declared ty writable value := by
  unfold NState.declared permute
  rw [rotate_append s.slots _ long]

theorem enter_permute (s : NState) :
    permute {s with scope := s.scope+1} = {permute s with scope := s.scope+1} := rfl

theorem frame_permute (s : NState) : (permute s).frame = s.frame := rfl
theorem scalars_permute (s : NState) : (permute s).scalars = s.scalars := rfl
theorem scope_permute (s : NState) : (permute s).scope = s.scope := rfl

theorem leave_permute (outer inner : NState) (ret : Option Ret) :
    (outer.leave inner ret).map permute = (permute outer).leave (permute inner) ret := by
  rcases outer with ⟨os,ofr,ox,oc,op⟩
  rcases inner with ⟨ins,inf,ix,ic,ip⟩
  dsimp only [permute,NState.leave]
  by_cases ok : os.memory.length ≤ ins.memory.length ∧
      (ins.memory.take os.memory.length).map Proofs.CppState.Cell.type =
        os.memory.map Proofs.CppState.Cell.type
  · simp only [ite_eq_left ok,Bind.bind]
    cases ret with
    | none =>
      simp only [Option.map_bind,Option.map_some,Option.bind_some,Function.comp_def]
      congr 1
    | some returned =>
      cases returned <;> simp only [Option.map_bind,Option.map_some,Option.bind_some,Function.comp_def]
      all_goals congr 1
  · simp only [ite_eq_right ok,Option.map_none]


def permuteStep (step : NStep) : NStep := {step with state := permute step.state}

theorem declare_run_permute (s : NState) (long : 16 ≤ s.slots.length)
    (ty : Ty) (writable : Bool) (e : NExpr) :
    ((NStmt.declare ty writable (expr cycle e)).run s).map permuteStep =
      (NStmt.declare ty writable e).run (permute s) := by
  have equal := expr_eval_permute s long e
  cases ran : (expr cycle e).eval s with
  | none =>
    simp only [ran,Option.map_none] at equal
    simp [NStmt.run,ran,← equal]
  | some pair =>
    obtain ⟨t,v⟩ := pair
    have nextLong : 16 ≤ t.slots.length := by rw [(expr_related e).slots s t v ran]; exact long
    simp only [ran,Option.map_some] at equal
    simp only [NStmt.run,ran,← equal,Bind.bind,Option.bind_some]
    cases converted : ty.convert v with
    | none => simp
    | some value =>
      simp [permuteStep,permute,NState.release,rotate_append t.slots _ nextLong] <;> rfl

theorem assign_run_permute (s : NState) (long : 16 ≤ s.slots.length)
    (slot : Nat) (ty : Ty) (e : NExpr) :
    ((NStmt.assign (cycle slot) ty (expr cycle e)).run s).map permuteStep =
      (NStmt.assign slot ty e).run (permute s) := by
  have equal := expr_eval_permute s long e
  cases ran : (expr cycle e).eval s with
  | none =>
    simp only [ran,Option.map_none] at equal
    simp [NStmt.run,ran,← equal]
  | some pair =>
    obtain ⟨t,v⟩ := pair
    have nextLong : 16 ≤ (t.release s).slots.length := by
      change 16 ≤ t.slots.length
      rw [(expr_related e).slots s t v ran]
      exact long
    simp only [ran,Option.map_some] at equal
    simp only [NStmt.run,ran,← equal,Bind.bind,Option.bind_some]
    rw [← release_permute,scalarCell_permute (t.release s) nextLong]
    cases resolved : (t.release s).scalarCell (cycle slot) ty with
    | none => simp
    | some pair =>
      obtain ⟨binding,cell⟩ := pair
      cases writable : binding.writable <;> cases converted : ty.convert v <;>
        simp [writable,permuteStep,permute,NState.release] <;> rfl

theorem EvalRel.toStep {f g : NState → Option (NState × Unit)} (related : EvalRel f g)
    (s : NState) (long : 16 ≤ s.slots.length) :
    ((f s).map (fun p => (⟨p.1,none,false⟩ : NStep))).map permuteStep =
      (g (permute s)).map (fun p => (⟨p.1,none,false⟩ : NStep)) := by
  rw [← related.commute s long]
  simp only [Option.map_map]
  rfl

theorem write_run_permute (s : NState) (long : 16 ≤ s.slots.length)
    (c : Container) (ty : Ty) (index value : NExpr) :
    ((NStmt.write (container cycle c) ty (expr cycle index) (expr cycle value)).run s).map permuteStep =
      (NStmt.write c ty index value).run (permute s) := by
  have all := ((expr_related value).precharge 0 (c.nodes+index.nodes+value.nodes+3)).bind
    (fun v => (container_related c).bind (fun owner => (expr_related index).bind (fun position =>
      frameStep_related (fun frame => do
        let reference ← frame.elementRef owner ty position
        let changed ← frame.write reference v
        some ({changed with bindings := changed.bindings.take s.frame.bindings.length},())) 1 0)))
  simpa only [Bind.bind,NStmt.run,expr_nodes,container_nodes,frameStep,
    Option.map_bind,Option.map_map,Function.comp_def,Option.map_some,Option.bind_some,Option.bind_assoc,NState.release,permuteStep,frame_permute]
    using all.toStep s long

end Proofs.BeatsSlotCycle
