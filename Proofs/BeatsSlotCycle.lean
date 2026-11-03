import Proofs.CppSlotRename
import Proofs.CppNestedEval

namespace Proofs.BeatsSlotCycle
open Proofs.CppNestedProgram Proofs.CppMixedInvoke

def cycle (i : Nat) : Nat := if i < 15 then i+1 else if i=15 then 0 else i

def rotate (xs : List α) : List α := (xs.drop 1).take 15 ++ (xs.take 1 ++ xs.drop 16)

theorem rotate_length (xs : List α) (long : 16 ≤ xs.length) :
    (rotate xs).length = xs.length := by
  simp only [rotate, List.length_append, List.length_take, List.length_drop]
  rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
  omega

theorem rotate_lookup (xs : List α) (long : 16 ≤ xs.length) (i : Nat) :
    (rotate xs)[i]? = xs[cycle i]? := by
  have first : ((xs.drop 1).take 15).length = 15 := by
    simp only [List.length_take, List.length_drop]
    exact Nat.min_eq_left (by omega)
  have second : (xs.take 1).length = 1 := by
    simp only [List.length_take]
    exact Nat.min_eq_left (by omega)
  simp only [rotate, List.getElem?_append, first, second]
  by_cases left : i < 15
  · simp only [ite_eq_left left, List.getElem?_take, List.getElem?_drop, cycle]
    congr 1
    omega
  · by_cases middle : i=15
    · subst i
      simp [cycle]
    · have rest : 16 ≤ i := by omega
      have tail : ¬i-15 < 1 := by omega
      simp only [ite_eq_right left, ite_eq_right tail, List.getElem?_drop, cycle,
        ite_eq_right middle]
      congr 1
      omega

def permute (s : NState) : NState := {s with slots := rotate s.slots}

theorem vectorSlot_permute (s : NState) (long : 16 ≤ s.slots.length) (i : Nat) :
    (permute s).vectorSlot i = s.vectorSlot (cycle i) := by
  simp only [NState.vectorSlot, permute, rotate_lookup s.slots long]

theorem scalarSlot_permute (s : NState) (long : 16 ≤ s.slots.length) (i : Nat) :
    (permute s).scalarSlot i = s.scalarSlot (cycle i) := by
  simp only [NState.scalarSlot, permute, rotate_lookup s.slots long]

theorem scalarCell_permute (s : NState) (long : 16 ≤ s.slots.length) (i : Nat)
    (ty : Proofs.CppScalar.Ty) :
    (permute s).scalarCell i ty = s.scalarCell (cycle i) ty := by
  unfold NState.scalarCell
  rw [scalarSlot_permute s long]
  rfl

def uncycle (i : Nat) : Nat := if i=0 then 15 else if i<16 then i-1 else i

theorem cycle_uncycle (i : Nat) : cycle (uncycle i) = i := by
  unfold cycle uncycle
  split <;> (try split) <;> (repeat' split) <;> omega

theorem uncycle_cycle (i : Nat) : uncycle (cycle i) = i := by
  unfold cycle uncycle
  split <;> (try split) <;> (repeat' split) <;> omega

def unrotate (xs : List α) : List α := (xs.drop 15).take 1 ++ (xs.take 15 ++ xs.drop 16)

theorem unrotate_lookup (xs : List α) (long : 16 ≤ xs.length) (i : Nat) :
    (unrotate xs)[i]? = xs[uncycle i]? := by
  have first : ((xs.drop 15).take 1).length = 1 := by
    simp only [List.length_take, List.length_drop]
    exact Nat.min_eq_left (by omega)
  have second : (xs.take 15).length = 15 := by
    simp only [List.length_take]
    exact Nat.min_eq_left (by omega)
  simp only [unrotate, List.getElem?_append, first, second]
  by_cases zero : i=0
  · subst i
    simp [List.getElem?_drop, uncycle]
  · have pos : ¬i<1 := by omega
    by_cases middle : i<16
    · have inner : i-1<15 := by omega
      simp only [ite_eq_right pos, List.getElem?_take, ite_eq_left inner, uncycle, ite_eq_right zero, ite_eq_left middle]
    · have inner : ¬i-1<15 := by omega
      simp only [ite_eq_right pos, ite_eq_right inner, List.getElem?_drop,
        uncycle, ite_eq_right zero, ite_eq_right middle]
      congr 1
      omega

theorem unrotate_length (xs : List α) (long : 16 ≤ xs.length) :
    (unrotate xs).length = xs.length := by
  simp only [unrotate, List.length_append, List.length_take, List.length_drop]
  rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
  omega

theorem unrotate_rotate (xs : List α) (long : 16 ≤ xs.length) : unrotate (rotate xs) = xs := by
  apply List.ext_getElem?
  intro i
  rw [unrotate_lookup _ (by rw [rotate_length xs long]; exact long),
    rotate_lookup xs long, cycle_uncycle]

theorem rotate_unrotate (xs : List α) (long : 16 ≤ xs.length) : rotate (unrotate xs) = xs := by
  apply List.ext_getElem?
  intro i
  rw [rotate_lookup _ (by rw [unrotate_length xs long]; exact long),
    unrotate_lookup xs long, uncycle_cycle]

def unpermute (s : NState) : NState := {s with slots := unrotate s.slots}

theorem unpermute_permute (s : NState) (long : 16 ≤ s.slots.length) :
    unpermute (permute s) = s := by
  change {s with slots := unrotate (rotate s.slots)} = s
  rw [unrotate_rotate s.slots long]

theorem permute_unpermute (s : NState) (long : 16 ≤ s.slots.length) :
    permute (unpermute s) = s := by
  change {s with slots := rotate (unrotate s.slots)} = s
  rw [rotate_unrotate s.slots long]

theorem payload_permute (s : NState) :
    (permute s).scalars = s.scalars ∧ (permute s).frame = s.frame ∧
    (permute s).scope = s.scope ∧ (permute s).peak = s.peak := ⟨rfl,rfl,rfl,rfl⟩

theorem slots_length_permute (s : NState) (long : 16 ≤ s.slots.length) :
    (permute s).slots.length = s.slots.length := rotate_length s.slots long

theorem work_permute (s : NState) : (permute s).work = s.work := rfl

theorem cycle_ge (i : Nat) (bound : 16 ≤ i) : cycle i = i := by
  unfold cycle
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem envOf_permute (s : NState) (long : 16 ≤ s.slots.length) (i : Nat)
    (ty : Proofs.CppScalar.Ty) :
    Proofs.CppNestedEval.envOf (permute s) i ty =
      Proofs.CppNestedEval.envOf s (cycle i) ty := by
  unfold Proofs.CppNestedEval.envOf
  rw [scalarCell_permute s long]

theorem scalarCell_permute_tail (s : NState) (long : 16 ≤ s.slots.length) (i : Nat)
    (bound : 16 ≤ i) (ty : Proofs.CppScalar.Ty) :
    (permute s).scalarCell i ty = s.scalarCell i ty := by
  rw [scalarCell_permute s long, cycle_ge i bound]

theorem denote_permute (s : NState) (long : 16 ≤ s.slots.length) (e : NExpr) :
    (Proofs.CppSlotRename.expr cycle e).denote (Proofs.CppNestedEval.envOf s) =
      e.denote (Proofs.CppNestedEval.envOf (permute s)) := by
  rw [Proofs.CppSlotRename.denote]
  have env : (fun i ty => Proofs.CppNestedEval.envOf s (cycle i) ty) =
      Proofs.CppNestedEval.envOf (permute s) := by
    funext i ty
    exact (envOf_permute s long i ty).symm
  rw [env]

theorem observe_permute (s : NState) : permute s.observe = (permute s).observe := rfl

theorem charge_permute (s : NState) (work temporaries : Nat) :
    permute (s.charge work temporaries) = (permute s).charge work temporaries := rfl

theorem local_eval_permute (s : NState) (long : 16 ≤ s.slots.length) (i : Nat) :
    ((Container.local (cycle i)).eval s).map (fun p => (permute p.1,p.2)) =
      (Container.local i).eval (permute s) := by
  simp only [Container.eval, vectorSlot_permute s long]
  cases s.vectorSlot (cycle i) <;> rfl

theorem literal_eval_permute (s : NState) (ty : Proofs.CppScalar.Ty) (value : Int) :
    ((NExpr.literal ty value).eval s).map (fun p => (permute p.1,p.2)) =
      (NExpr.literal ty value).eval (permute s) := by
  simp only [NExpr.eval]
  split <;> rfl

theorem variable_eval_permute (s : NState) (long : 16 ≤ s.slots.length) (i : Nat)
    (ty : Proofs.CppScalar.Ty) :
    ((NExpr.variable ty (cycle i)).eval s).map (fun p => (permute p.1,p.2)) =
      (NExpr.variable ty i).eval (permute s) := by
  simp only [NExpr.eval, scalarCell_permute s long]
  cases s.scalarCell (cycle i) ty <;> rfl

end Proofs.BeatsSlotCycle
