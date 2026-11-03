import Proofs.CppPeakComponents
import Proofs.CppEvalFrame

set_option maxRecDepth 4000

namespace Proofs.CppEvalPeak
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppVectorOwnership Proofs.DynamicResultValid Proofs.CppPeakComponents

mutual
theorem container_peak (c : Container) (s t : NState) (value : Nat)
    (actual : c.eval s = some (t,value)) : Grows s t := by
  cases c with
  | «local» slot =>
    unfold Container.eval at actual
    obtain ⟨binding,_,rest⟩ := bind_some _ _ _ actual
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    exact charge s 1 1
  | row parent ty index =>
    unfold Container.eval at actual
    obtain ⟨⟨a,owner⟩,ra,rest⟩ := bind_some _ _ _ actual
    obtain ⟨⟨b,pos⟩,rb,rest⟩ := bind_some _ _ _ rest
    obtain ⟨⟨frame,binding⟩,rf,rest⟩ := bind_some _ _ _ rest
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    have same := Proofs.CppEvalFrame.child_frame b.frame frame owner ty pos binding rf
    have reframed := reframe_raw b frame (by rw [same.1]; exact Nat.le_refl _)
    exact (charge s 0 (parent.nodes+index.nodes+1)).trans
      ((container_peak parent _ a owner ra).trans ((expression_peak index a b pos rb).trans
        (reframed.trans (charge _ 1 1))))
termination_by sizeOf c

theorem expression_peak (e : NExpr) (s t : NState) (value : Int)
    (actual : e.eval s = some (t,value)) : Grows s t := by
  cases e with
  | literal ty v =>
    unfold NExpr.eval at actual
    split at actual
    · have eq := congrArg Prod.fst (Option.some.inj actual)
      change _ = t at eq
      subst t
      exact charge s 1 1
    · simp at actual
  | «variable» ty slot =>
    unfold NExpr.eval at actual
    obtain ⟨cell,_,rest⟩ := bind_some _ _ _ actual
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    exact charge s 1 1
  | cast ty operand | targetCast ty operand | unary ty _ operand =>
    unfold NExpr.eval at actual
    obtain ⟨⟨a,x⟩,ra,rest⟩ := bind_some _ _ _ actual
    obtain ⟨x,_,rest⟩ := bind_some _ _ _ rest
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    exact (charge s 0 (operand.nodes+1)).trans
      ((expression_peak operand (s.charge 0 (operand.nodes+1)) a _ ra).trans (charge a 1 1))
  | binary ty _ left right | divrem ty _ left right =>
    unfold NExpr.eval at actual
    obtain ⟨⟨a,x⟩,ra,rest⟩ := bind_some _ _ _ actual
    obtain ⟨⟨b,y⟩,rb,rest⟩ := bind_some _ _ _ rest
    obtain ⟨z,_,rest⟩ := bind_some _ _ _ rest
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    exact (charge s 0 (left.nodes+right.nodes+1)).trans
      ((expression_peak left (s.charge 0 (left.nodes+right.nodes+1)) a x ra).trans
        ((expression_peak right a b y rb).trans (charge b 1 1)))
  | logical conjunction left right =>
    unfold NExpr.eval at actual
    obtain ⟨⟨a,x⟩,ra,rest⟩ := bind_some _ _ _ actual
    have first := (charge s 0 (left.nodes+right.nodes+1)).trans
      (expression_peak left (s.charge 0 (left.nodes+right.nodes+1)) a x ra)
    dsimp only at rest
    split at rest <;> split at rest
    all_goals
      first
      | have eq := congrArg Prod.fst (Option.some.inj rest)
        change _ = t at eq
        subst t
        exact first.trans (charge a 1 1)
      | obtain ⟨⟨b,y⟩,rb,rest⟩ := bind_some _ _ _ rest
        have eq := congrArg Prod.fst (Option.some.inj rest)
        change _ = t at eq
        subst t
        exact first.trans ((expression_peak right a b y rb).trans (charge b 1 1))
  | size ty c =>
    unfold NExpr.eval at actual
    obtain ⟨⟨a,owner⟩,ra,rest⟩ := bind_some _ _ _ actual
    obtain ⟨⟨frame,x⟩,rf,rest⟩ := bind_some _ _ _ rest
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    have same := Proofs.CppEvalFrame.size_frame a.frame frame owner ty x rf
    have reframed := reframe_raw a frame (by rw [same.1]; exact Nat.le_refl _)
    exact (charge s 0 (c.nodes+2)).trans ((container_peak c _ a owner ra).trans (reframed.trans (charge _ 1 2)))
  | read ty c index =>
    unfold NExpr.eval at actual
    obtain ⟨⟨a,owner⟩,ra,rest⟩ := bind_some _ _ _ actual
    obtain ⟨⟨b,pos⟩,rb,rest⟩ := bind_some _ _ _ rest
    obtain ⟨reference,_,rest⟩ := bind_some _ _ _ rest
    obtain ⟨x,_,rest⟩ := bind_some _ _ _ rest
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    exact (charge s 0 (c.nodes+index.nodes+2)).trans
      ((container_peak c _ a owner ra).trans ((expression_peak index a b pos rb).trans (charge b 1 2)))
termination_by sizeOf e
end

end Proofs.CppEvalPeak
