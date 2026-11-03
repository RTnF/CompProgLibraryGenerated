import Proofs.CppEvalFrame

namespace Proofs.CppEvalScope
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings Proofs.DynamicResultValid

mutual
theorem container_scope (c : Container) (s t : NState) (value : Nat)
    (actual : c.eval s = some (t,value)) : t.scope = s.scope := by
  cases c with
  | «local» slot =>
    unfold Container.eval at actual
    obtain ⟨binding,_,rest⟩ := bind_some _ _ _ actual
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    rfl
  | row parent ty index =>
    unfold Container.eval at actual
    obtain ⟨⟨a,owner⟩,ra,rest⟩ := bind_some _ _ _ actual
    obtain ⟨⟨b,pos⟩,rb,rest⟩ := bind_some _ _ _ rest
    obtain ⟨⟨frame,binding⟩,rf,rest⟩ := bind_some _ _ _ rest
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    exact (expression_scope index a b pos rb).trans (container_scope parent (s.charge 0 (parent.nodes+index.nodes+1)) a owner ra)
termination_by sizeOf c

theorem expression_scope (e : NExpr) (s t : NState) (value : Int)
    (actual : e.eval s = some (t,value)) : t.scope = s.scope := by
  cases e with
  | literal ty v =>
    unfold NExpr.eval at actual
    split at actual
    · have eq := congrArg Prod.fst (Option.some.inj actual)
      change _ = t at eq
      subst t
      rfl
    · simp at actual
  | «variable» ty slot =>
    unfold NExpr.eval at actual
    obtain ⟨cell,_,rest⟩ := bind_some _ _ _ actual
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    rfl
  | cast ty operand | targetCast ty operand | unary ty _ operand =>
    unfold NExpr.eval at actual
    obtain ⟨⟨a,x⟩,ra,rest⟩ := bind_some _ _ _ actual
    obtain ⟨x,_,rest⟩ := bind_some _ _ _ rest
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    exact expression_scope operand (s.charge 0 (operand.nodes+1)) a _ ra
  | binary ty _ left right | divrem ty _ left right =>
    unfold NExpr.eval at actual
    obtain ⟨⟨a,x⟩,ra,rest⟩ := bind_some _ _ _ actual
    obtain ⟨⟨b,y⟩,rb,rest⟩ := bind_some _ _ _ rest
    obtain ⟨z,_,rest⟩ := bind_some _ _ _ rest
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    exact (expression_scope right a b y rb).trans (expression_scope left (s.charge 0 (left.nodes+right.nodes+1)) a x ra)
  | logical conjunction left right =>
    unfold NExpr.eval at actual
    obtain ⟨⟨a,x⟩,ra,rest⟩ := bind_some _ _ _ actual
    have first := expression_scope left (s.charge 0 (left.nodes+right.nodes+1)) a x ra
    dsimp only at rest
    split at rest <;> split at rest
    all_goals
      first
      | have eq := congrArg Prod.fst (Option.some.inj rest)
        change _ = t at eq
        subst t
        exact first
      | obtain ⟨⟨b,y⟩,rb,rest⟩ := bind_some _ _ _ rest
        have eq := congrArg Prod.fst (Option.some.inj rest)
        change _ = t at eq
        subst t
        exact (expression_scope right a b y rb).trans first
  | size ty c =>
    unfold NExpr.eval at actual
    obtain ⟨⟨a,owner⟩,ra,rest⟩ := bind_some _ _ _ actual
    obtain ⟨⟨frame,x⟩,rf,rest⟩ := bind_some _ _ _ rest
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    exact container_scope c (s.charge 0 (c.nodes+2)) a owner ra
  | read ty c index =>
    unfold NExpr.eval at actual
    obtain ⟨⟨a,owner⟩,ra,rest⟩ := bind_some _ _ _ actual
    obtain ⟨⟨b,pos⟩,rb,rest⟩ := bind_some _ _ _ rest
    obtain ⟨reference,_,rest⟩ := bind_some _ _ _ rest
    obtain ⟨x,_,rest⟩ := bind_some _ _ _ rest
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    exact (expression_scope index a b pos rb).trans (container_scope c (s.charge 0 (c.nodes+index.nodes+2)) a owner ra)
termination_by sizeOf e
end

end Proofs.CppEvalScope
