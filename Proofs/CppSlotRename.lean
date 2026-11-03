import Proofs.CppNestedEval
namespace Proofs.CppSlotRename
open Proofs.CppNestedProgram

mutual
def container (f : Nat → Nat) : Container → Container
  | .local i => .local (f i)
  | .row parent el index => .row (container f parent) el (expr f index)
def expr (f : Nat → Nat) : NExpr → NExpr
  | .literal ty v => .literal ty v
  | .variable ty i => .variable ty (f i)
  | .cast ty e => .cast ty (expr f e)
  | .targetCast ty e => .targetCast ty (expr f e)
  | .unary ty op e => .unary ty op (expr f e)
  | .binary ty op a b => .binary ty op (expr f a) (expr f b)
  | .divrem ty rem a b => .divrem ty rem (expr f a) (expr f b)
  | .logical conj a b => .logical conj (expr f a) (expr f b)
  | .size el c => .size el (container f c)
  | .read ty c i => .read ty (container f c) (expr f i)
end

theorem denote (f : Nat → Nat) (env : Nat → Proofs.CppScalar.Ty → Option Int) :
    ∀ e, (expr f e).denote env = e.denote (fun i ty => env (f i) ty)
  | .literal _ _ => rfl
  | .variable _ _ => rfl
  | .cast _ e => by simp only [expr,NExpr.denote,denote f env e]
  | .targetCast _ e => by simp only [expr,NExpr.denote,denote f env e]
  | .unary _ _ e => by simp only [expr,NExpr.denote,denote f env e]
  | .binary _ _ a b => by simp only [expr,NExpr.denote,denote f env a,denote f env b]
  | .divrem _ _ a b => by simp only [expr,NExpr.denote,denote f env a,denote f env b]
  | .logical _ a b => by simp only [expr,NExpr.denote,denote f env a,denote f env b]
  | .size _ _ => rfl
  | .read _ _ _ => rfl

mutual
theorem container_nodes (f : Nat → Nat) : ∀ c, (container f c).nodes = c.nodes
  | .local _ => rfl
  | .row c _ i => by simp only [container,Container.nodes,container_nodes f c,expr_nodes f i]
theorem expr_nodes (f : Nat → Nat) : ∀ e, (expr f e).nodes = e.nodes
  | .literal _ _ => rfl
  | .variable _ _ => rfl
  | .cast _ e => by simp only [expr,NExpr.nodes,expr_nodes f e]
  | .targetCast _ e => by simp only [expr,NExpr.nodes,expr_nodes f e]
  | .unary _ _ e => by simp only [expr,NExpr.nodes,expr_nodes f e]
  | .binary _ _ a b => by simp only [expr,NExpr.nodes,expr_nodes f a,expr_nodes f b]
  | .divrem _ _ a b => by simp only [expr,NExpr.nodes,expr_nodes f a,expr_nodes f b]
  | .logical _ a b => by simp only [expr,NExpr.nodes,expr_nodes f a,expr_nodes f b]
  | .size _ c => by simp only [expr,NExpr.nodes,container_nodes f c]
  | .read _ c i => by simp only [expr,NExpr.nodes,container_nodes f c,expr_nodes f i]
end

theorem scalarOnly (f : Nat → Nat) : ∀ e, (expr f e).scalarOnly = e.scalarOnly
  | .literal _ _ => rfl
  | .variable _ _ => rfl
  | .cast _ e => by simp only [expr,NExpr.scalarOnly,scalarOnly f e]
  | .targetCast _ e => by simp only [expr,NExpr.scalarOnly,scalarOnly f e]
  | .unary _ _ e => by simp only [expr,NExpr.scalarOnly,scalarOnly f e]
  | .binary _ _ a b => by simp only [expr,NExpr.scalarOnly,scalarOnly f a,scalarOnly f b]
  | .divrem _ _ a b => by simp only [expr,NExpr.scalarOnly,scalarOnly f a,scalarOnly f b]
  | .logical _ a b => by simp only [expr,NExpr.scalarOnly,scalarOnly f a,scalarOnly f b]
  | .size _ _ => rfl
  | .read _ _ _ => rfl
end Proofs.CppSlotRename
