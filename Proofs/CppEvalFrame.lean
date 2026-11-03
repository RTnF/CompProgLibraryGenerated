import Proofs.CppBufferHeaders
import Proofs.DynamicResultValid

set_option maxRecDepth 4000

namespace Proofs.CppEvalFrame
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppVectorOwnership Proofs.DynamicResultValid

def FrameSame (f g : Frame) : Prop := g.state = f.state ∧ g.rootWritable = f.rootWritable
theorem FrameSame.trans {a b c : Frame} (x : FrameSame a b) (y : FrameSame b c) : FrameSame a c :=
  ⟨y.1.trans x.1,y.2.trans x.2⟩

theorem child_frame (f g : Frame) (slot : Nat) (ty : Element) (index : Int) (binding : Nat)
    (actual : f.child slot ty index = some (g,binding)) : FrameSame f g := by
  unfold Frame.child at actual
  obtain ⟨⟨origin,parent⟩,_,rest⟩ := bind_some _ _ _ actual
  unfold Frame.bindChild at rest
  obtain ⟨⟨origin,parent⟩,_,rest⟩ := bind_some _ _ _ rest
  dsimp only at rest
  split at rest
  · obtain ⟨address,_,rest⟩ := bind_some _ _ _ rest
    obtain ⟨result,_,rest⟩ := bind_some _ _ _ rest
    cases value : result.value with
    | integer x => simp [value] at rest
    | child owner =>
      simp only [value] at rest
      obtain ⟨⟨object,tag⟩,_,rest⟩ := bind_some _ _ _ rest
      dsimp only at rest
      split at rest
      · have eq := congrArg Prod.fst (Option.some.inj rest)
        change _ = g at eq
        subst g
        exact ⟨rfl,rfl⟩
      · simp at rest
  · simp at rest

theorem size_frame (f g : Frame) (slot : Nat) (ty : Element) (value : Int)
    (actual : f.size slot ty = some (g,value)) : FrameSame f g := by
  unfold Frame.size at actual
  obtain ⟨⟨binding,buffer⟩,_,rest⟩ := bind_some _ _ _ actual
  dsimp only at rest
  split at rest
  · have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = g at eq
    subst g
    exact ⟨rfl,rfl⟩
  · simp at rest

mutual
theorem container_frame (c : Container) (s t : NState) (value : Nat)
    (actual : c.eval s = some (t,value)) : FrameSame s.frame t.frame := by
  cases c with
  | «local» slot =>
    unfold Container.eval at actual
    obtain ⟨binding,_,rest⟩ := bind_some _ _ _ actual
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    exact ⟨rfl,rfl⟩
  | row parent ty index =>
    unfold Container.eval at actual
    obtain ⟨⟨a,owner⟩,ra,rest⟩ := bind_some _ _ _ actual
    obtain ⟨⟨b,pos⟩,rb,rest⟩ := bind_some _ _ _ rest
    obtain ⟨⟨frame,binding⟩,rf,rest⟩ := bind_some _ _ _ rest
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    exact (container_frame parent _ a owner ra).trans ((expression_frame index a b pos rb).trans
      (child_frame b.frame frame owner ty pos binding rf))
termination_by sizeOf c

theorem expression_frame (e : NExpr) (s t : NState) (value : Int)
    (actual : e.eval s = some (t,value)) : FrameSame s.frame t.frame := by
  cases e with
  | literal ty v =>
    unfold NExpr.eval at actual
    split at actual
    · have eq := congrArg Prod.fst (Option.some.inj actual)
      change _ = t at eq
      subst t
      exact ⟨rfl,rfl⟩
    · simp at actual
  | «variable» ty slot =>
    unfold NExpr.eval at actual
    obtain ⟨cell,_,rest⟩ := bind_some _ _ _ actual
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    exact ⟨rfl,rfl⟩
  | cast ty operand | targetCast ty operand | unary ty _ operand =>
    unfold NExpr.eval at actual
    obtain ⟨⟨a,x⟩,ra,rest⟩ := bind_some _ _ _ actual
    obtain ⟨x,_,rest⟩ := bind_some _ _ _ rest
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    exact expression_frame operand (s.charge 0 (operand.nodes+1)) a _ ra
  | binary ty _ left right | divrem ty _ left right =>
    unfold NExpr.eval at actual
    obtain ⟨⟨a,x⟩,ra,rest⟩ := bind_some _ _ _ actual
    obtain ⟨⟨b,y⟩,rb,rest⟩ := bind_some _ _ _ rest
    obtain ⟨z,_,rest⟩ := bind_some _ _ _ rest
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    exact (expression_frame left (s.charge 0 (left.nodes+right.nodes+1)) a x ra).trans (expression_frame right a b y rb)
  | logical conjunction left right =>
    unfold NExpr.eval at actual
    obtain ⟨⟨a,x⟩,ra,rest⟩ := bind_some _ _ _ actual
    have first := expression_frame left (s.charge 0 (left.nodes+right.nodes+1)) a x ra
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
        exact first.trans (expression_frame right a b y rb)
  | size ty c =>
    unfold NExpr.eval at actual
    obtain ⟨⟨a,owner⟩,ra,rest⟩ := bind_some _ _ _ actual
    obtain ⟨⟨frame,x⟩,rf,rest⟩ := bind_some _ _ _ rest
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    exact (container_frame c _ a owner ra).trans (size_frame a.frame frame owner ty x rf)
  | read ty c index =>
    unfold NExpr.eval at actual
    obtain ⟨⟨a,owner⟩,ra,rest⟩ := bind_some _ _ _ actual
    obtain ⟨⟨b,pos⟩,rb,rest⟩ := bind_some _ _ _ rest
    obtain ⟨reference,_,rest⟩ := bind_some _ _ _ rest
    obtain ⟨x,_,rest⟩ := bind_some _ _ _ rest
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    exact (container_frame c _ a owner ra).trans (expression_frame index a b pos rb)
termination_by sizeOf e
end

end Proofs.CppEvalFrame
