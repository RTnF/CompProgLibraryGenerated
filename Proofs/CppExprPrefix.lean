import Proofs.CppEvalFrame

set_option maxRecDepth 4000
namespace Proofs.CppExprPrefix
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings Proofs.CppVectorOwnership
open Proofs.DynamicResultValid

def Prefix (s t : NState) : Prop := t.slots = s.slots ∧ ∃ extra, t.frame.bindings = s.frame.bindings++extra

theorem Prefix.trans {a b c : NState} (x : Prefix a b) (y : Prefix b c) : Prefix a c := by
  obtain ⟨extra1,bindings1⟩ := x.2
  obtain ⟨extra2,bindings2⟩ := y.2
  refine ⟨y.1.trans x.1,extra1++extra2,?_⟩
  rw [bindings2,bindings1,List.append_assoc]

theorem child_prefix (f g : Frame) (slot : Nat) (ty : Element) (index : Int) (binding : Nat)
    (actual : f.child slot ty index = some (g,binding)) : ∃ extra, g.bindings = f.bindings++extra := by
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
        exact ⟨_,rfl⟩
      · simp at rest
  · simp at rest

theorem size_eq (f g : Frame) (slot : Nat) (ty : Element) (value : Int)
    (actual : f.size slot ty = some (g,value)) : g = f := by
  unfold Frame.size at actual
  obtain ⟨⟨binding,buffer⟩,_,rest⟩ := bind_some _ _ _ actual
  dsimp only at rest
  split at rest
  · have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = g at eq
    subst g
    rfl
  · simp at rest

mutual
theorem container_prefix (c : Container) (s t : NState) (value : Nat)
    (actual : c.eval s = some (t,value)) : Prefix s t := by
  cases c with
  | «local» slot =>
    unfold Container.eval at actual
    obtain ⟨binding,_,rest⟩ := bind_some _ _ _ actual
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    exact ⟨rfl,[],by simp⟩
  | row parent ty index =>
    unfold Container.eval at actual
    obtain ⟨⟨a,owner⟩,ra,rest⟩ := bind_some _ _ _ actual
    obtain ⟨⟨b,pos⟩,rb,rest⟩ := bind_some _ _ _ rest
    obtain ⟨⟨frame,binding⟩,rf,rest⟩ := bind_some _ _ _ rest
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    have previous := (container_prefix parent _ a owner ra).trans (expression_prefix index a b pos rb)
    obtain ⟨extra,prior⟩ := previous.2
    obtain ⟨new,following⟩ := child_prefix b.frame frame owner ty pos binding rf
    refine ⟨previous.1,extra++new,?_⟩
    change b.frame.bindings = s.frame.bindings++extra at prior
    change frame.bindings = s.frame.bindings++(extra++new)
    rw [following,prior,List.append_assoc]
termination_by sizeOf c

theorem expression_prefix (e : NExpr) (s t : NState) (value : Int)
    (actual : e.eval s = some (t,value)) : Prefix s t := by
  cases e with
  | literal ty v =>
    unfold NExpr.eval at actual
    split at actual
    · have eq := congrArg Prod.fst (Option.some.inj actual)
      change _ = t at eq
      subst t
      exact ⟨rfl,[],by simp⟩
    · simp at actual
  | «variable» ty slot =>
    unfold NExpr.eval at actual
    obtain ⟨cell,_,rest⟩ := bind_some _ _ _ actual
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    exact ⟨rfl,[],by simp⟩
  | cast ty operand | targetCast ty operand | unary ty _ operand =>
    unfold NExpr.eval at actual
    obtain ⟨⟨a,x⟩,ra,rest⟩ := bind_some _ _ _ actual
    obtain ⟨x,_,rest⟩ := bind_some _ _ _ rest
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    exact expression_prefix operand (s.charge 0 (operand.nodes+1)) a _ ra
  | binary ty _ left right | divrem ty _ left right =>
    unfold NExpr.eval at actual
    obtain ⟨⟨a,x⟩,ra,rest⟩ := bind_some _ _ _ actual
    obtain ⟨⟨b,y⟩,rb,rest⟩ := bind_some _ _ _ rest
    obtain ⟨z,_,rest⟩ := bind_some _ _ _ rest
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    exact (expression_prefix left (s.charge 0 (left.nodes+right.nodes+1)) a x ra).trans (expression_prefix right a b y rb)
  | logical conjunction left right =>
    unfold NExpr.eval at actual
    obtain ⟨⟨a,x⟩,ra,rest⟩ := bind_some _ _ _ actual
    have first := expression_prefix left (s.charge 0 (left.nodes+right.nodes+1)) a x ra
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
        exact first.trans (expression_prefix right a b y rb)
  | size ty c =>
    unfold NExpr.eval at actual
    obtain ⟨⟨a,owner⟩,ra,rest⟩ := bind_some _ _ _ actual
    obtain ⟨⟨frame,x⟩,rf,rest⟩ := bind_some _ _ _ rest
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    have same := size_eq a.frame frame owner ty x rf
    subst frame
    exact container_prefix c (s.charge 0 (c.nodes+2)) a owner ra
  | read ty c index =>
    unfold NExpr.eval at actual
    obtain ⟨⟨a,owner⟩,ra,rest⟩ := bind_some _ _ _ actual
    obtain ⟨⟨b,pos⟩,rb,rest⟩ := bind_some _ _ _ rest
    obtain ⟨reference,_,rest⟩ := bind_some _ _ _ rest
    obtain ⟨x,_,rest⟩ := bind_some _ _ _ rest
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    exact (container_prefix c _ a owner ra).trans (expression_prefix index a b pos rb)
termination_by sizeOf e
end


theorem release_bindings (s t : NState) (prefixEq : Prefix s t) : (t.release s).frame.bindings = s.frame.bindings := by
  obtain ⟨extra,bindings⟩ := prefixEq.2
  change t.frame.bindings.take s.frame.bindings.length = s.frame.bindings
  simp [bindings]

theorem release_frame (e : NExpr) (s t : NState) (value : Int) (actual : e.eval s = some (t,value)) :
    (t.release s).frame = s.frame := by
  have frame := Proofs.CppEvalFrame.expression_frame e s t value actual
  have bindings := release_bindings s t (expression_prefix e s t value actual)
  change t.frame.bindings.take s.frame.bindings.length = s.frame.bindings at bindings
  change (⟨t.frame.state,t.frame.rootWritable,t.frame.bindings.take s.frame.bindings.length⟩ : Frame) = s.frame
  rw [frame.1,frame.2,bindings]

end Proofs.CppExprPrefix
