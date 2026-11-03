import Proofs.DynamicExprCompose
import Proofs.DynamicExprLaws
import Proofs.DynamicFlatSound

namespace Proofs.DynamicExprCertified
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppNestedEval Proofs.CppNestedSim Proofs.CppNestedStmt
open Proofs.MultiVecDynamic Proofs.DynamicContents Proofs.DynamicExpr Proofs.DynamicRealizes
open Proofs.DynamicExprCompose Proofs.DynamicExprLaws

-- Atomic certificates are discharged by the size/read lookup theorems. This
-- interface lets composite proofs share one rule regardless of root layout.
def Atomic (params : List Parameter) (l : Locals) (h : ContentsHeap) (e : NExpr) (v : Int) : Prop :=
  ∀ s, Realizes params l h s → denote params l h e = some v ∧
    ∃ t extra, Ev s e t v extra (2*e.nodes) (2*e.nodes)

inductive Evaluation (params : List Parameter) (l : Locals) (h : ContentsHeap) : NExpr → Int → Prop where
  | scalar (e : NExpr) (v : Int) (scalar : e.scalarOnly = true) (value : e.denote (environment l) = some v) : Evaluation params l h e v
  | atom (e : NExpr) (v : Int) (proved : Atomic params l h e v) : Evaluation params l h e v
  | cast (ty : Ty) (operand : NExpr) (a v : Int) (inner : Evaluation params l h operand a)
      (converted : ty.convert a = some v) : Evaluation params l h (.cast ty operand) v
  | targetCast (ty : Ty) (operand : NExpr) (a v : Int) (inner : Evaluation params l h operand a)
      (converted : ty.targetConvert a = some v) : Evaluation params l h (.targetCast ty operand) v
  | unary (ty : Ty) (op : Unary) (operand : NExpr) (a v : Int) (inner : Evaluation params l h operand a)
      (converted : ty.convert (unaryValue op a) = some v) : Evaluation params l h (.unary ty op operand) v
  | binary (ty : Ty) (op : Binary) (left right : NExpr) (a b v : Int)
      (first : Evaluation params l h left a) (second : Evaluation params l h right b)
      (converted : ty.convert (binaryValue op a b) = some v) : Evaluation params l h (.binary ty op left right) v
  | divrem (ty : Ty) (rem : Bool) (left right : NExpr) (a b v : Int)
      (first : Evaluation params l h left a) (second : Evaluation params l h right b)
      (checked : checkedDivRem ty rem a b = some v) : Evaluation params l h (.divrem ty rem left right) v
  | logicalShort (conj : Bool) (left right : NExpr) (a : Int) (first : Evaluation params l h left a)
      (short : if conj then a = 0 else a ≠ 0) : Evaluation params l h (.logical conj left right) (if conj then 0 else 1)
  | logicalNext (conj : Bool) (left right : NExpr) (a b : Int)
      (first : Evaluation params l h left a) (second : Evaluation params l h right b)
      (cont : if conj then a ≠ 0 else a = 0) : Evaluation params l h (.logical conj left right) (if b = 0 then 0 else 1)

-- The induction covers every scalar composition, including both short-circuit
-- paths. No allocation identity or fixed capacity appears in the statement.
theorem sound {params : List Parameter} {l : Locals} {h : ContentsHeap} {e : NExpr} {v : Int}
    (certificate : Evaluation params l h e v) : Atomic params l h e v := by
  induction certificate with
  | scalar e v scalar value =>
    intro s realizes
    have actualValue : e.denote (envOf s) = some v := by rw [← snapshot_env,realizes.locals]; exact value
    obtain ⟨t,ev⟩ := Ev.scalar scalar actualValue
    exact ⟨by rw [denote_scalar _ _ _ _ scalar]; exact value,t,[],ev.mono (by omega) (by omega)⟩
  | atom e v proved => exact proved
  | cast ty operand a v inner converted ih =>
    intro s realizes
    have rc := in_extension params l h s (s.charge 0 (operand.nodes+1)) realizes (Ext.charge s 0 _)
    obtain ⟨pure,t,extra,ev⟩ := ih _ rc
    have result := Ev.cast ev converted
    refine ⟨by simpa [DynamicExprLaws.cast_eq,pure] using converted,t.charge 1 1,extra,?_⟩
    exact result.mono (by simp [NExpr.nodes]; omega) (by simp [NExpr.nodes]; omega)
  | targetCast ty operand a v inner converted ih =>
    intro s realizes
    have rc := in_extension params l h s (s.charge 0 (operand.nodes+1)) realizes (Ext.charge s 0 _)
    obtain ⟨pure,t,extra,ev⟩ := ih _ rc
    have result := DynamicExprCompose.targetCast ev converted
    refine ⟨by simpa [targetCast_eq,pure] using converted,t.charge 1 1,extra,?_⟩
    exact result.mono (by simp [NExpr.nodes]; omega) (by simp [NExpr.nodes]; omega)
  | unary ty op operand a v inner converted ih =>
    intro s realizes
    have rc := in_extension params l h s (s.charge 0 (operand.nodes+1)) realizes (Ext.charge s 0 _)
    obtain ⟨pure,t,extra,ev⟩ := ih _ rc
    have result := DynamicExprCompose.unary ev converted
    refine ⟨by simpa [unary_eq,pure] using converted,t.charge 1 1,extra,?_⟩
    exact result.mono (by simp [NExpr.nodes]; omega) (by simp [NExpr.nodes]; omega)
  | binary ty op left right a b v first second converted ih1 ih2 =>
    intro s realizes
    let start := s.charge 0 (left.nodes+right.nodes+1)
    have rc := in_extension params l h s start realizes (Ext.charge s 0 _)
    obtain ⟨pure1,t1,extra1,ev1⟩ := ih1 start rc
    have r1 := after_ev params l h start t1 rc left a extra1 _ _ ev1
    obtain ⟨pure2,t2,extra2,ev2⟩ := ih2 t1 r1
    have result := Ev.binary ev1 ev2 converted
    refine ⟨by simpa [binary_eq,pure1,pure2] using converted,t2.charge 1 1,extra1++extra2,?_⟩
    exact result.mono (by simp [NExpr.nodes]; omega) (by simp [NExpr.nodes]; omega)
  | divrem ty rem left right a b v first second checked ih1 ih2 =>
    intro s realizes
    let start := s.charge 0 (left.nodes+right.nodes+1)
    have rc := in_extension params l h s start realizes (Ext.charge s 0 _)
    obtain ⟨pure1,t1,extra1,ev1⟩ := ih1 start rc
    have r1 := after_ev params l h start t1 rc left a extra1 _ _ ev1
    obtain ⟨pure2,t2,extra2,ev2⟩ := ih2 t1 r1
    have result := DynamicExprCompose.divrem ev1 ev2 checked
    refine ⟨by simpa [divrem_eq,pure1,pure2] using checked,t2.charge 1 1,extra1++extra2,?_⟩
    exact result.mono (by simp [NExpr.nodes]; omega) (by simp [NExpr.nodes]; omega)
  | logicalShort conj left right a first short ih =>
    intro s realizes
    let start := s.charge 0 (left.nodes+right.nodes+1)
    have rc := in_extension params l h s start realizes (Ext.charge s 0 _)
    obtain ⟨pure,t,extra,ev⟩ := ih start rc
    have result := logical_short ev short
    refine ⟨?_,t.charge 1 1,extra,?_⟩
    · rw [logical_eq,pure]
      cases conj <;> simp_all
    · exact result.mono (by simp [NExpr.nodes]; omega) (by simp [NExpr.nodes]; omega)
  | logicalNext conj left right a b first second cont ih1 ih2 =>
    intro s realizes
    let start := s.charge 0 (left.nodes+right.nodes+1)
    have rc := in_extension params l h s start realizes (Ext.charge s 0 _)
    obtain ⟨pure1,t1,extra1,ev1⟩ := ih1 start rc
    have r1 := after_ev params l h start t1 rc left a extra1 _ _ ev1
    obtain ⟨pure2,t2,extra2,ev2⟩ := ih2 t1 r1
    have result := logical_next ev1 ev2 cont
    refine ⟨?_,t2.charge 1 1,extra1++extra2,?_⟩
    · rw [logical_eq,pure1]
      cases conj <;> simp_all
    · exact result.mono (by simp [NExpr.nodes]; omega) (by simp [NExpr.nodes]; omega)

theorem released {params : List Parameter} {l : Locals} {h : ContentsHeap} {e : NExpr} {v : Int}
    (certificate : Evaluation params l h e v) (s : NState) (realizes : Realizes params l h s) :
    denote params l h e = some v ∧ ∃ t, e.eval s = some (t,v) ∧
      Realizes params l h ((t.release s).charge 1 0) ∧
      ((t.release s).charge 1 0).work ≤ s.work+2*e.nodes+1 ∧
      ((t.release s).charge 1 0).peak ≤ max s.peak
        (max s.scalars.peak (liveS s+2*e.nodes)+s.frame.state.storage.peak) := by
  obtain ⟨pure,t,extra,ev⟩ := sound certificate s realizes
  obtain ⟨after,_,work,peak⟩ := ev_preserves params l h s t realizes e v extra _ _ ev
  exact ⟨pure,t,ev.1,after,work,peak⟩

end Proofs.DynamicExprCertified
