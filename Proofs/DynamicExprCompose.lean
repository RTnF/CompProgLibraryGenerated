import Proofs.DynamicRealizes

namespace Proofs.DynamicExprCompose
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppNestedEval Proofs.CppNestedSim Proofs.CppNestedStmt
open Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic
open Proofs.DynamicContents Proofs.DynamicExpr Proofs.DynamicRealizes

-- Intermediate expression states may retain reference temporaries. They
-- preserve scalar locals, object contents, and all original parameter grants.
theorem in_extension (params : List Parameter) (locals : Locals) (contents : ContentsHeap)
    (s u : NState) (realizes : Realizes params locals contents s) (ext : Ext s u) :
    Realizes params locals contents u := by
  obtain ⟨h,m,family,he⟩ := realizes.heap
  obtain ⟨state,rights,⟨extra,bindings⟩,slots,scope,memory,scalarBindings,base⟩ := ext
  refine ⟨?_,h,m,family.transport u.frame state rights ?_,he⟩
  · have eq : snapshot u = snapshot s := by simp [snapshot,memory,scalarBindings,slots]
    exact eq.trans realizes.locals
  · intro p hp
    rw [bindings,List.getElem?_append_left (List.getElem?_eq_some_iff.mp (family.bindings p hp)).1]
    exact family.bindings p hp

theorem after_ev (params : List Parameter) (locals : Locals) (contents : ContentsHeap)
    (s t : NState) (realizes : Realizes params locals contents s) (e : NExpr) (v : Int)
    (extra : List Binding) (w p : Nat) (ev : Ev s e t v extra w p) :
    Realizes params locals contents t :=
  in_extension params locals contents s t realizes (Ext.of_goodF ev.2.1 ev.2.2)

-- Target casts and checked arithmetic use the same C++ scalar operations as
-- the source model, including failure on undefined signed operations.
theorem targetCast {ty : Ty} {operand : NExpr} {s t : NState} {v v' : Int}
    {extra : List Binding} {w p : Nat}
    (inner : Ev (s.charge 0 (operand.nodes+1)) operand t v extra w p)
    (converted : ty.targetConvert v = some v') :
    Ev s (.targetCast ty operand) (t.charge 1 1) v' extra (w+1) (max (operand.nodes+1) (max p 1)) := by
  refine ⟨by simp [NExpr.eval,inner.1,converted],?_,by simpa using inner.2.2⟩
  have good := (GoodF.charge s 0 (operand.nodes+1)).trans (inner.2.1.trans (GoodF.charge t 1 1))
  exact good.mono (by omega) (by omega)

theorem unary {ty : Ty} {op : Unary} {operand : NExpr} {s t : NState} {v v' : Int}
    {extra : List Binding} {w p : Nat}
    (inner : Ev (s.charge 0 (operand.nodes+1)) operand t v extra w p)
    (converted : ty.convert (unaryValue op v) = some v') :
    Ev s (.unary ty op operand) (t.charge 1 1) v' extra (w+1) (max (operand.nodes+1) (max p 1)) := by
  refine ⟨by simp [NExpr.eval,inner.1,converted],?_,by simpa using inner.2.2⟩
  have good := (GoodF.charge s 0 (operand.nodes+1)).trans (inner.2.1.trans (GoodF.charge t 1 1))
  exact good.mono (by omega) (by omega)

theorem divrem {ty : Ty} {rem : Bool} {left right : NExpr} {s t1 t2 : NState} {a b v : Int}
    {extra1 extra2 : List Binding} {w1 p1 w2 p2 : Nat}
    (first : Ev (s.charge 0 (left.nodes+right.nodes+1)) left t1 a extra1 w1 p1)
    (second : Ev t1 right t2 b extra2 w2 p2) (checked : checkedDivRem ty rem a b = some v) :
    Ev s (.divrem ty rem left right) (t2.charge 1 1) v (extra1 ++ extra2)
      (w1+w2+1) (max (left.nodes+right.nodes+1) (max (max p1 p2) 1)) := by
  refine ⟨by simp [NExpr.eval,first.1,second.1,checked],?_,?_⟩
  have good := (GoodF.charge s 0 (left.nodes+right.nodes+1)).trans
    (first.2.1.trans (second.2.1.trans (GoodF.charge t2 1 1)))
  exact good.mono (by omega) (by omega)
  simp only [charge_frame_bindings]
  rw [second.2.2,first.2.2,List.append_assoc]
  rfl

theorem logical_short {conj : Bool} {left right : NExpr} {s t : NState} {a : Int}
    {extra : List Binding} {w p : Nat}
    (first : Ev (s.charge 0 (left.nodes+right.nodes+1)) left t a extra w p)
    (short : if conj then a = 0 else a ≠ 0) :
    Ev s (.logical conj left right) (t.charge 1 1) (if conj then 0 else 1) extra
      (w+1) (max (left.nodes+right.nodes+1) (max p 1)) := by
  refine ⟨?_,?_,by simpa using first.2.2⟩
  · have eval1 := first.1
    cases conj <;> simp_all [NExpr.eval]
  · have good := (GoodF.charge s 0 (left.nodes+right.nodes+1)).trans (first.2.1.trans (GoodF.charge t 1 1))
    exact good.mono (by omega) (by omega)

theorem logical_next {conj : Bool} {left right : NExpr} {s t1 t2 : NState} {a b : Int}
    {extra1 extra2 : List Binding} {w1 p1 w2 p2 : Nat}
    (first : Ev (s.charge 0 (left.nodes+right.nodes+1)) left t1 a extra1 w1 p1)
    (second : Ev t1 right t2 b extra2 w2 p2)
    (cont : if conj then a ≠ 0 else a = 0) :
    Ev s (.logical conj left right) (t2.charge 1 1) (if b = 0 then 0 else 1) (extra1 ++ extra2)
      (w1+w2+1) (max (left.nodes+right.nodes+1) (max (max p1 p2) 1)) := by
  refine ⟨?_,?_,?_⟩
  · have eval1 := first.1
    have eval2 := second.1
    cases conj <;> simp_all [NExpr.eval]
  · have good := (GoodF.charge s 0 (left.nodes+right.nodes+1)).trans
      (first.2.1.trans (second.2.1.trans (GoodF.charge t2 1 1)))
    exact good.mono (by omega) (by omega)
  · simp only [charge_frame_bindings]
    rw [second.2.2,first.2.2,List.append_assoc]
    rfl

end Proofs.DynamicExprCompose
