import Proofs.CppNestedHoare

namespace Proofs.CppNestedEval
open Proofs.CppScalar Proofs.CppMixedInvoke Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedSim

-- Expressions without vector access: only literals, scalar variables and
-- arithmetic. Their evaluation changes counters and nothing else.
def _root_.Proofs.CppNestedProgram.NExpr.scalarOnly : NExpr → Bool
  | .literal _ _ | .variable _ _ => true
  | .cast _ e | .targetCast _ e | .unary _ _ e => e.scalarOnly
  | .binary _ _ a b | .divrem _ _ a b | .logical _ a b => a.scalarOnly && b.scalarOnly
  | .size _ _ | .read _ _ _ => false

-- The core of a state: everything except work and peak counters.
def Core (s t : NState) : Prop :=
  t.frame = s.frame ∧ t.slots = s.slots ∧ t.scope = s.scope ∧
  t.scalars.memory = s.scalars.memory ∧ t.scalars.bindings = s.scalars.bindings ∧
  t.scalars.baseMemory = s.scalars.baseMemory

theorem Core.refl (s : NState) : Core s s := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
theorem Core.trans {a b c : NState} (x : Core a b) (y : Core b c) : Core a c := by
  obtain ⟨f1,s1,c1,m1,b1,k1⟩ := x
  obtain ⟨f2,s2,c2,m2,b2,k2⟩ := y
  exact ⟨f2.trans f1,s2.trans s1,c2.trans c1,m2.trans m1,b2.trans b1,k2.trans k1⟩
theorem core_charge (s : NState) (work temporaries : Nat) : Core s (s.charge work temporaries) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

def liveS (s : NState) : Nat := s.scalars.memory.length-s.scalars.baseMemory+s.scalars.bindings.length

-- Scalar work grows by at most `w`; the scalar peak by at most live cells + `p`.
def Good (s t : NState) (w p : Nat) : Prop :=
  Core s t ∧ s.scalars.work ≤ t.scalars.work ∧ t.scalars.work ≤ s.scalars.work+w ∧
  t.frame.state.storage = s.frame.state.storage ∧ s.scalars.peak ≤ t.scalars.peak ∧
  t.scalars.peak ≤ max s.scalars.peak (liveS s+p) ∧
  s.peak ≤ t.peak ∧ t.peak ≤ max s.peak (t.scalars.peak+t.frame.state.storage.peak)

theorem liveS_core {s t : NState} (core : Core s t) : liveS t = liveS s := by
  obtain ⟨_,_,_,m,b,k⟩ := core
  simp [liveS,m,b,k]

theorem Good.refl (s : NState) : Good s s 0 0 :=
  ⟨Core.refl s,Nat.le_refl _,by omega,rfl,Nat.le_refl _,Nat.le_max_left _ _,Nat.le_refl _,Nat.le_max_left _ _⟩

theorem Good.charge (s : NState) (work temporaries : Nat) : Good s (s.charge work temporaries) work temporaries := by
  refine ⟨core_charge s work temporaries,?_,?_,rfl,?_,?_,?_,?_⟩
  · simp [charge_work]
  · simp [charge_work]
  · simp only [charge_scalar_peak]; omega
  · simp only [charge_scalar_peak,liveS]; omega
  · simp only [charge_peak]; omega
  · simp only [charge_peak,charge_scalar_peak,charge_storage]; omega

theorem Good.mono {s t : NState} {w p w' p' : Nat} (good : Good s t w p) (hw : w ≤ w') (hp : p ≤ p') :
    Good s t w' p' := by
  obtain ⟨core,l,u,storage,pl,pu,ql,qu⟩ := good
  exact ⟨core,l,by omega,storage,pl,by omega,ql,qu⟩

theorem Good.trans {a b c : NState} {w1 p1 w2 p2 : Nat} (x : Good a b w1 p1) (y : Good b c w2 p2) :
    Good a c (w1+w2) (max p1 p2) := by
  obtain ⟨core1,l1,u1,st1,pl1,pu1,ql1,qu1⟩ := x
  obtain ⟨core2,l2,u2,st2,pl2,pu2,ql2,qu2⟩ := y
  have live : liveS b = liveS a := liveS_core core1
  rw [live] at pu2
  have storage : c.frame.state.storage.peak = a.frame.state.storage.peak := by
    rw [st2,st1]
  have storageB : b.frame.state.storage.peak = a.frame.state.storage.peak := by rw [st1]
  exact ⟨core1.trans core2,by omega,by omega,st2.trans st1,by omega,by omega,by omega,by omega⟩

theorem good_work {s t : NState} {w p : Nat} (good : Good s t w p) :
    t.scalars.work ≤ s.scalars.work+w := good.2.2.1

theorem eval_scalar : ∀ (e : NExpr) (s t : NState) (v : Int), e.scalarOnly = true →
    e.eval s = some (t,v) → Good s t e.nodes e.nodes
  | .literal ty value, s, t, v, _, ran => by
      simp only [NExpr.eval] at ran
      split at ran
      · simp at ran
        obtain ⟨rfl,_⟩ := ran
        exact Good.charge s 1 1
      · simp at ran
  | .variable ty slot, s, t, v, _, ran => by
      simp only [NExpr.eval] at ran
      cases cell : s.scalarCell slot ty with
      | none => simp [cell] at ran
      | some pair =>
        simp [cell] at ran
        obtain ⟨rfl,_⟩ := ran
        exact Good.charge s 1 1
  | .cast ty operand, s, t, v, hs, ran => by
      have inner : operand.scalarOnly = true := by simpa [NExpr.scalarOnly] using hs
      simp only [NExpr.eval] at ran
      cases h : operand.eval (s.charge 0 (operand.nodes+1)) with
      | none => simp [h] at ran
      | some pair =>
        rcases pair with ⟨next,u⟩
        have g := eval_scalar operand _ _ _ inner h
        simp only [h] at ran
        cases c : ty.convert u with
        | none => simp [c] at ran
        | some converted =>
          simp [c] at ran
          obtain ⟨rfl,_⟩ := ran
          have all := ((Good.charge s 0 (operand.nodes+1)).trans g).trans (Good.charge next 1 1)
          exact all.mono (by simp [NExpr.nodes] <;> omega) (by simp [NExpr.nodes] <;> omega)
  | .targetCast ty operand, s, t, v, hs, ran => by
      have inner : operand.scalarOnly = true := by simpa [NExpr.scalarOnly] using hs
      simp only [NExpr.eval] at ran
      cases h : operand.eval (s.charge 0 (operand.nodes+1)) with
      | none => simp [h] at ran
      | some pair =>
        rcases pair with ⟨next,u⟩
        have g := eval_scalar operand _ _ _ inner h
        simp only [h] at ran
        cases c : ty.targetConvert u with
        | none => simp [c] at ran
        | some converted =>
          simp [c] at ran
          obtain ⟨rfl,_⟩ := ran
          have all := ((Good.charge s 0 (operand.nodes+1)).trans g).trans (Good.charge next 1 1)
          exact all.mono (by simp [NExpr.nodes] <;> omega) (by simp [NExpr.nodes] <;> omega)
  | .unary ty op operand, s, t, v, hs, ran => by
      have inner : operand.scalarOnly = true := by simpa [NExpr.scalarOnly] using hs
      simp only [NExpr.eval] at ran
      cases h : operand.eval (s.charge 0 (operand.nodes+1)) with
      | none => simp [h] at ran
      | some pair =>
        rcases pair with ⟨next,u⟩
        have g := eval_scalar operand _ _ _ inner h
        simp only [h] at ran
        cases c : ty.convert (unaryValue op u) with
        | none => simp [c] at ran
        | some converted =>
          simp [c] at ran
          obtain ⟨rfl,_⟩ := ran
          have all := ((Good.charge s 0 (operand.nodes+1)).trans g).trans (Good.charge next 1 1)
          exact all.mono (by simp [NExpr.nodes] <;> omega) (by simp [NExpr.nodes] <;> omega)
  | .binary ty op left right, s, t, v, hs, ran => by
      have inner : left.scalarOnly = true ∧ right.scalarOnly = true := by simpa [NExpr.scalarOnly] using hs
      simp only [NExpr.eval] at ran
      cases h1 : left.eval (s.charge 0 (left.nodes+right.nodes+1)) with
      | none => simp [h1] at ran
      | some first =>
        rcases first with ⟨next,a⟩
        have g1 := eval_scalar left _ _ _ inner.1 h1
        simp only [h1,Bind.bind,Option.bind] at ran
        cases h2 : right.eval next with
        | none => simp [h2] at ran
        | some second =>
          rcases second with ⟨last,b⟩
          have g2 := eval_scalar right _ _ _ inner.2 h2
          simp only [h2,Bind.bind,Option.bind] at ran
          cases c : ty.convert (binaryValue op a b) with
          | none => simp [c] at ran
          | some converted =>
            simp [c] at ran
            obtain ⟨rfl,_⟩ := ran
            have all := (((Good.charge s 0 (left.nodes+right.nodes+1)).trans g1).trans g2).trans (Good.charge last 1 1)
            exact all.mono (by simp [NExpr.nodes] <;> omega) (by simp [NExpr.nodes] <;> omega)
  | .divrem ty remainder left right, s, t, v, hs, ran => by
      have inner : left.scalarOnly = true ∧ right.scalarOnly = true := by simpa [NExpr.scalarOnly] using hs
      simp only [NExpr.eval] at ran
      cases h1 : left.eval (s.charge 0 (left.nodes+right.nodes+1)) with
      | none => simp [h1] at ran
      | some first =>
        rcases first with ⟨next,a⟩
        have g1 := eval_scalar left _ _ _ inner.1 h1
        simp only [h1,Bind.bind,Option.bind] at ran
        cases h2 : right.eval next with
        | none => simp [h2] at ran
        | some second =>
          rcases second with ⟨last,b⟩
          have g2 := eval_scalar right _ _ _ inner.2 h2
          simp only [h2,Bind.bind,Option.bind] at ran
          cases c : checkedDivRem ty remainder a b with
          | none => simp [c] at ran
          | some converted =>
            simp [c] at ran
            obtain ⟨rfl,_⟩ := ran
            have all := (((Good.charge s 0 (left.nodes+right.nodes+1)).trans g1).trans g2).trans (Good.charge last 1 1)
            exact all.mono (by simp [NExpr.nodes] <;> omega) (by simp [NExpr.nodes] <;> omega)
  | .logical conjunction left right, s, t, v, hs, ran => by
      have inner : left.scalarOnly = true ∧ right.scalarOnly = true := by simpa [NExpr.scalarOnly] using hs
      simp only [NExpr.eval] at ran
      cases h1 : left.eval (s.charge 0 (left.nodes+right.nodes+1)) with
      | none => simp [h1] at ran
      | some first =>
        rcases first with ⟨next,a⟩
        have g1 := (Good.charge s 0 (left.nodes+right.nodes+1)).trans (eval_scalar left _ _ _ inner.1 h1)
        simp only [h1,Bind.bind,Option.bind] at ran
        have short : Good s (next.charge 1 1) (left.nodes+right.nodes+1) (left.nodes+right.nodes+1) :=
          (g1.trans (Good.charge next 1 1)).mono (by omega) (by omega)
        have long : ∀ (last : NState) (b : Int), right.eval next = some (last,b) →
            Good s (last.charge 1 1) (left.nodes+right.nodes+1) (left.nodes+right.nodes+1) := by
          intro last b h2
          have g2 := eval_scalar right _ _ _ inner.2 h2
          exact ((g1.trans g2).trans (Good.charge last 1 1)).mono (by omega) (by omega)
        have total : Good s t (NExpr.logical conjunction left right).nodes
            (NExpr.logical conjunction left right).nodes ↔
            Good s t (left.nodes+right.nodes+1) (left.nodes+right.nodes+1) := by simp [NExpr.nodes]
        rw [total]
        cases conjunction <;> cases z : (a == 0) <;>
          first
          | (simp [z] at ran; obtain ⟨rfl,_⟩ := ran; exact short)
          | (cases h2 : right.eval next with
             | none => simp [z,h2] at ran
             | some second =>
               rcases second with ⟨last,b⟩
               simp [z,h2] at ran
               obtain ⟨rfl,_⟩ := ran
               exact long last b h2)
  | .size _ _, _, _, _, hs, _ => by simp [NExpr.scalarOnly] at hs
  | .read _ _ _, _, _, _, hs, _ => by simp [NExpr.scalarOnly] at hs

-- Pure meaning of a scalar expression in the environment of declared locals.
def envOf (s : NState) (slot : Nat) (ty : Ty) : Option Int :=
  (s.scalarCell slot ty).map fun pair => pair.2.value

theorem envOf_core {s t : NState} (core : Core s t) : envOf t = envOf s := by
  obtain ⟨_,slots,_,memory,bindings,_⟩ := core
  funext slot ty
  simp [envOf,NState.scalarCell,NState.scalarSlot,slots,memory,bindings]

def _root_.Proofs.CppNestedProgram.NExpr.denote (env : Nat → Ty → Option Int) : NExpr → Option Int
  | .literal ty value => if ty.valid value then some value else none
  | .variable ty slot => env slot ty
  | .cast ty operand => (operand.denote env).bind ty.convert
  | .targetCast ty operand => (operand.denote env).bind ty.targetConvert
  | .unary ty op operand => (operand.denote env).bind fun value => ty.convert (unaryValue op value)
  | .binary ty op left right => (left.denote env).bind fun a => (right.denote env).bind fun b =>
      ty.convert (binaryValue op a b)
  | .divrem ty remainder left right => (left.denote env).bind fun a => (right.denote env).bind fun b =>
      checkedDivRem ty remainder a b
  | .logical conjunction left right => (left.denote env).bind fun a =>
      if conjunction then
        (if a == 0 then some 0 else (right.denote env).bind fun b => some (if b == 0 then 0 else 1))
      else
        (if a == 0 then (right.denote env).bind fun b => some (if b == 0 then 0 else 1) else some 1)
  | .size _ _ | .read _ _ _ => none

theorem denote_inc (env : Nat → Ty → Option Int) (slot : Nat) (ty : Ty) (v : Int)
    (found : env slot ty = some v) (literal : ty.valid 1 = true) (converted : ty.convert (v+1) = some (v+1)) :
    (NExpr.binary ty .add (.variable ty slot) (.literal ty 1)).denote env = some (v+1) := by
  simp [NExpr.denote,found,literal,binaryValue,converted]

theorem denote_lt (env : Nat → Ty → Option Int) (a b : Nat) (ty : Ty) (x y : Int)
    (left : env a ty = some x) (right : env b ty = some y) :
    (NExpr.binary ⟨1,false,true⟩ .lt (.variable ty a) (.variable ty b)).denote env =
      some (if x < y then 1 else 0) := by
  simp only [NExpr.denote,left,right,Option.bind_some,binaryValue,Ty.convert]
  by_cases h : x < y <;> simp [h]

theorem denote_sound : ∀ (e : NExpr) (s t : NState) (v : Int), e.scalarOnly = true →
    e.eval s = some (t,v) → e.denote (envOf s) = some v
  | .literal ty value, s, t, v, _, ran => by
      simp only [NExpr.eval] at ran
      split at ran
      · rename_i valid
        simp at ran
        obtain ⟨_,rfl⟩ := ran
        simp [NExpr.denote,valid]
      · simp at ran
  | .variable ty slot, s, t, v, _, ran => by
      simp only [NExpr.eval] at ran
      cases cell : s.scalarCell slot ty with
      | none => simp [cell] at ran
      | some pair =>
        simp [cell] at ran
        obtain ⟨_,rfl⟩ := ran
        simp [NExpr.denote,envOf,cell]
  | .cast ty operand, s, t, v, hs, ran => by
      have inner : operand.scalarOnly = true := by simpa [NExpr.scalarOnly] using hs
      simp only [NExpr.eval] at ran
      cases h : operand.eval (s.charge 0 (operand.nodes+1)) with
      | none => simp [h] at ran
      | some pair =>
        rcases pair with ⟨next,u⟩
        have value := denote_sound operand _ _ _ inner h
        simp only [h,Bind.bind,Option.bind] at ran
        cases c : ty.convert u with
        | none => simp [c] at ran
        | some converted =>
          simp [c] at ran
          obtain ⟨_,rfl⟩ := ran
          have env : envOf (s.charge 0 (operand.nodes+1)) = envOf s := envOf_core (core_charge _ _ _)
          rw [env] at value
          simp [NExpr.denote,value,c]
  | .targetCast ty operand, s, t, v, hs, ran => by
      have inner : operand.scalarOnly = true := by simpa [NExpr.scalarOnly] using hs
      simp only [NExpr.eval] at ran
      cases h : operand.eval (s.charge 0 (operand.nodes+1)) with
      | none => simp [h] at ran
      | some pair =>
        rcases pair with ⟨next,u⟩
        have value := denote_sound operand _ _ _ inner h
        simp only [h,Bind.bind,Option.bind] at ran
        cases c : ty.targetConvert u with
        | none => simp [c] at ran
        | some converted =>
          simp [c] at ran
          obtain ⟨_,rfl⟩ := ran
          have env : envOf (s.charge 0 (operand.nodes+1)) = envOf s := envOf_core (core_charge _ _ _)
          rw [env] at value
          simp [NExpr.denote,value,c]
  | .unary ty op operand, s, t, v, hs, ran => by
      have inner : operand.scalarOnly = true := by simpa [NExpr.scalarOnly] using hs
      simp only [NExpr.eval] at ran
      cases h : operand.eval (s.charge 0 (operand.nodes+1)) with
      | none => simp [h] at ran
      | some pair =>
        rcases pair with ⟨next,u⟩
        have value := denote_sound operand _ _ _ inner h
        simp only [h,Bind.bind,Option.bind] at ran
        cases c : ty.convert (unaryValue op u) with
        | none => simp [c] at ran
        | some converted =>
          simp [c] at ran
          obtain ⟨_,rfl⟩ := ran
          have env : envOf (s.charge 0 (operand.nodes+1)) = envOf s := envOf_core (core_charge _ _ _)
          rw [env] at value
          simp [NExpr.denote,value,c]
  | .binary ty op left right, s, t, v, hs, ran => by
      have inner : left.scalarOnly = true ∧ right.scalarOnly = true := by simpa [NExpr.scalarOnly] using hs
      simp only [NExpr.eval] at ran
      cases h1 : left.eval (s.charge 0 (left.nodes+right.nodes+1)) with
      | none => simp [h1] at ran
      | some first =>
        rcases first with ⟨next,a⟩
        have g1 := eval_scalar left _ _ _ inner.1 h1
        have value1 := denote_sound left _ _ _ inner.1 h1
        simp only [h1,Bind.bind,Option.bind] at ran
        cases h2 : right.eval next with
        | none => simp [h2] at ran
        | some second =>
          rcases second with ⟨last,b⟩
          have value2 := denote_sound right _ _ _ inner.2 h2
          simp only [h2,Bind.bind,Option.bind] at ran
          cases c : ty.convert (binaryValue op a b) with
          | none => simp [c] at ran
          | some converted =>
            simp [c] at ran
            obtain ⟨_,rfl⟩ := ran
            have env1 : envOf (s.charge 0 (left.nodes+right.nodes+1)) = envOf s := envOf_core (core_charge _ _ _)
            have env2 : envOf next = envOf (s.charge 0 (left.nodes+right.nodes+1)) := envOf_core g1.1
            rw [env1] at value1 env2
            rw [env2] at value2
            simp [NExpr.denote,value1,value2,c]
  | .divrem ty remainder left right, s, t, v, hs, ran => by
      have inner : left.scalarOnly = true ∧ right.scalarOnly = true := by simpa [NExpr.scalarOnly] using hs
      simp only [NExpr.eval] at ran
      cases h1 : left.eval (s.charge 0 (left.nodes+right.nodes+1)) with
      | none => simp [h1] at ran
      | some first =>
        rcases first with ⟨next,a⟩
        have g1 := eval_scalar left _ _ _ inner.1 h1
        have value1 := denote_sound left _ _ _ inner.1 h1
        simp only [h1,Bind.bind,Option.bind] at ran
        cases h2 : right.eval next with
        | none => simp [h2] at ran
        | some second =>
          rcases second with ⟨last,b⟩
          have value2 := denote_sound right _ _ _ inner.2 h2
          simp only [h2,Bind.bind,Option.bind] at ran
          cases c : checkedDivRem ty remainder a b with
          | none => simp [c] at ran
          | some converted =>
            simp [c] at ran
            obtain ⟨_,rfl⟩ := ran
            have env1 : envOf (s.charge 0 (left.nodes+right.nodes+1)) = envOf s := envOf_core (core_charge _ _ _)
            have env2 : envOf next = envOf (s.charge 0 (left.nodes+right.nodes+1)) := envOf_core g1.1
            rw [env1] at value1 env2
            rw [env2] at value2
            simp [NExpr.denote,value1,value2,c]
  | .logical conjunction left right, s, t, v, hs, ran => by
      have inner : left.scalarOnly = true ∧ right.scalarOnly = true := by simpa [NExpr.scalarOnly] using hs
      simp only [NExpr.eval] at ran
      cases h1 : left.eval (s.charge 0 (left.nodes+right.nodes+1)) with
      | none => simp [h1] at ran
      | some first =>
        rcases first with ⟨next,a⟩
        have g1 := eval_scalar left _ _ _ inner.1 h1
        have value1 := denote_sound left _ _ _ inner.1 h1
        have env1 : envOf (s.charge 0 (left.nodes+right.nodes+1)) = envOf s := envOf_core (core_charge _ _ _)
        have env2 : envOf next = envOf s := (envOf_core g1.1).trans env1
        rw [env1] at value1
        simp only [h1,Bind.bind,Option.bind] at ran
        cases conjunction <;> by_cases zero : a = 0 <;>
          first
          | (simp [zero] at ran; obtain ⟨_,rfl⟩ := ran; simp [NExpr.denote,value1,zero])
          | (cases h2 : right.eval next with
             | none => simp [zero,h2] at ran
             | some second =>
               rcases second with ⟨last,b⟩
               have value2 := denote_sound right _ _ _ inner.2 h2
               rw [env2] at value2
               simp [zero,h2] at ran
               obtain ⟨_,rfl⟩ := ran
               simp [NExpr.denote,value1,value2,zero])
  | .size _ _, _, _, _, hs, _ => by simp [NExpr.scalarOnly] at hs
  | .read _ _ _, _, _, _, hs, _ => by simp [NExpr.scalarOnly] at hs

theorem denote_complete : ∀ (e : NExpr) (s : NState) (v : Int), e.scalarOnly = true →
    e.denote (envOf s) = some v → ∃ t, e.eval s = some (t,v)
  | .literal ty value, s, v, _, h => by
      simp only [NExpr.denote] at h
      split at h
      · rename_i valid
        simp at h
        subst h
        exact ⟨s.charge 1 1,by simp [NExpr.eval,valid]⟩
      · simp at h
  | .variable ty slot, s, v, _, h => by
      simp only [NExpr.denote,envOf] at h
      cases cell : s.scalarCell slot ty with
      | none => simp [cell] at h
      | some pair =>
        simp [cell] at h
        exact ⟨s.charge 1 1,by simp [NExpr.eval,cell,h]⟩
  | .cast ty operand, s, v, hs, h => by
      have inner : operand.scalarOnly = true := by simpa [NExpr.scalarOnly] using hs
      simp only [NExpr.denote] at h
      cases d : operand.denote (envOf s) with
      | none => simp [d] at h
      | some u =>
        simp only [d,Option.bind_some] at h
        have env : envOf (s.charge 0 (operand.nodes+1)) = envOf s := envOf_core (core_charge _ _ _)
        obtain ⟨next,ran⟩ := denote_complete operand (s.charge 0 (operand.nodes+1)) u inner (by rw [env]; exact d)
        exact ⟨next.charge 1 1,by simp [NExpr.eval,ran,h]⟩
  | .targetCast ty operand, s, v, hs, h => by
      have inner : operand.scalarOnly = true := by simpa [NExpr.scalarOnly] using hs
      simp only [NExpr.denote] at h
      cases d : operand.denote (envOf s) with
      | none => simp [d] at h
      | some u =>
        simp only [d,Option.bind_some] at h
        have env : envOf (s.charge 0 (operand.nodes+1)) = envOf s := envOf_core (core_charge _ _ _)
        obtain ⟨next,ran⟩ := denote_complete operand (s.charge 0 (operand.nodes+1)) u inner (by rw [env]; exact d)
        exact ⟨next.charge 1 1,by simp [NExpr.eval,ran,h]⟩
  | .unary ty op operand, s, v, hs, h => by
      have inner : operand.scalarOnly = true := by simpa [NExpr.scalarOnly] using hs
      simp only [NExpr.denote] at h
      cases d : operand.denote (envOf s) with
      | none => simp [d] at h
      | some u =>
        simp only [d,Option.bind_some] at h
        have env : envOf (s.charge 0 (operand.nodes+1)) = envOf s := envOf_core (core_charge _ _ _)
        obtain ⟨next,ran⟩ := denote_complete operand (s.charge 0 (operand.nodes+1)) u inner (by rw [env]; exact d)
        exact ⟨next.charge 1 1,by simp [NExpr.eval,ran,h]⟩
  | .binary ty op left right, s, v, hs, h => by
      have inner : left.scalarOnly = true ∧ right.scalarOnly = true := by simpa [NExpr.scalarOnly] using hs
      simp only [NExpr.denote] at h
      cases d1 : left.denote (envOf s) with
      | none => simp [d1] at h
      | some a =>
        cases d2 : right.denote (envOf s) with
        | none => simp [d1,d2] at h
        | some b =>
          simp only [d1,d2,Option.bind_some] at h
          have env1 : envOf (s.charge 0 (left.nodes+right.nodes+1)) = envOf s := envOf_core (core_charge _ _ _)
          obtain ⟨next,ran1⟩ := denote_complete left (s.charge 0 (left.nodes+right.nodes+1)) a inner.1
            (by rw [env1]; exact d1)
          have g1 := eval_scalar left _ _ _ inner.1 ran1
          have env2 : envOf next = envOf s := (envOf_core g1.1).trans env1
          obtain ⟨last,ran2⟩ := denote_complete right next b inner.2 (by rw [env2]; exact d2)
          exact ⟨last.charge 1 1,by simp [NExpr.eval,ran1,ran2,h]⟩
  | .divrem ty remainder left right, s, v, hs, h => by
      have inner : left.scalarOnly = true ∧ right.scalarOnly = true := by simpa [NExpr.scalarOnly] using hs
      simp only [NExpr.denote] at h
      cases d1 : left.denote (envOf s) with
      | none => simp [d1] at h
      | some a =>
        cases d2 : right.denote (envOf s) with
        | none => simp [d1,d2] at h
        | some b =>
          simp only [d1,d2,Option.bind_some] at h
          have env1 : envOf (s.charge 0 (left.nodes+right.nodes+1)) = envOf s := envOf_core (core_charge _ _ _)
          obtain ⟨next,ran1⟩ := denote_complete left (s.charge 0 (left.nodes+right.nodes+1)) a inner.1
            (by rw [env1]; exact d1)
          have g1 := eval_scalar left _ _ _ inner.1 ran1
          have env2 : envOf next = envOf s := (envOf_core g1.1).trans env1
          obtain ⟨last,ran2⟩ := denote_complete right next b inner.2 (by rw [env2]; exact d2)
          exact ⟨last.charge 1 1,by simp [NExpr.eval,ran1,ran2,h]⟩
  | .logical conjunction left right, s, v, hs, h => by
      have inner : left.scalarOnly = true ∧ right.scalarOnly = true := by simpa [NExpr.scalarOnly] using hs
      simp only [NExpr.denote] at h
      cases d1 : left.denote (envOf s) with
      | none => simp [d1] at h
      | some a =>
        simp only [d1,Option.bind_some] at h
        have env1 : envOf (s.charge 0 (left.nodes+right.nodes+1)) = envOf s := envOf_core (core_charge _ _ _)
        obtain ⟨next,ran1⟩ := denote_complete left (s.charge 0 (left.nodes+right.nodes+1)) a inner.1
          (by rw [env1]; exact d1)
        have g1 := eval_scalar left _ _ _ inner.1 ran1
        have env2 : envOf next = envOf s := (envOf_core g1.1).trans env1
        cases conjunction <;> by_cases zero : a = 0 <;>
          first
          | (simp [zero] at h; subst h; exact ⟨next.charge 1 1,by simp [NExpr.eval,ran1,zero]⟩)
          | (cases d2 : right.denote (envOf s) with
             | none => simp [zero,d2] at h
             | some b =>
               simp [zero,d2] at h
               obtain ⟨last,ran2⟩ := denote_complete right next b inner.2 (by rw [env2]; exact d2)
               subst h
               exact ⟨last.charge 1 1,by simp [NExpr.eval,ran1,ran2,zero]⟩)
  | .size _ _, _, _, hs, _ => by simp [NExpr.scalarOnly] at hs
  | .read _ _ _, _, _, hs, _ => by simp [NExpr.scalarOnly] at hs

end Proofs.CppNestedEval
