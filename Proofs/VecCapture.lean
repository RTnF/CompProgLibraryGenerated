import Proofs.UfFieldsRoot
import Proofs.DynamicResultValid

namespace Proofs.VecCapture
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecWrite
open Proofs.VecKitW Proofs.PowModStep Proofs.DynamicResultValid

-- A terminal value return becomes the inliner's fresh, writable scalar local.
-- Prefixes must continue normally; capturing an early return is unsound.
def Silent (ty : Ty) (c : Command) : Prop :=
  ∀ fuel ps vec r, pexecW ty fuel c ps vec = some r → r.ret = none

inductive Terminal (vecTy valueTy : Ty) (e : NExpr) : Command → Command → Prop
  | done : Terminal vecTy valueTy e (.sequence (.primitive (.ret e)) Sk)
      (.sequence (.primitive (.declare valueTy true e)) Sk)
  | seq (first before after : Command) (silent : Silent vecTy first)
      (tail : Terminal vecTy valueTy e before after) :
      Terminal vecTy valueTy e (.sequence first before) (.sequence first after)

def appended (ty : Ty) (v : Int) (ps : PS) : PS :=
  ⟨ps.mem++[⟨ty,v⟩],ps.bs++[⟨ps.mem.length,true⟩]⟩

def captured (ty : Ty) (e : NExpr) (v : Int) (r : PRW) : PRW :=
  ⟨appended ty v r.ps,r.vec,none,r.cost,max r.need (r.ps.mem.length+r.ps.bs.length+(vwp e).2+4),r.wk⟩

theorem execution {vecTy valueTy : Ty} {e : NExpr} {before after : Command}
    (shape : Terminal vecTy valueTy e before after) :
    ∀ fuel ps vec r v, pexecW vecTy fuel before ps vec = some r → r.ret = some v →
      valueTy.convert v = some v → pexecW vecTy fuel after ps vec = some (captured valueTy e v r) ∧
      (captured valueTy e v r).need ≤ r.need+2 := by
  induction shape with
  | done =>
    intro fuel ps vec r v run ret convert
    cases value : vdenL vecTy vec (penv1 ps) e with
    | none => simp [pexecW,pstmtW,value] at run
    | some u =>
      simp only [pexecW,pstmtW,value,Bind.bind,Option.bind] at run
      have same := Option.some.inj run
      subst r
      have equal : u = v := Option.some.inj ret
      subst u
      have decl := pstmtW_declare_ok vecTy ps vec valueTy true e v value v convert
      have prim := (pexecW_prim vecTy fuel (.declare valueTy true e) ps vec).trans decl
      have seq := seqW_some prim rfl (pexecW_skip vecTy fuel (appended valueTy v ps) vec)
      have small : ps.mem.length+1+(ps.bs.length+1) ≤ ps.mem.length+ps.bs.length+(vwp e).2+4 := by omega
      constructor
      · simpa [captured,appended,Nat.max_eq_left small] using seq
      · simp [captured]
  | seq first before after silent tail ih =>
    intro fuel ps vec r v run ret convert
    rw [pexecW_seq] at run
    obtain ⟨one,oneRun,rest⟩ := bind_some _ _ _ run
    have continuing := silent fuel ps vec one oneRun
    simp only [continuing] at rest
    obtain ⟨two,twoRun,joined⟩ := bind_some _ _ _ rest
    have same := Option.some.inj joined
    subst r
    obtain ⟨next,space⟩ := ih fuel one.ps one.vec two v twoRun ret convert
    have combined := seqW_some oneRun continuing next
    constructor
    · simpa [captured,Nat.max_assoc] using combined
    · simp only [captured] at space ⊢; omega

-- Replace only the terminal skip on a sequence's right spine. Loop bodies
-- and scoped prefixes retain their own lexical exits.
def plug : Command → Command → Command
  | .primitive .skip, tail => tail
  | .sequence first rest, tail => .sequence first (plug rest tail)
  | other, tail => .sequence other tail

def followed (first next : PRW) : PRW :=
  ⟨next.ps,next.vec,next.ret,first.cost+next.cost,max first.need next.need,first.wk+next.wk⟩

theorem continuation {vecTy valueTy : Ty} {e : NExpr} {before after : Command}
    (shape : Terminal vecTy valueTy e before after) :
    ∀ fuel ps vec r v tail next, pexecW vecTy fuel before ps vec = some r → r.ret = some v →
      valueTy.convert v = some v →
      pexecW vecTy fuel tail (appended valueTy v r.ps) r.vec = some next →
      pexecW vecTy fuel (plug after tail) ps vec = some (followed (captured valueTy e v r) next) := by
  induction shape with
  | done =>
    intro fuel ps vec r v tail next run ret convert tailRun
    cases value : vdenL vecTy vec (penv1 ps) e with
    | none => simp [pexecW,pstmtW,value] at run
    | some u =>
      simp only [pexecW,pstmtW,value,Bind.bind,Option.bind] at run
      have same := Option.some.inj run
      subst r
      have equal : u = v := Option.some.inj ret
      subst u
      have decl := pstmtW_declare_ok vecTy ps vec valueTy true e v value v convert
      have prim := (pexecW_prim vecTy fuel (.declare valueTy true e) ps vec).trans decl
      have combined := seqW_some prim rfl tailRun
      simpa [plug,captured,followed] using combined
  | seq first before after silent tailShape ih =>
    intro fuel ps vec r v tail next run ret convert tailRun
    rw [pexecW_seq] at run
    obtain ⟨one,oneRun,rest⟩ := bind_some _ _ _ run
    have continuing := silent fuel ps vec one oneRun
    simp only [continuing] at rest
    obtain ⟨two,twoRun,joined⟩ := bind_some _ _ _ rest
    have same := Option.some.inj joined
    subst r
    have capturedTail := ih fuel one.ps one.vec two v tail next twoRun ret convert tailRun
    have combined := seqW_some oneRun continuing capturedTail
    simpa [plug,captured,followed,Nat.add_assoc,Nat.max_assoc] using combined

-- The pure flat executor rejects a return from a while body rather than
-- propagating it. Every successful while in this profile therefore continues.
theorem while_silent (ty : Ty) (condition : NExpr) (body : Command) : Silent ty (.whileLoop condition body) := by
  intro fuel
  induction fuel with
  | zero => intro ps vec r run; simp [pexecW] at run
  | succ fuel ih =>
    intro ps vec r run
    rw [pexecW_while] at run
    obtain ⟨v,value,rest⟩ := bind_some _ _ _ run
    by_cases zero : v = 0
    · simp only [zero,ite_true] at rest
      have same := Option.some.inj rest
      subst r; rfl
    · simp only [zero,ite_false] at rest
      obtain ⟨one,oneRun,tail⟩ := bind_some _ _ _ rest
      cases returned : one.ret with
      | some x => simp [returned] at tail
      | none =>
        simp only [returned] at tail
        obtain ⟨two,twoRun,joined⟩ := bind_some _ _ _ tail
        have same := Option.some.inj joined
        subst r
        exact ih one.ps one.vec two twoRun

theorem declare_silent (vecTy ty : Ty) (w : Bool) (e : NExpr) : Silent vecTy (.primitive (.declare ty w e)) := by
  intro fuel ps vec r run
  rw [pexecW_prim] at run
  simp only [pstmtW,Bind.bind,Option.bind] at run
  obtain ⟨v,value,rest⟩ := bind_some _ _ _ run
  obtain ⟨x,convert,done⟩ := bind_some _ _ _ rest
  have same := Option.some.inj done
  subst r; rfl

theorem check_silent (vecTy : Ty) (e : NExpr) : Silent vecTy (.primitive (.check e)) := by
  intro fuel ps vec r run
  rw [pexecW_prim] at run
  simp only [pstmtW,Bind.bind,Option.bind] at run
  obtain ⟨v,value,rest⟩ := bind_some _ _ _ run
  split at rest
  · have same := Option.some.inj rest
    subst r; rfl
  · contradiction

end Proofs.VecCapture
