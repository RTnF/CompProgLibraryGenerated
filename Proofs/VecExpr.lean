import Proofs.StraightLine
import Proofs.Mod61Body

namespace Proofs.VecExpr
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppMixedInvoke
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.FlatVectorStmt Proofs.QuotientFrame
open Proofs.StraightLine Proofs.Mod61Body
open Proofs.CppState (Cell)

-- A callee with one read-only flat vector parameter (location slot 0) and scalar locals at the slots from 1.
structure VCtx where
  ty : Ty
  wV : Bool
  flag : Bool
  R : Nat
  vsc : Nat
  buf : Buffer Value
  vec : List Int
  items : buf.items = vec.map Value.integer
  perm : wV = true → flag = true
  small : vec.length < 18446744073709551616
  L0 : Nat
  T0 : Nat
  sc : Nat
  N : Nat

def sl1 (n : Nat) : List Location := .vector 0 :: ssl n

-- Frame facts that survive every statement that does not write the vector.
structure FV (c : VCtx) (fr : Frame) : Prop where
  valid : fr.state.wellFormed = true
  lengths : fr.rootWritable.length = fr.state.forest.objects.length
  live : fr.state.liveSpace = c.L0
  work : fr.state.storage.work = c.T0
  strict : ∀ owner k, fr.state.forest.context owner = some k → k < c.sc
  count : fr.state.storage.objects.length = c.N
  bindings : fr.bindings = [⟨c.R,.integer c.ty,c.wV,.root c.vsc⟩]
  vtag : fr.state.forest.lookup c.R = some ⟨.integer c.ty,none,some c.vsc,[]⟩
  vfound : fr.state.storage.lookup c.R = some c.buf
  flagR : fr.rootWritable[c.R]? = some c.flag

-- The scalar locals of `ps` live at location slots 1, 2, ...; slot 0 is the vector.
def penv1 (ps : PS) : Nat → Ty → Option Int
  | 0, _ => none
  | k+1, ty => penv ps k ty

def elemAt (c : VCtx) (j : Int) : Option Int :=
  if 0 ≤ j then (c.vec[j.toNat]?).bind fun x => if c.ty.valid x = true then some x else none else none

-- Pure meaning of the expressions that read or measure the vector (and scalar subtrees).
def vden (c : VCtx) (env : Nat → Ty → Option Int) (e : NExpr) : Option Int :=
  if e.scalarOnly = true then e.denote env else
  match e with
  | .cast ty op => (vden c env op).bind ty.convert
  | .unary ty op e => (vden c env e).bind fun v => ty.convert (unaryValue op v)
  | .binary ty op l r => (vden c env l).bind fun a => (vden c env r).bind fun b => ty.convert (binaryValue op a b)
  | .size (.integer ty) (.local 0) => if ty = c.ty then some (c.vec.length : Int) else none
  | .read ty (.local 0) index =>
      if ty = c.ty ∧ index.scalarOnly = true then (index.denote env).bind (elemAt c) else none
  | _ => none

-- Work and temporaries charged by the evaluation (as given by the Ev lemmas).
def vwp : NExpr → Nat × Nat
  | .cast ty op => if (NExpr.cast ty op).scalarOnly = true then ((NExpr.cast ty op).nodes,(NExpr.cast ty op).nodes)
      else ((vwp op).1+1,max (op.nodes+1) (max (vwp op).2 1))
  | .unary ty o e => if (NExpr.unary ty o e).scalarOnly = true then ((NExpr.unary ty o e).nodes,(NExpr.unary ty o e).nodes)
      else ((vwp e).1+1,max (e.nodes+1) (max (vwp e).2 1))
  | .binary ty o l r => if (NExpr.binary ty o l r).scalarOnly = true then
        ((NExpr.binary ty o l r).nodes,(NExpr.binary ty o l r).nodes)
      else ((vwp l).1+(vwp r).1+1,max (l.nodes+r.nodes+1) (max (max (vwp l).2 (vwp r).2) 1))
  | .size el (.local k) => (3,3)
  | .size el (.row p e i) => (i.nodes+4,i.nodes+4)
  | .read ty (.local k) index => (index.nodes+3,index.nodes+3)
  | .read ty (.row p e i) pos => (i.nodes+pos.nodes+4,i.nodes+pos.nodes+4)
  | e => (e.nodes,e.nodes)


theorem env1_of_qs {S : NState} {B sc : Nat} {ps : PS} (qs : QS S [] B sc ps.mem ps.bs (sl1 ps.bs.length)) :
    envOf S = penv1 ps := by
  funext slot ty
  cases slot with
  | zero =>
    simp [envOf, NState.scalarCell, NState.scalarSlot, qs.slots, sl1, penv1]
  | succ k =>
    unfold envOf NState.scalarCell NState.scalarSlot penv1 penv
    rw [qs.slots,qs.bindings,qs.memory]
    by_cases h : k < ps.bs.length
    · have e : (sl1 ps.bs.length)[k+1]? = some (.scalar k) := by simp [sl1,ssl,h]
      rw [e]
      cases hb : ps.bs[k]? with
      | none => simp at hb; omega
      | some b =>
        cases hm : ps.mem[b.address]? with
        | none => simp [hb,hm]
        | some c =>
          by_cases ok : c.type = ty ∧ ty.valid c.value = true
          · simp [hb,hm,ok]
          · simp [hb,hm,ok]
    · have e : (sl1 ps.bs.length)[k+1]? = none := by simp [sl1,ssl]; omega
      have e2 : ps.bs[k]? = none := by simp; omega
      simp [e,e2]

theorem vden_scalar (c : VCtx) (env : Nat → Ty → Option Int) (e : NExpr) (h : e.scalarOnly = true) :
    vden c env e = e.denote env := by
  unfold vden; simp [h]


theorem vwp_scalar (e : NExpr) (h : e.scalarOnly = true) : vwp e = (e.nodes,e.nodes) := by
  cases e <;> simp_all [vwp, NExpr.scalarOnly]

theorem vectorSlot_zero {S : NState} {n : Nat} (h : S.slots = sl1 n) : S.vectorSlot 0 = some 0 := by
  simp [NState.vectorSlot, h, sl1]

theorem ev_vden (c : VCtx) : ∀ (e : NExpr) (S : NState) (ps : PS) {B sc : Nat} (v : Int),
    QS S [] B sc ps.mem ps.bs (sl1 ps.bs.length) → FV c S.frame → vden c (penv1 ps) e = some v →
    ∃ t, Ev S e t v [] (vwp e).1 (vwp e).2
  | e, S, ps, B, sc, v, qs, fv, h => by
    by_cases hs : e.scalarOnly = true
    · rw [vden_scalar c _ e hs, ← env1_of_qs qs] at h
      obtain ⟨t, ev⟩ := Ev.scalar hs h
      exact ⟨t, by rw [vwp_scalar e hs]; exact ev⟩
    · cases e with
      | cast ty op =>
        have hn : (vden c (penv1 ps) op).bind ty.convert = some v := by
          have := h; unfold vden at this; simpa [hs] using this
        obtain ⟨a, ha, hc⟩ := Option.bind_eq_some_iff.mp hn
        obtain ⟨t, ev⟩ := ev_vden c op (S.charge 0 (op.nodes+1)) ps a (qs.core (core_charge S 0 _)) fv ha
        refine ⟨t.charge 1 1, ?_⟩
        have := Ev.cast ev hc
        simpa [vwp, hs] using this
      | unary ty o op =>
        have hn : (vden c (penv1 ps) op).bind (fun a => ty.convert (unaryValue o a)) = some v := by
          have := h; unfold vden at this; simpa [hs] using this
        obtain ⟨a, ha, hc⟩ := Option.bind_eq_some_iff.mp hn
        obtain ⟨t, ev⟩ := ev_vden c op (S.charge 0 (op.nodes+1)) ps a (qs.core (core_charge S 0 _)) fv ha
        refine ⟨t.charge 1 1, ?_⟩
        have := Ev.unary ev hc
        simpa [vwp, hs] using this
      | binary ty o l r =>
        have hn : (vden c (penv1 ps) l).bind (fun a => (vden c (penv1 ps) r).bind fun b => ty.convert (binaryValue o a b)) = some v := by
          have := h; unfold vden at this; simpa [hs] using this
        obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.mp hn
        obtain ⟨b, hb', hc⟩ := Option.bind_eq_some_iff.mp hb
        obtain ⟨t1, ev1⟩ := ev_vden c l (S.charge 0 (l.nodes+r.nodes+1)) ps a (qs.core (core_charge S 0 _)) fv ha
        have g1 := Ev.good ev1
        have core1 : Core S t1 := (core_charge S 0 _).trans g1.1
        obtain ⟨t2, ev2⟩ := ev_vden c r t1 ps b (qs.core core1) (by rw [core1.1]; exact fv) hb'
        refine ⟨t2.charge 1 1, ?_⟩
        have := Ev.binary ev1 ev2 hc
        simpa [vwp, hs] using this
      | size el ct =>
        cases el with
        | vector _ => unfold vden at h; simp [hs] at h
        | integer ty =>
          cases ct with
          | row _ _ _ => unfold vden at h; simp [hs] at h
          | «local» k =>
            cases k with
            | succ _ => unfold vden at h; simp [hs] at h
            | zero =>
              have hn : (if ty = c.ty then some (c.vec.length : Int) else none) = some v := by
                have := h; unfold vden at this; simpa [hs] using this
              have hty : ty = c.ty := by
                by_cases t : ty = c.ty
                · exact t
                · simp [t] at hn
              subst hty
              have hsz : c.buf.items.length = c.vec.length := by rw [c.items, List.length_map]
              have hv : (c.vec.length : Int) = v := by simpa using hn
              have small : c.buf.items.length < 2 ^ 64 := by
                rw [hsz]; have := c.small; simpa using this
              obtain ⟨t, ev⟩ := Ev.sizeRoot S 0 0 c.R c.vsc c.ty c.wV c.flag c.buf (vectorSlot_zero qs.slots)
                (by simp [fv.bindings]) fv.valid fv.vtag fv.vfound fv.lengths fv.flagR c.perm small
              refine ⟨t, ?_⟩
              rw [hsz, hv] at ev
              simpa [vwp] using ev
      | read ty ct index =>
        cases ct with
        | row _ _ _ => unfold vden at h; simp [hs] at h
        | «local» k =>
          cases k with
          | succ _ => unfold vden at h; simp [hs] at h
          | zero =>
            have hn : (if ty = c.ty ∧ index.scalarOnly = true then (index.denote (penv1 ps)).bind (elemAt c) else none) = some v := by
              have := h; unfold vden at this; simpa [hs] using this
            have hc : ty = c.ty ∧ index.scalarOnly = true := by
              by_cases t : ty = c.ty ∧ index.scalarOnly = true
              · exact t
              · simp [t] at hn
            obtain ⟨hty, hidx⟩ := hc
            subst hty
            simp only [hidx, and_self, ite_true] at hn
            obtain ⟨j, hj, he⟩ := Option.bind_eq_some_iff.mp hn
            unfold elemAt at he
            by_cases hj0 : 0 ≤ j
            · simp only [hj0, ite_true] at he
              obtain ⟨x, hx, hxv⟩ := Option.bind_eq_some_iff.mp he
              by_cases hvalid : c.ty.valid x = true
              · simp only [hvalid, ite_true] at hxv
                have hxv' : x = v := Option.some.inj hxv
                have jnat : ((j.toNat : Nat) : Int) = j := Int.toNat_of_nonneg hj0
                have item : c.buf.items[j.toNat]? = some (Value.integer v) := by
                  rw [c.items]; simp [List.getElem?_map, hx, hxv']
                have idxv : index.denote (envOf S) = some ((j.toNat : Nat) : Int) := by
                  rw [env1_of_qs qs, jnat]; exact hj
                obtain ⟨t, ev⟩ := Ev.readRoot S 0 0 c.R c.vsc index j.toNat c.ty c.wV c.flag c.buf v hidx idxv
                  (vectorSlot_zero qs.slots) (by simp [fv.bindings]) fv.valid fv.vtag fv.vfound fv.lengths fv.flagR c.perm item
                exact ⟨t, by simpa [vwp] using ev⟩
              · simp [hvalid] at hxv
            · simp [hj0] at he
      | literal _ _ => simp [NExpr.scalarOnly] at hs
      | «variable» _ _ => simp [NExpr.scalarOnly] at hs
      | targetCast _ _ => unfold vden at h; simp [hs] at h
      | divrem _ _ _ _ => unfold vden at h; simp [hs] at h
      | logical _ _ _ => unfold vden at h; simp [hs] at h

end Proofs.VecExpr
