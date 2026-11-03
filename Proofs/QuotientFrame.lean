import Proofs.DoublingPrologue
import Proofs.FlatVectorStmt

namespace Proofs.QuotientFrame
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppMixedInvoke
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.FlatVectorStmt
open Proofs.CppState (Cell)


-- Counter bounds reuse the doubling bundle through a dummy `Fixed` carrying only the two bounds.
def fx (SPB TPB : Nat) : Fixed := ⟨[],0,0,0,0,0,0,0,0,[],[],⟨0,[],0,0,0⟩,SPB,TPB⟩
abbrev Cq (SPB TPB W : Nat) (S : NState) : Prop := Cb (fx SPB TPB) W S

-- Scalar shape of the program's states.
structure QS (S : NState) (P : List Cell) (B scope : Nat) (cells : List Cell)
    (binds : List CppState.Binding) (slots : List Location) : Prop where
  slots : S.slots = slots
  memory : S.scalars.memory = P ++ cells
  bindings : S.scalars.bindings = binds
  base : S.scalars.baseMemory = B
  scope : S.scope = scope

theorem QS.core {S t : NState} {P B scope cells binds slots} (qs : QS S P B scope cells binds slots)
    (core : Core S t) : QS t P B scope cells binds slots := by
  obtain ⟨frame,sl,sc,me,bi,ba⟩ := core
  exact ⟨by rw [sl]; exact qs.slots,by rw [me]; exact qs.memory,by rw [bi]; exact qs.bindings,
    by rw [ba]; exact qs.base,by rw [sc]; exact qs.scope⟩

theorem QS.live_eq {S : NState} {P B scope cells binds slots} (qs : QS S P B scope cells binds slots) :
    liveS S = P.length+cells.length-B+binds.length := by
  simp [liveS,qs.memory,qs.bindings,qs.base]

-- Frame facts before the result vector exists.
structure FA (fr : Frame) (L0 T0 sc N : Nat) : Prop where
  valid : fr.state.wellFormed = true
  lengths : fr.rootWritable.length = fr.state.forest.objects.length
  live : fr.state.liveSpace = L0
  work : fr.state.storage.work = T0
  strict : ∀ owner c, fr.state.forest.context owner = some c → c < sc
  bindings : fr.bindings = []
  count : fr.state.storage.objects.length = N

theorem FA.of_eq {fr fr' : Frame} {L0 T0 N sc : Nat} (fa : FA fr L0 T0 sc N) (h : fr' = fr) : FA fr' L0 T0 sc N := by
  rw [h]; exact fa

theorem FA.fresh {fr : Frame} {L0 T0 N sc scope : Nat} (fa : FA fr L0 T0 sc N) (hsc : sc ≤ scope) :
    ∀ owner, fr.state.forest.context owner ≠ some (scope+1) := by
  intro owner h
  have := fa.strict owner _ h
  omega

theorem FA.noop {fr fr' : Frame} {L0 T0 N sc : Nat} (fa : FA fr L0 T0 sc N)
    (same : SameObjects fr.state fr'.state) (rw : fr'.rootWritable = fr.rootWritable)
    (work : fr'.state.storage.work = fr.state.storage.work) (hb : fr'.bindings = []) : FA fr' L0 T0 sc N := by
  refine ⟨?_,?_,?_,?_,?_,hb,?_⟩
  · rw [same.wellFormed]; exact fa.valid
  · rw [rw,same.1]; exact fa.lengths
  · rw [same.liveSpace]; exact fa.live
  · rw [work]; exact fa.work
  · intro owner c h
    rw [same.1] at h
    exact fa.strict owner c h
  · rw [same.2.1]; exact fa.count

-- Leaving a scalar-only scope: cells declared inside disappear, outer cells keep their (updated) values.
theorem leave_gen (outer inner : NState) (mem extra : List Cell)
    (hm : inner.scalars.memory = mem ++ extra)
    (hty : mem.map Cell.type = outer.scalars.memory.map Cell.type)
    (valid : inner.frame.state.wellFormed = true)
    (fresh : ∀ owner, inner.frame.state.forest.context owner ≠ some (outer.scope+1)) :
    outer.leave inner none = some (outer.left inner) ∧ (outer.left inner).scalars.memory = mem := by
  have lens : mem.length = outer.scalars.memory.length := by
    have := congrArg List.length hty; simpa using this
  have take : inner.scalars.memory.take outer.scalars.memory.length = mem := by
    rw [hm,← lens]; exact List.take_left
  have fits : outer.scalars.memory.length ≤ inner.scalars.memory.length := by rw [hm]; simp; omega
  refine ⟨leave_scalar outer inner none (by simp) fits (by rw [take]; exact hty) valid fresh,?_⟩
  rw [left_memory,take]

theorem decl_step {P : List Cell} {B scope : Nat} {cells : List Cell} {binds : List CppState.Binding}
    {slots : List Location} {SPB TPB W : Nat} (S : NState) (e : NExpr) (ty : Ty) (writable : Bool) (v v' : Int)
    (qs : QS S P B scope cells binds slots) (cq : Cq SPB TPB W S) (cap : liveS S+e.nodes+1 ≤ SPB)
    (scalar : e.scalarOnly = true) (value : e.denote (envOf S) = some v) (conv : ty.convert v = some v') :
    ∃ t, (NStmt.declare ty writable e).run S = some ⟨t,none,false⟩ ∧ t.frame = S.frame ∧
      QS t P B scope (cells ++ [⟨ty,v'⟩]) (binds ++ [⟨P.length+cells.length,writable⟩])
        (slots ++ [.scalar binds.length]) ∧ Cq SPB TPB (W+e.nodes+1) t := by
  obtain ⟨t,run,frame,sl,sc,me,bi,ba,wl,wu,pl,pu,ql,qu⟩ := declare_good e ty writable S v v' scalar value conv
  have memLen : S.scalars.memory.length = P.length+cells.length := by simp [qs.memory]
  have bindLen : S.scalars.bindings.length = binds.length := by simp [qs.bindings]
  refine ⟨t,run,frame,⟨?_,?_,?_,?_,?_⟩,?_⟩
  · rw [sl,bindLen,qs.slots]
  · rw [me,qs.memory]; simp
  · rw [bi,memLen,qs.bindings]
  · rw [ba]; exact qs.base
  · rw [sc]; exact qs.scope
  · exact Cb.step (w := e.nodes+1) (p := e.nodes+1) cq frame (by omega) pu cap qu

theorem assign_step {P : List Cell} {B scope : Nat} {cells cells' : List Cell} {binds : List CppState.Binding}
    {slots : List Location} {SPB TPB W : Nat} (S : NState) (e : NExpr) (slot idx : Nat) (ty : Ty) (v v' : Int)
    (binding : CppState.Binding) (cell : Cell)
    (qs : QS S P B scope cells binds slots) (cq : Cq SPB TPB W S) (cap : liveS S+e.nodes ≤ SPB)
    (scalar : e.scalarOnly = true) (value : e.denote (envOf S) = some v) (conv : ty.convert v = some v')
    (hs : slots[slot]? = some (.scalar idx)) (hb : binds[idx]? = some binding)
    (hm : (P ++ cells)[binding.address]? = some cell) (ctype : cell.type = ty) (cvalid : ty.valid cell.value = true)
    (writable : binding.writable = true)
    (hcells : (P ++ cells).set binding.address ⟨ty,v'⟩ = P ++ cells') :
    ∃ t, (NStmt.assign slot ty e).run S = some ⟨t,none,false⟩ ∧ t.frame = S.frame ∧
      QS t P B scope cells' binds slots ∧ Cq SPB TPB (W+e.nodes+1) t := by
  obtain ⟨t,run,frame,sl,sc,me,bi,ba,wl,wu,pl,pu,ql,qu,live⟩ := assign_good e slot idx ty S v v' binding cell
    scalar value conv (by rw [qs.slots]; exact hs) (by rw [qs.bindings]; exact hb)
    (by rw [qs.memory]; exact hm) ctype cvalid writable
  refine ⟨t,run,frame,⟨?_,?_,?_,?_,?_⟩,?_⟩
  · rw [sl]; exact qs.slots
  · rw [me,qs.memory,hcells]
  · rw [bi]; exact qs.bindings
  · rw [ba]; exact qs.base
  · rw [sc]; exact qs.scope
  · exact Cb.step (w := e.nodes+1) (p := e.nodes) cq frame (by omega) pu cap qu

def scopeUp (S : NState) : NState := {S with scope := S.scope+1}

theorem QS.enter {S : NState} {P B scope cells binds slots} (qs : QS S P B scope cells binds slots) :
    QS (scopeUp S) P B (scope+1) cells binds slots :=
  ⟨qs.slots,qs.memory,qs.bindings,qs.base,by simp [scopeUp,qs.scope]⟩

theorem Cq.enter {SPB TPB W : Nat} {S : NState} (cq : Cq SPB TPB W S) : Cq SPB TPB W (scopeUp S) :=
  Cb.enter cq

-- Leaving a scope that declared scalar cells and may have updated outer cells.
theorem leave_pack {outer inner : NState} {P : List Cell} {B sc : Nat} {cells cells' extra : List Cell}
    {binds binds' : List CppState.Binding} {slots slots' : List Location} {L0 T0 N scq SPB TPB W W' : Nat}
    (qs : QS outer P B sc cells binds slots) (qsI : QS inner P B (sc+1) (cells' ++ extra) binds' slots')
    (hty : cells'.map Cell.type = cells.map Cell.type)
    (faI : FA inner.frame L0 T0 scq N) (hsc : scq ≤ sc)
    (co : Cq SPB TPB W outer) (ci : Cq SPB TPB W' inner) (cap : liveS outer ≤ SPB) (hL : L0 ≤ TPB) :
    ∃ r, outer.leave inner none = some r ∧ QS r P B sc cells' binds slots ∧ FA r.frame L0 T0 scq N ∧
      Cq SPB TPB (W'+1) r := by
  have hm : inner.scalars.memory = (P ++ cells') ++ extra := by rw [qsI.memory,List.append_assoc]
  have hty' : (P ++ cells').map Cell.type = outer.scalars.memory.map Cell.type := by
    rw [qs.memory]; simp [hty]
  obtain ⟨leaveEq,memEq⟩ := leave_gen outer inner (P ++ cells') extra hm hty' faI.valid
    (by rw [qs.scope]; exact faI.fresh hsc)
  have lens : (P ++ cells').length = outer.scalars.memory.length := by
    have := congrArg List.length hty'; simpa using this
  have lengthTake : (inner.scalars.memory.take outer.scalars.memory.length).length = outer.scalars.memory.length := by
    rw [hm,← lens]; rw [List.take_left]
  refine ⟨outer.left inner,leaveEq,⟨?_,?_,?_,?_,?_⟩,?_,?_⟩
  · rw [left_slots]; exact qs.slots
  · rw [memEq]
  · rw [left_bindings]; exact qs.bindings
  · rw [left_baseMemory]; exact qs.base
  · rw [left_scope]; exact qs.scope
  · refine faI.noop (by rw [left_state]; exact noopRetired_same _) (by rw [left_rootWritable]) ?_ ?_
    · rw [left_state]; rfl
    · rw [left_frameBindings,faI.bindings]; exact List.take_nil
  · refine Cb.left co ci lengthTake cap ?_
    have e : (fx SPB TPB).TPB = TPB := rfl
    rw [faI.live]; omega

-- Scope exit with the frame facts supplied abstractly.
theorem leave_core {outer inner : NState} {P : List Cell} {B sc : Nat} {cells cells' extra : List Cell}
    {binds binds' : List CppState.Binding} {slots slots' : List Location} {SPB TPB W W' : Nat}
    (qs : QS outer P B sc cells binds slots) (qsI : QS inner P B (sc+1) (cells' ++ extra) binds' slots')
    (hty : cells'.map Cell.type = cells.map Cell.type)
    (valid : inner.frame.state.wellFormed = true)
    (fresh : ∀ owner, inner.frame.state.forest.context owner ≠ some (sc+1))
    (hlive : inner.frame.state.liveSpace-inner.frame.state.storage.baseSpace ≤ TPB)
    (co : Cq SPB TPB W outer) (ci : Cq SPB TPB W' inner) (cap : liveS outer ≤ SPB) :
    ∃ r, outer.leave inner none = some r ∧ QS r P B sc cells' binds slots ∧
      r.frame.state = (noopRetired inner.frame).state ∧ r.frame.rootWritable = inner.frame.rootWritable ∧
      r.frame.bindings = inner.frame.bindings.take outer.frame.bindings.length ∧ Cq SPB TPB (W'+1) r := by
  have hm : inner.scalars.memory = (P ++ cells') ++ extra := by rw [qsI.memory,List.append_assoc]
  have hty' : (P ++ cells').map Cell.type = outer.scalars.memory.map Cell.type := by
    rw [qs.memory]; simp [hty]
  obtain ⟨leaveEq,memEq⟩ := leave_gen outer inner (P ++ cells') extra hm hty' valid (by rw [qs.scope]; exact fresh)
  have lens : (P ++ cells').length = outer.scalars.memory.length := by
    have := congrArg List.length hty'; simpa using this
  have lengthTake : (inner.scalars.memory.take outer.scalars.memory.length).length = outer.scalars.memory.length := by
    rw [hm,← lens]; rw [List.take_left]
  refine ⟨outer.left inner,leaveEq,⟨?_,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
  · rw [left_slots]; exact qs.slots
  · rw [memEq]
  · rw [left_bindings]; exact qs.bindings
  · rw [left_baseMemory]; exact qs.base
  · rw [left_scope]; exact qs.scope
  · rw [left_state]
  · rw [left_rootWritable]
  · rw [left_frameBindings]
  · exact Cb.left co ci lengthTake cap hlive

end Proofs.QuotientFrame
