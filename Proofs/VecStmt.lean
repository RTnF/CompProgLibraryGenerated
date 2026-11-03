import Proofs.VecExpr

namespace Proofs.VecStmt
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppMixedInvoke
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.FlatVectorStmt Proofs.QuotientFrame
open Proofs.StraightLine Proofs.VecExpr Proofs.Mod61Body
open Proofs.CppState (Cell)

-- The statement lemmas of CppNestedStmt, for an expression whose evaluation is given as an `Ev`.
theorem declare_good_g (e : NExpr) (ty : Ty) (writable : Bool) (s t0 : NState) (v v' : Int) (w p : Nat)
    (ran : e.eval s = some (t0,v)) (good : Good s t0 w p) (hp : 1 ≤ p) (converted : ty.convert v = some v') :
    ∃ t, (NStmt.declare ty writable e).run s = some ⟨t,none,false⟩ ∧
      t.frame = s.frame ∧ t.slots = s.slots ++ [.scalar s.scalars.bindings.length] ∧ t.scope = s.scope ∧
      t.scalars.memory = s.scalars.memory ++ [⟨ty,v'⟩] ∧
      t.scalars.bindings = s.scalars.bindings ++ [⟨s.scalars.memory.length,writable⟩] ∧
      t.scalars.baseMemory = s.scalars.baseMemory ∧
      s.scalars.work ≤ t.scalars.work ∧ t.scalars.work ≤ s.scalars.work+w+1 ∧
      s.scalars.peak ≤ t.scalars.peak ∧ t.scalars.peak ≤ max s.scalars.peak (liveS s+p+1) ∧
      s.peak ≤ t.peak ∧ t.peak ≤ max s.peak (t.scalars.peak+t.frame.state.storage.peak) := by
  have run := declare_run e ty writable s t0 v v' ran converted
  rw [release_self good.1.1] at run
  obtain ⟨⟨f,sl,sc,m,b,k⟩,l,u,st,pl,pu,ql,qu⟩ := good
  refine ⟨_,run,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [NState.declared,f]
  · simp [NState.declared,sl,b]
  · simp [NState.declared,sc]
  · simp [NState.declared,m]
  · simp [NState.declared,b,m]
  · simp [NState.declared,k]
  · simp [NState.declared,charge_work]; omega
  · simp [NState.declared,charge_work]; omega
  · simp [NState.declared,charge_scalar_peak]; omega
  · simp [NState.declared,charge_scalar_peak,liveS,m,b,k]; unfold liveS at pu; omega
  · simp [NState.declared,charge_peak]; omega
  · simp [NState.declared,charge_peak,charge_scalar_peak,f]
    have st' : t0.frame.state.storage.peak = s.frame.state.storage.peak := by rw [st]
    simp [f] at qu
    omega


theorem assign_good_g (e : NExpr) (slot idx : Nat) (ty : Ty) (s t0 : NState) (v v' : Int) (w p : Nat)
    (binding : CppState.Binding) (cell : CppState.Cell)
    (ran : e.eval s = some (t0,v)) (good : Good s t0 w p) (converted : ty.convert v = some v')
    (hs : s.slots[slot]? = some (.scalar idx)) (hb : s.scalars.bindings[idx]? = some binding)
    (hm : s.scalars.memory[binding.address]? = some cell) (ctype : cell.type = ty)
    (cvalid : ty.valid cell.value = true) (writable : binding.writable = true) :
    ∃ t, (NStmt.assign slot ty e).run s = some ⟨t,none,false⟩ ∧
      t.frame = s.frame ∧ t.slots = s.slots ∧ t.scope = s.scope ∧
      t.scalars.memory = s.scalars.memory.set binding.address ⟨ty,v'⟩ ∧
      t.scalars.bindings = s.scalars.bindings ∧ t.scalars.baseMemory = s.scalars.baseMemory ∧
      s.scalars.work ≤ t.scalars.work ∧ t.scalars.work ≤ s.scalars.work+w+1 ∧
      s.scalars.peak ≤ t.scalars.peak ∧ t.scalars.peak ≤ max s.scalars.peak (liveS s+p) ∧
      s.peak ≤ t.peak ∧ t.peak ≤ max s.peak (t.scalars.peak+t.frame.state.storage.peak) ∧
      liveS t = liveS s := by
  have self := release_self good.1.1
  have cellFound : (t0.release s).scalarCell slot ty = some (binding,cell) := by
    rw [self]
    obtain ⟨⟨f,sl,sc,m,b,k⟩,_⟩ := good
    simp [NState.scalarCell,NState.scalarSlot,sl,b,m,hs,hb,hm,ctype,cvalid]
  have run := assign_run e slot ty s t0 v v' binding cell ran cellFound writable converted
  rw [self] at run
  obtain ⟨⟨f,sl,sc,m,b,k⟩,l,u,st,pl,pu,ql,qu⟩ := good
  refine ⟨_,run,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa using f
  · simpa using sl
  · simpa using sc
  · simp [m,ctype]
  · simpa using b
  · simpa using k
  · simp [charge_work]; omega
  · simp [charge_work]; omega
  · simp [charge_scalar_peak]; omega
  · simp [charge_scalar_peak,liveS,m,b,k]
    have mlen : (s.scalars.memory.set binding.address ⟨ty,v'⟩).length = s.scalars.memory.length := by simp
    simp [mlen]
    unfold liveS at pu; omega
  · simp [charge_peak]; omega
  · simp [charge_peak,charge_scalar_peak,f]
    have st' : t0.frame.state.storage.peak = s.frame.state.storage.peak := by rw [st]
    simp [f] at qu
    omega
  · simp [liveS,m,b,k]

theorem check_good_g (e : NExpr) (s t0 : NState) (v : Int) (w p : Nat)
    (ran : e.eval s = some (t0,v)) (good : Good s t0 w p) (nonzero : v ≠ 0) :
    ∃ t, (NStmt.check e).run s = some ⟨t,none,false⟩ ∧ Good s t (w+1) p := by
  have run := check_run e s t0 v ran nonzero
  rw [release_self good.1.1] at run
  exact ⟨_,run,(good.trans (Good.charge t0 1 0)).mono (by omega) (by omega)⟩

theorem decl_stepG {P : List Cell} {B scope : Nat} {cells : List Cell} {binds : List CppState.Binding}
    {slots : List Location} {SPB TPB W : Nat} (S t0 : NState) (e : NExpr) (ty : Ty) (writable : Bool) (v v' : Int)
    (w p : Nat) (qs : QS S P B scope cells binds slots) (cq : Cq SPB TPB W S) (cap : liveS S+p+1 ≤ SPB)
    (ran : e.eval S = some (t0,v)) (good : Good S t0 w p) (hp : 1 ≤ p) (conv : ty.convert v = some v') :
    ∃ t, (NStmt.declare ty writable e).run S = some ⟨t,none,false⟩ ∧ t.frame = S.frame ∧
      QS t P B scope (cells ++ [⟨ty,v'⟩]) (binds ++ [⟨P.length+cells.length,writable⟩])
        (slots ++ [.scalar binds.length]) ∧ Cq SPB TPB (W+w+1) t := by
  obtain ⟨t,run,frame,sl,sc,me,bi,ba,wl,wu,pl,pu,ql,qu⟩ := declare_good_g e ty writable S t0 v v' w p ran good hp conv
  have memLen : S.scalars.memory.length = P.length+cells.length := by simp [qs.memory]
  have bindLen : S.scalars.bindings.length = binds.length := by simp [qs.bindings]
  refine ⟨t,run,frame,⟨?_,?_,?_,?_,?_⟩,?_⟩
  · rw [sl,bindLen,qs.slots]
  · rw [me,qs.memory]; simp
  · rw [bi,memLen,qs.bindings]
  · rw [ba]; exact qs.base
  · rw [sc]; exact qs.scope
  · exact Cb.step (w := w+1) (p := p+1) cq frame (by omega) pu cap qu

theorem assign_stepG {P : List Cell} {B scope : Nat} {cells cells' : List Cell} {binds : List CppState.Binding}
    {slots : List Location} {SPB TPB W : Nat} (S t0 : NState) (e : NExpr) (slot idx : Nat) (ty : Ty) (v v' : Int)
    (w p : Nat) (binding : CppState.Binding) (cell : Cell)
    (qs : QS S P B scope cells binds slots) (cq : Cq SPB TPB W S) (cap : liveS S+p ≤ SPB)
    (ran : e.eval S = some (t0,v)) (good : Good S t0 w p) (conv : ty.convert v = some v')
    (hs : slots[slot]? = some (.scalar idx)) (hb : binds[idx]? = some binding)
    (hm : (P ++ cells)[binding.address]? = some cell) (ctype : cell.type = ty) (cvalid : ty.valid cell.value = true)
    (writable : binding.writable = true)
    (hcells : (P ++ cells).set binding.address ⟨ty,v'⟩ = P ++ cells') :
    ∃ t, (NStmt.assign slot ty e).run S = some ⟨t,none,false⟩ ∧ t.frame = S.frame ∧
      QS t P B scope cells' binds slots ∧ Cq SPB TPB (W+w+1) t := by
  obtain ⟨t,run,frame,sl,sc,me,bi,ba,wl,wu,pl,pu,ql,qu,live⟩ := assign_good_g e slot idx ty S t0 v v' w p binding cell
    ran good conv (by rw [qs.slots]; exact hs) (by rw [qs.bindings]; exact hb)
    (by rw [qs.memory]; exact hm) ctype cvalid writable
  refine ⟨t,run,frame,⟨?_,?_,?_,?_,?_⟩,?_⟩
  · rw [sl]; exact qs.slots
  · rw [me,qs.memory,hcells]
  · rw [bi]; exact qs.bindings
  · rw [ba]; exact qs.base
  · rw [sc]; exact qs.scope
  · exact Cb.step (w := w+1) (p := p) cq frame (by omega) pu cap qu

end Proofs.VecStmt
