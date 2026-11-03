import Proofs.DoublingPrologue

namespace Proofs.CountLoop
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppMixedInvoke
open Proofs.DoublingNested Proofs.DoublingPrologue
open Proofs.CppState (Cell)

-- The callee's scalar parameters and locals are all writable i32 cells after the P prefix.
def bn (F : Fixed) (k : Nat) : List CppState.Binding := (List.range k).map fun j => ⟨F.P.length+j,true⟩
def sl (k : Nat) : List Location := .vector 0 :: (List.range k).map fun j => .scalar j

theorem bn_succ (F : Fixed) (k : Nat) : bn F (k+1) = bn F k ++ [⟨F.P.length+k,true⟩] := by
  simp [bn,List.range_succ]

theorem sl_succ (k : Nat) : sl (k+1) = sl k ++ [.scalar k] := by
  simp [sl,List.range_succ]

theorem bn_length (F : Fixed) (k : Nat) : (bn F k).length = k := by simp [bn]

theorem env_gen (F : Fixed) {sc : Nat} {rw0 : List Bool} {cells : List Cell} {k : Nat} (S : NState)
    (ps : PS F sc rw0 S cells (bn F k) (sl k)) (idx : Nat) (x : Int) (hidx : idx < k)
    (hcell : cells[idx]? = some ⟨i32,x⟩) (valid : i32.valid x = true) :
    envOf S (idx+1) i32 = some x := by
  refine envOf_at S (idx+1) idx ⟨F.P.length+idx,true⟩ i32 x ?_ ?_ ?_ valid
  · simp [ps.slots,sl,hidx]
  · simp [ps.bindings,bn,hidx]
  · simp [ps.memory,List.getElem?_append_right,hcell]

theorem decl_gen (F : Fixed) {sc : Nat} {rw0 : List Bool} {W k : Nat} {cells : List Cell} (S : NState)
    (e : NExpr) (x : Int) (hk : cells.length = k) (ps : PS F sc rw0 S cells (bn F k) (sl k)) (cb : Cb F W S)
    (scalar : e.scalarOnly = true) (value : e.denote (envOf S) = some x) (xv : i32.valid x = true)
    (cap : liveS S+e.nodes+1 ≤ F.SPB) :
    ∃ t, (NStmt.declare i32 true e).run S = some ⟨t,none,false⟩ ∧
      PS F sc rw0 t (cells ++ [⟨i32,x⟩]) (bn F (k+1)) (sl (k+1)) ∧ t.frame = S.frame ∧ Cb F (W+e.nodes+1) t := by
  obtain ⟨t,run,frame,sl',sc',me,bi,ba,wl,wu,pl,pu,ql,qu⟩ := declare_good e i32 true S x x scalar value
    (Ty.convert_of_valid _ _ xv)
  have memLen : S.scalars.memory.length = F.P.length+k := by simp [ps.memory,hk]
  have bindLen : S.scalars.bindings.length = k := by simp [ps.bindings,bn_length]
  refine ⟨t,run,⟨?_,?_,?_,?_,?_,?_,?_⟩,frame,?_⟩
  · rw [sl',bindLen,ps.slots,sl_succ]
  · rw [me,ps.memory]; simp
  · rw [bi,memLen,ps.bindings,bn_succ]
  · rw [ba]; exact ps.base
  · rw [sc']; exact ps.scope
  · rw [frame]; exact ps.frameBindings
  · rw [frame]; exact ps.writable
  · exact cb.step (w := e.nodes+1) (p := e.nodes+1) frame (by omega) pu cap qu

theorem assign_of_good (e : NExpr) (slot idx : Nat) (ty : Ty) (s t0 : NState) (v v' : Int) (w p : Nat)
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

theorem assign_gen (F : Fixed) {sc : Nat} {rw0 : List Bool} {W k : Nat} {cells : List Cell} (S : NState)
    (e : NExpr) (idx : Nat) (old x : Int) (hidx : idx < k) (hk : cells.length = k)
    (hcell : cells[idx]? = some ⟨i32,old⟩) (oldv : i32.valid old = true)
    (ps : PS F sc rw0 S cells (bn F k) (sl k)) (cb : Cb F W S)
    (scalar : e.scalarOnly = true) (value : e.denote (envOf S) = some x) (xv : i32.valid x = true)
    (cap : liveS S+e.nodes ≤ F.SPB) :
    ∃ t, (NStmt.assign (idx+1) i32 e).run S = some ⟨t,none,false⟩ ∧
      PS F sc rw0 t (cells.set idx ⟨i32,x⟩) (bn F k) (sl k) ∧ t.frame = S.frame ∧ Cb F (W+e.nodes+1) t := by
  obtain ⟨t0,ran,good⟩ := scalar_eval e S x scalar value
  have hs : S.slots[idx+1]? = some (.scalar idx) := by simp [ps.slots,sl,hidx]
  have hb : S.scalars.bindings[idx]? = some ⟨F.P.length+idx,true⟩ := by simp [ps.bindings,bn,hidx]
  have hm : S.scalars.memory[F.P.length+idx]? = some ⟨i32,old⟩ := by
    simp [ps.memory,List.getElem?_append_right,hcell]
  obtain ⟨t,run,frame,sl',sc',me,bi,ba,wl,wu,pl,pu,ql,qu,live⟩ := assign_of_good e (idx+1) idx i32 S t0 x x e.nodes e.nodes
    ⟨F.P.length+idx,true⟩ ⟨i32,old⟩ ran good (Ty.convert_of_valid _ _ xv) hs hb hm rfl oldv rfl
  refine ⟨t,run,⟨?_,?_,?_,?_,?_,?_,?_⟩,frame,?_⟩
  · rw [sl']; exact ps.slots
  · rw [me,ps.memory]; simp [List.set_append_right]
  · rw [bi]; exact ps.bindings
  · rw [ba]; exact ps.base
  · rw [sc']; exact ps.scope
  · rw [frame]; exact ps.frameBindings
  · rw [frame]; exact ps.writable
  · exact cb.step (w := e.nodes+1) (p := e.nodes) frame (by omega) pu cap qu


def C5 (v b e c i : Int) : List Cell := [⟨i32,v⟩,⟨i32,b⟩,⟨i32,e⟩,⟨i32,c⟩,⟨i32,i⟩]

abbrev ix : NExpr := .cast u64 (.variable i32 5)
abbrev cmpE : NExpr := .binary bl .eq (.read i32 (.local 0) ix) (.variable i32 1)
abbrev incCnt : NExpr := .binary i32 .add (.variable i32 4) (.literal i32 1)
abbrev incI : NExpr := .binary i32 .add (.variable i32 5) (.literal i32 1)
abbrev yesC : Command := .sequence (.scope (.sequence (.primitive (.assign 4 i32 incCnt)) (.primitive .skip))) (.primitive .skip)
abbrev ifC : Command := .branch cmpE yesC (.primitive .skip)
abbrev ifScope : Command := .scope (.sequence ifC (.primitive .skip))
abbrev bodyC : Command := .sequence ifScope (.sequence (.primitive (.assign 5 i32 incI)) (.primitive .skip))
abbrev condC : NExpr := .binary bl .lt (.variable i32 5) (.variable i32 3)
abbrev loopC : Command := .whileLoop condC bodyC

theorem ix_scalar : ix.scalarOnly = true := by simp [NExpr.scalarOnly]
theorem incCnt_scalar : incCnt.scalarOnly = true := by simp [NExpr.scalarOnly]
theorem incI_scalar : incI.scalarOnly = true := by simp [NExpr.scalarOnly]
theorem condC_scalar : condC.scalarOnly = true := by simp [NExpr.scalarOnly]

-- Leaving a scalar-only scope in which some outer cells were overwritten with values of the same type.
theorem leave_set (F : Fixed) {sc : Nat} {rw0 : List Bool} {L0 T0 W W' : Nat} {cells cells' : List Cell}
    {binds : List CppState.Binding} {slots : List Location} (S tB : NState) (hsc : F.sc ≤ sc)
    (ps : PS F sc rw0 S cells binds slots) (psB : PS F (sc+1) rw0 tB cells' binds slots)
    (hty : cells'.map Cell.type = cells.map Cell.type)
    (vfB : VF F L0 T0 tB.frame) (hL : L0 ≤ F.TPB) (co : Cb F W S) (ci : Cb F W' tB) (cap : liveS S ≤ F.SPB) :
    ∃ restored, S.leave tB none = some restored ∧ PS F sc rw0 restored cells' binds slots ∧
      VF F L0 T0 restored.frame ∧ Cb F (W'+1) restored := by
  have lens : cells'.length = cells.length := by simpa using congrArg List.length hty
  have take : tB.scalars.memory.take S.scalars.memory.length = F.P ++ cells' := by
    rw [psB.memory,ps.memory]
    have : (F.P ++ cells).length = (F.P ++ cells').length := by simp [lens]
    rw [this]; exact List.take_length
  have fits : S.scalars.memory.length ≤ tB.scalars.memory.length := by
    rw [psB.memory,ps.memory]; simp [lens]
  have leaveEq : S.leave tB none = some (S.left tB) :=
    leave_scalar S tB none (by simp) fits
      (by rw [take,ps.memory]; simp [List.map_append,hty]) vfB.valid
      (by rw [ps.scope]; exact vfB.fresh hsc)
  have sameBind : tB.frame.bindings = S.frame.bindings := by rw [psB.frameBindings,ps.frameBindings]
  have lengthTake : (tB.scalars.memory.take S.scalars.memory.length).length = S.scalars.memory.length := by
    rw [take,ps.memory]; simp [lens]
  refine ⟨S.left tB,leaveEq,⟨?_,?_,?_,?_,?_,?_,?_⟩,?_,?_⟩
  · rw [left_slots]; exact ps.slots
  · rw [left_memory,take]
  · rw [left_bindings]; exact ps.bindings
  · rw [left_baseMemory]; exact ps.base
  · rw [left_scope]; exact ps.scope
  · rw [left_frameBindings,sameBind]; simpa using ps.frameBindings
  · rw [left_rootWritable]; exact psB.writable
  · refine vfB.of_same ?_ (by rw [left_rootWritable]) ?_
    · rw [left_state]; exact noopRetired_same _
    · rw [left_state]; rfl
  · refine co.left ci lengthTake cap ?_
    rw [vfB.live]; omega


theorem yes_phase (F : Fixed) {rw0 : List Bool} {L0 T0 W : Nat} {v b e : Int} {c i : Nat} (U : NState)
    (hsc : F.sc ≤ U.scope) (hL : L0 ≤ F.TPB) (hc : c+1 < 2147483648)
    (ps : PS F U.scope rw0 U (C5 v b e c i) (bn F 5) (sl 5)) (vf : VF F L0 T0 U.frame) (cb : Cb F W U)
    (cap : liveS U+30 ≤ F.SPB) :
    RunsTo yesC U fun step => step.returned = none ∧ step.breaking = false ∧
      PS F U.scope rw0 step.state (C5 v b e (c+1 : Nat) i) (bn F 5) (sl 5) ∧ VF F L0 T0 step.state.frame ∧
      Cb F (W+10) step.state := by
  have ps1 := ps.enter
  have cb1 := cb.enter
  have capEq : liveS ({U with scope := U.scope+1} : NState) = liveS U := rfl
  have cv : i32.valid (c : Int) = true := i32_valid_nat c (by omega)
  have cv1 : i32.valid ((c : Int)+1) = true := by simp [Ty.valid]; omega
  have e4 : envOf ({U with scope := U.scope+1} : NState) 4 i32 = some (c : Int) :=
    env_gen F _ ps1 3 (c : Int) (by decide) (by simp [C5]) cv
  have lit : i32.valid (1 : Int) = true := by simp [Ty.valid]
  have value : incCnt.denote (envOf ({U with scope := U.scope+1} : NState)) = some ((c : Int)+1) :=
    denote_inc _ 4 i32 c e4 lit (Ty.convert_of_valid _ _ cv1)
  obtain ⟨t,run,psT,frame,cbT⟩ := assign_gen (k := 5) F _ incCnt 3 (c : Int) ((c : Int)+1) (by decide) (by simp [C5])
    (by simp [C5]) cv ps1 cb1 incCnt_scalar value cv1 (by rw [capEq]; simp [NExpr.nodes]; omega)
  have cells : (C5 v b e c i).set 3 ⟨i32,(c : Int)+1⟩ = C5 v b e (c+1 : Nat) i := by
    simp [C5]
  rw [cells] at psT
  have vfT : VF F L0 T0 t.frame := vf.of_eq (by simpa using frame)
  obtain ⟨restored,leaveEq,psR,vfR,cbR⟩ := leave_set F U t hsc ps psT (by simp [C5]) vfT hL cb
    (cbT.mono (Nat.le_refl _)) (by omega)
  apply RunsTo.seqSkip
  apply RunsTo.scopeSimple
  apply RunsTo.seq
  apply RunsTo.primitive run
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.skip
  refine ⟨rfl,rfl,?_⟩
  refine ⟨restored,leaveEq,rfl,rfl,rfl,rfl,psR,vfR,cbR.mono ?_⟩
  simp [NExpr.nodes]


theorem ix_value (F : Fixed) {sc : Nat} {rw0 : List Bool} {cells : List Cell} {k : Nat} (S : NState) (j : Nat)
    (hj : j < 2147483648) (ps : PS F sc rw0 S cells (bn F k) (sl k)) (hk : 4 < k)
    (hcell : cells[4]? = some ⟨i32,(j : Int)⟩) :
    ix.denote (envOf S) = some (j : Int) := by
  have e5 := env_gen F S ps 4 (j : Int) hk hcell (i32_valid_nat j hj)
  have valid : u64.valid (j : Int) = true := u64_valid_nat j (by omega)
  simp [NExpr.denote,e5,Ty.convert_of_valid _ _ valid]

theorem item_val (F : Fixed) (items : List Int) (hv : F.vbuf.items = items.map Value.integer) (i : Nat)
    (hi : i < items.length) : ∃ x : Int, F.vbuf.items[i]? = some (Value.integer x) ∧ items[i]? = some x :=
  ⟨items[i],by rw [hv]; simp [List.getElem?_map,hi],by simp [hi]⟩

theorem if_phase (F : Fixed) (items : List Int) (hv : F.vbuf.items = items.map Value.integer)
    {rw0 : List Bool} {L0 T0 W : Nat} {v b e : Int} {c i : Nat} (S : NState)
    (hi : i < items.length) (hn : items.length < 2147483648) (hsc : F.sc ≤ S.scope) (hL : L0 ≤ F.TPB)
    (hc : c+1 < 2147483648) (vv : i32.valid v = true)
    (ps : PS F S.scope rw0 S (C5 v b e c i) (bn F 5) (sl 5)) (vf : VF F L0 T0 S.frame) (cb : Cb F W S)
    (cap : liveS S+60 ≤ F.SPB) :
    RunsTo ifScope S fun step => step.returned = none ∧ step.breaking = false ∧
      PS F S.scope rw0 step.state (C5 v b e (c+(if items[i]? = some v then 1 else 0) : Nat) i) (bn F 5) (sl 5) ∧
      VF F L0 T0 step.state.frame ∧ Cb F (W+60) step.state := by
  have ps1 := ps.enter
  have cb1 := cb.enter
  have capEq : liveS ({S with scope := S.scope+1} : NState) = liveS S := rfl
  have hs : ({S with scope := S.scope+1} : NState).vectorSlot 0 = some 0 := by
    simp [NState.vectorSlot,ps.slots,sl]
  have vf1 : VF F L0 T0 ({S with scope := S.scope+1} : NState).frame := vf
  obtain ⟨x,item,itemE⟩ := item_val F items hv i hi
  have idx := ix_value F ({S with scope := S.scope+1} : NState) i (by omega) ps1 (by decide) (by simp [C5])
  obtain ⟨t1,first⟩ := readV_ev F ({S with scope := S.scope+1} : NState)
    (({S with scope := S.scope+1} : NState).charge 0 ((NExpr.read i32 (.local 0) ix).nodes+(NExpr.variable i32 1).nodes+1))
    (core_charge _ _ _) hs ps1.frameBindings vf1 ix i ix_scalar idx x item
  have core1 : Core ({S with scope := S.scope+1} : NState) t1 := (core_charge _ _ _).trans (Ev.good first).1
  have env1 := env_gen F ({S with scope := S.scope+1} : NState) ps1 0 v (by decide) (by simp [C5]) vv
  have varScalar : (NExpr.variable i32 1).scalarOnly = true := by simp [NExpr.scalarOnly]
  obtain ⟨t2,second⟩ := Ev.scalar varScalar (v := v) (by simp [NExpr.denote,envOf_core core1,env1]) (s := t1)
  have conv : bl.convert (binaryValue .eq x v) = some (if x = v then 1 else 0) := by
    have bv : binaryValue .eq x v = if x = v then 1 else 0 := by
      by_cases h : x = v <;> simp [binaryValue,h]
    rw [bv]
    exact Ty.convert_of_valid bl _ (by by_cases h : x = v <;> simp [h,Ty.valid])
  have ev := Ev.binary first second conv
  obtain ⟨next,w,p,ev',hw,hp⟩ : ∃ next w p, Ev ({S with scope := S.scope+1} : NState) cmpE next
      (if x = v then (1 : Int) else 0) [] w p ∧ w ≤ 40 ∧ p ≤ 40 :=
    ⟨_,_,_,by simpa using ev,by simp [NExpr.nodes,Container.nodes],by simp [NExpr.nodes,Container.nodes]⟩
  have good := Ev.good ev'
  have self := release_self good.1.1
  have liveN : liveS next = liveS S := (liveS_core good.1).trans capEq
  have cbN : Cb F (W+w) next := cb1.good good (by rw [capEq]; omega)
  have coreU : Core ({S with scope := S.scope+1} : NState) (next.charge 1 0) := good.1.trans (core_charge next 1 0)
  have psU : PS F (S.scope+1) rw0 (next.charge 1 0) (C5 v b e c i) (bn F 5) (sl 5) := ps1.core coreU
  have eqs : (next.charge 1 0).scope = S.scope+1 := psU.scope
  have vfU : VF F L0 T0 (next.charge 1 0).frame := vf.of_eq (by simpa using good.1.1)
  have cbU : Cb F (W+w+1) (next.charge 1 0) := cbN.good (Good.charge next 1 0) (by omega)
  have liveU : liveS (next.charge 1 0) = liveS S := (liveS_core coreU).trans capEq
  apply RunsTo.scopeSimple
  apply RunsTo.seqSkip
  by_cases hx : x = v
  · subst hx
    have ival : (if x = x then (1 : Int) else 0) = 1 := by simp
    have hcond : (if items[i]? = some x then 1 else 0) = 1 := by rw [itemE]; simp
    apply RunsTo.branch (next := next) (value := if x = x then 1 else 0) (Ev.eval ev')
    rw [ival, if_neg (by decide), self]
    refine (yes_phase F (U := next.charge 1 0) (by rw [eqs]; omega) hL hc (psU.self) vfU cbU
      (by rw [liveU]; omega)).mono ?_
    intro step ⟨nr,nb,psE,vfE,cbE⟩
    rw [eqs] at psE
    obtain ⟨restored,leaveEq,psR,vfR,cbR⟩ := leave_set F S step.state hsc ps psE (by simp [C5]) vfE hL cb cbE
      (by omega)
    rw [hcond]
    exact ⟨nr,nb,rfl,rfl,restored,leaveEq,rfl,rfl,psR,vfR,cbR.mono (by omega)⟩
  · have ival : (if x = v then (1 : Int) else 0) = 0 := by simp [hx]
    have hcond : (if items[i]? = some v then 1 else 0) = 0 := by
      rw [itemE]; simp [hx]
    apply RunsTo.branch (next := next) (value := if x = v then 1 else 0) (Ev.eval ev')
    rw [ival, if_pos rfl, self]
    obtain ⟨restored,leaveEq,psR,vfR,cbR⟩ := leave_set F S (next.charge 1 0) hsc ps
      psU (by simp [C5]) vfU hL cb cbU (by omega)
    apply RunsTo.skip
    rw [hcond]
    exact ⟨rfl,rfl,rfl,rfl,restored,leaveEq,rfl,rfl,psR,vfR,cbR.mono (by omega)⟩


-- Number of positions among b, ..., b+k-1 whose entry equals x.
def cntU (items : List Int) (x : Int) (b : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => cntU items x b k + (if items[b+k]? = some x then 1 else 0)

theorem cntU_le (items : List Int) (x : Int) (b k : Nat) : cntU items x b k ≤ k := by
  induction k with
  | zero => simp [cntU]
  | succ k ih => simp only [cntU]; split <;> omega

theorem body_phase (F : Fixed) (items : List Int) (hv : F.vbuf.items = items.map Value.integer)
    {rw0 : List Bool} {L0 T0 W : Nat} {v b e : Int} {c i : Nat} (S : NState)
    (hi : i < items.length) (hn : items.length < 2147483648) (hsc : F.sc ≤ S.scope) (hL : L0 ≤ F.TPB)
    (hc : c+1 < 2147483648) (vv : i32.valid v = true)
    (ps : PS F S.scope rw0 S (C5 v b e c i) (bn F 5) (sl 5)) (vf : VF F L0 T0 S.frame) (cb : Cb F W S)
    (cap : liveS S+60 ≤ F.SPB) :
    RunsTo bodyC S fun step => step.returned = none ∧ step.breaking = false ∧
      PS F S.scope rw0 step.state (C5 v b e (c+(if items[i]? = some v then 1 else 0) : Nat) (i+1 : Nat))
        (bn F 5) (sl 5) ∧ VF F L0 T0 step.state.frame ∧ Cb F (W+100) step.state := by
  apply RunsTo.seq
  refine (if_phase F items hv S hi hn hsc hL hc vv ps vf cb cap).mono ?_
  intro mid ⟨nr,nb,psM,vfM,cbM⟩
  refine ⟨nr,nb,?_⟩
  have liveM : liveS mid.state = liveS S := by rw [psM.live_eq,ps.live_eq]; simp [C5]
  have ci : i32.valid (i : Int) = true := i32_valid_nat i (by omega)
  have ci1 : i32.valid ((i+1 : Nat) : Int) = true := i32_valid_nat (i+1) (by omega)
  have e5 := env_gen F mid.state psM 4 (i : Int) (by decide) (by simp [C5]) ci
  have lit : i32.valid (1 : Int) = true := by simp [Ty.valid]
  have value : incI.denote (envOf mid.state) = some ((i+1 : Nat) : Int) := by
    have := denote_inc (envOf mid.state) 5 i32 i e5 lit (Ty.convert_of_valid _ _ (by simpa using ci1))
    simpa using this
  obtain ⟨t,run,psT,frame,cbT⟩ := assign_gen (k := 5) F mid.state incI 4 (i : Int) ((i+1 : Nat) : Int) (by decide)
    (by simp [C5]) (by simp [C5]) ci psM cbM incI_scalar value ci1 (by rw [liveM]; simp [NExpr.nodes]; omega)
  have cells : (C5 v b e (c+(if items[i]? = some v then 1 else 0) : Nat) i).set 4 ⟨i32,((i+1 : Nat) : Int)⟩ =
      C5 v b e (c+(if items[i]? = some v then 1 else 0) : Nat) (i+1 : Nat) := by
    simp [C5]
  rw [cells] at psT
  apply RunsTo.seqSkip
  apply RunsTo.primitive run
  exact ⟨rfl,rfl,rfl,rfl,psT,vfM.of_eq frame,cbT.mono (by simp [NExpr.nodes])⟩

theorem count_loop (F : Fixed) (items : List Int) (hv : F.vbuf.items = items.map Value.integer)
    {rw0 : List Bool} {L0 T0 W : Nat} {v : Int} {b E : Nat} (S : NState)
    (hE : E ≤ items.length) (hn : items.length < 2147483648) (hb : b < 2147483648)
    (hsc : F.sc ≤ S.scope) (hL : L0 ≤ F.TPB) (vv : i32.valid v = true)
    (ps : PS F S.scope rw0 S (C5 v b E 0 b) (bn F 5) (sl 5)) (vf : VF F L0 T0 S.frame) (cb : Cb F W S)
    (cap : liveS S+60 ≤ F.SPB) :
    RunsTo loopC S fun step => step.returned = none ∧ step.breaking = false ∧
      PS F S.scope rw0 step.state (C5 v b E (cntU items v b (E-b) : Nat) (b+(E-b) : Nat)) (bn F 5) (sl 5) ∧
      VF F L0 T0 step.state.frame ∧ Cb F (W+(E-b)*108+8) step.state := by
  have liveS0 : liveS S = F.P.length+5-F.B+5 := by
    rw [ps.live_eq]; simp [C5,bn_length]
  refine RunsTo.whileGhost (fun g t => ∃ k, g = (E-b)-k ∧ k ≤ E-b ∧
      PS F S.scope rw0 t (C5 v b E (cntU items v b k : Nat) (b+k : Nat)) (bn F 5) (sl 5) ∧
      VF F L0 T0 t.frame ∧ Cb F (W+k*108) t) _ ?_ (E-b) (E-b) S (Nat.le_refl _) ⟨0,by omega,by omega,by simpa [cntU] using ps,vf,by simpa using cb⟩
  intro g t ⟨k,hg,hk,pt,vft,cbt⟩
  have liveT : liveS t = liveS S := by rw [pt.live_eq,ps.live_eq]; simp [C5]
  have ei := env_gen F t pt 4 ((b+k : Nat) : Int) (by decide) (by simp [C5]) (i32_valid_nat _ (by omega))
  have ee := env_gen F t pt 2 (E : Int) (by decide) (by simp [C5]) (i32_valid_nat E (by omega))
  have value : condC.denote (envOf t) = some (if ((b+k : Nat) : Int) < (E : Int) then 1 else 0) :=
    denote_lt (envOf t) 5 3 i32 _ _ ei ee
  obtain ⟨u,hu,good⟩ := scalar_eval condC t _ condC_scalar value
  have self := release_self good.1.1
  have cbU : Cb F (W+k*108+4) u := (cbt.good good (by simp [NExpr.nodes]; omega)).mono (by simp [NExpr.nodes])
  have liveU0 : liveS u = liveS t := liveS_core good.1
  have cbC : Cb F (W+k*108+8) (u.charge 1 0) :=
    (cbU.good (Good.charge u 1 0) (by omega)).mono (by omega)
  have coreU : Core t (u.charge 1 0) := good.1.trans (core_charge u 1 0)
  have ptU : PS F S.scope rw0 (u.charge 1 0) (C5 v b E (cntU items v b k : Nat) (b+k : Nat)) (bn F 5) (sl 5) :=
    pt.core coreU
  have vfU : VF F L0 T0 (u.charge 1 0).frame := vft.of_eq (by simpa using good.1.1)
  refine ⟨u,_,hu,?_,?_⟩
  · intro zero
    have notLt : ¬ (b+k < E) := by
      intro h
      have : (((b+k : Nat) : Int) < (E : Int)) := by omega
      rw [if_pos this] at zero
      exact absurd zero (by decide)
    have eq : k = E-b := by omega
    subst eq
    rw [self]
    exact ⟨rfl,rfl,ptU,vfU,cbC.mono (by omega)⟩
  · intro nonzero
    have lt : b+k < E := by
      by_cases h : b+k < E
      · exact h
      · have : ¬ (((b+k : Nat) : Int) < (E : Int)) := by omega
        rw [if_neg this] at nonzero
        exact absurd rfl nonzero
    rw [self]
    have scopeU : (u.charge 1 0).scope = S.scope := ptU.scope
    have capU : liveS (u.charge 1 0)+60 ≤ F.SPB := by
      rw [(liveS_core coreU).trans liveT]; omega
    have cle := cntU_le items v b k
    have body := body_phase F items hv (W := W+k*108+8) (u.charge 1 0) (c := cntU items v b k) (i := b+k)
      (by omega) hn (by rw [scopeU]; exact hsc) hL (by omega) vv (by rw [scopeU]; exact ptU) vfU cbC capU
    refine body.mono ?_
    intro step ⟨nr,nb,psE,vfE,cbE⟩
    refine ⟨nr,nb,E-b-(k+1),by omega,k+1,rfl,by omega,?_,vfE,cbE.mono (by omega)⟩
    rw [scopeU] at psE
    have e1 : (cntU items v b k + (if items[b+k]? = some v then 1 else 0)) = cntU items v b (k+1) := rfl
    have e2 : b+k+1 = b+(k+1) := by omega
    rw [e1,e2] at psE
    exact psE


-- Like `leave_set`, and the inner scope may also have declared extra cells.
theorem leave_ext (F : Fixed) {sc : Nat} {rw0 : List Bool} {L0 T0 W W' : Nat} {cells cells' extra : List Cell}
    {binds binds' : List CppState.Binding} {slots slots' : List Location} (S tB : NState) (hsc : F.sc ≤ sc)
    (ps : PS F sc rw0 S cells binds slots) (psB : PS F (sc+1) rw0 tB (cells' ++ extra) binds' slots')
    (hty : cells'.map Cell.type = cells.map Cell.type)
    (vfB : VF F L0 T0 tB.frame) (hL : L0 ≤ F.TPB) (co : Cb F W S) (ci : Cb F W' tB) (cap : liveS S ≤ F.SPB) :
    ∃ restored, S.leave tB none = some restored ∧ PS F sc rw0 restored cells' binds slots ∧
      VF F L0 T0 restored.frame ∧ Cb F (W'+1) restored := by
  have lens : cells'.length = cells.length := by simpa using congrArg List.length hty
  have take : tB.scalars.memory.take S.scalars.memory.length = F.P ++ cells' := by
    rw [psB.memory,ps.memory,← List.append_assoc]
    have : (F.P ++ cells).length = (F.P ++ cells').length := by simp [lens]
    rw [this]; exact List.take_left
  have fits : S.scalars.memory.length ≤ tB.scalars.memory.length := by
    rw [psB.memory,ps.memory]; simp [lens]
  have leaveEq : S.leave tB none = some (S.left tB) :=
    leave_scalar S tB none (by simp) fits
      (by rw [take,ps.memory]; simp [List.map_append,hty]) vfB.valid
      (by rw [ps.scope]; exact vfB.fresh hsc)
  have sameBind : tB.frame.bindings = S.frame.bindings := by rw [psB.frameBindings,ps.frameBindings]
  have lengthTake : (tB.scalars.memory.take S.scalars.memory.length).length = S.scalars.memory.length := by
    rw [take,ps.memory]; simp [lens]
  refine ⟨S.left tB,leaveEq,⟨?_,?_,?_,?_,?_,?_,?_⟩,?_,?_⟩
  · rw [left_slots]; exact ps.slots
  · rw [left_memory,take]
  · rw [left_bindings]; exact ps.bindings
  · rw [left_baseMemory]; exact ps.base
  · rw [left_scope]; exact ps.scope
  · rw [left_frameBindings,sameBind]; simpa using ps.frameBindings
  · rw [left_rootWritable]; exact psB.writable
  · refine vfB.of_same ?_ (by rw [left_rootWritable]) ?_
    · rw [left_state]; exact noopRetired_same _
    · rw [left_state]; rfl
  · refine co.left ci lengthTake cap ?_
    rw [vfB.live]; omega

def C3 (v b e : Int) : List Cell := [⟨i32,v⟩,⟨i32,b⟩,⟨i32,e⟩]

abbrev cEnd : NExpr := .binary bl .eq (.variable i32 3) (.unary i32 .neg (.literal i32 1))
abbrev szE : NExpr := .cast i32 (.size (.integer i32) (.local 0))
abbrev yesFix : Command := .sequence (.scope (.sequence (.primitive (.assign 3 i32 szE)) (.primitive .skip))) (.primitive .skip)
abbrev fixC : Command := .branch cEnd yesFix (.primitive .skip)
abbrev declCnt : NStmt := .declare i32 true (.literal i32 0)
abbrev declI : NStmt := .declare i32 true (.variable i32 2)
abbrev iScope : Command := .scope (.sequence (.primitive declI) (.sequence loopC (.primitive .skip)))
abbrev retC : Command := .sequence (.primitive (.ret (.variable i32 4))) (.primitive .skip)
abbrev cbody : Command := .sequence fixC (.sequence (.primitive declCnt) (.sequence iScope retC))

theorem liveS_scope_eq (T : NState) (s : Nat) : liveS ({T with scope := s} : NState) = liveS T := rfl

theorem cEnd_scalar : cEnd.scalarOnly = true := by simp [NExpr.scalarOnly]

theorem cEnd_value (env : Nat → Ty → Option Int) (e : Int) (h : env 3 i32 = some e) (valid : i32.valid e = true) :
    cEnd.denote env = some (if e = -1 then 1 else 0) := by
  have lit : i32.valid (1 : Int) = true := by simp [Ty.valid]
  have neg : i32.valid (-1 : Int) = true := by simp [Ty.valid]
  have c1 := Ty.convert_of_valid i32 (-1) neg
  have b1 : bl.convert 1 = some 1 := Ty.convert_of_valid bl 1 (by simp [Ty.valid])
  have b0 : bl.convert 0 = some 0 := Ty.convert_of_valid bl 0 (by simp [Ty.valid])
  simp only [NExpr.denote,h,lit,Option.bind_some,unaryValue,binaryValue,c1]
  by_cases hh : e = -1 <;> simp [hh,b1,b0,c1]


theorem assign_gen_ev (F : Fixed) {sc : Nat} {rw0 : List Bool} {W k : Nat} {cells : List Cell} (S : NState)
    (e : NExpr) (idx : Nat) (old x : Int) (t0 : NState) (w p : Nat) (hidx : idx < k) (hk : cells.length = k)
    (hcell : cells[idx]? = some ⟨i32,old⟩) (oldv : i32.valid old = true)
    (ps : PS F sc rw0 S cells (bn F k) (sl k)) (cb : Cb F W S)
    (ran : e.eval S = some (t0,x)) (good : Good S t0 w p) (xv : i32.valid x = true)
    (cap : liveS S+p ≤ F.SPB) :
    ∃ t, (NStmt.assign (idx+1) i32 e).run S = some ⟨t,none,false⟩ ∧
      PS F sc rw0 t (cells.set idx ⟨i32,x⟩) (bn F k) (sl k) ∧ t.frame = S.frame ∧ Cb F (W+w+1) t := by
  have hs : S.slots[idx+1]? = some (.scalar idx) := by simp [ps.slots,sl,hidx]
  have hb : S.scalars.bindings[idx]? = some ⟨F.P.length+idx,true⟩ := by simp [ps.bindings,bn,hidx]
  have hm : S.scalars.memory[F.P.length+idx]? = some ⟨i32,old⟩ := by
    simp [ps.memory,List.getElem?_append_right,hcell]
  obtain ⟨t,run,frame,sl',sc',me,bi,ba,wl,wu,pl,pu,ql,qu,live⟩ := assign_of_good e (idx+1) idx i32 S t0 x x w p
    ⟨F.P.length+idx,true⟩ ⟨i32,old⟩ ran good (Ty.convert_of_valid _ _ xv) hs hb hm rfl oldv rfl
  refine ⟨t,run,⟨?_,?_,?_,?_,?_,?_,?_⟩,frame,?_⟩
  · rw [sl']; exact ps.slots
  · rw [me,ps.memory]; simp [List.set_append_right]
  · rw [bi]; exact ps.bindings
  · rw [ba]; exact ps.base
  · rw [sc']; exact ps.scope
  · rw [frame]; exact ps.frameBindings
  · rw [frame]; exact ps.writable
  · exact cb.step (w := w+1) (p := p) frame (by omega) pu cap qu

theorem fix_phase (F : Fixed) (items : List Int) {rw0 : List Bool} {L0 T0 W : Nat} {v b e : Int} (S : NState)
    (hn : items.length < 2147483648) (hvn : F.vbuf.items.length = items.length)
    (hsc : F.sc ≤ S.scope) (hL : L0 ≤ F.TPB) (ev : i32.valid e = true)
    (ps : PS F S.scope rw0 S (C3 v b e) (bn F 3) (sl 3)) (vf : VF F L0 T0 S.frame) (cb : Cb F W S)
    (cap : liveS S+60 ≤ F.SPB) :
    RunsTo fixC S fun step => step.returned = none ∧ step.breaking = false ∧
      PS F S.scope rw0 step.state (C3 v b (if e = -1 then (items.length : Int) else e)) (bn F 3) (sl 3) ∧
      VF F L0 T0 step.state.frame ∧ Cb F (W+60) step.state := by
  have env3 := env_gen F S ps 2 e (by decide) (by simp [C3]) ev
  have value := cEnd_value (envOf S) e env3 ev
  have cnodes : cEnd.nodes = 4 := by simp [NExpr.nodes]
  obtain ⟨u,hu,good⟩ := scalar_eval cEnd S _ cEnd_scalar value
  have self := release_self good.1.1
  have liveU0 : liveS u = liveS S := liveS_core good.1
  have cbU : Cb F (W+cEnd.nodes) u := cb.good good (by omega)
  have cbC : Cb F (W+cEnd.nodes+1) (u.charge 1 0) := cbU.good (Good.charge u 1 0) (by omega)
  have coreU : Core S (u.charge 1 0) := good.1.trans (core_charge u 1 0)
  have psU : PS F S.scope rw0 (u.charge 1 0) (C3 v b e) (bn F 3) (sl 3) := ps.core coreU
  have vfU : VF F L0 T0 (u.charge 1 0).frame := vf.of_eq (by simpa using good.1.1)
  have liveU : liveS (u.charge 1 0) = liveS S := (liveS_core coreU)
  by_cases h : e = -1
  · have ival : (if e = -1 then (1 : Int) else 0) = 1 := by simp [h]
    apply RunsTo.branch (next := u) (value := if e = -1 then 1 else 0) hu
    rw [ival, if_neg (by decide), self]
    -- the size is assigned to the end index inside a scope
    have ps1 := psU.enter
    have cb1 := cbC.enter
    have sl3 : u.slots = sl 3 := psU.slots
    have hs : ({u.charge 1 0 with scope := (u.charge 1 0).scope+1} : NState).vectorSlot 0 = some 0 := by
      simp [NState.vectorSlot,sl3,sl]
    have vf1 : VF F L0 T0 ({u.charge 1 0 with scope := (u.charge 1 0).scope+1} : NState).frame := vfU
    have small : F.vbuf.items.length < 2^64 := by omega
    obtain ⟨t1,first⟩ := sizeV_ev F ({u.charge 1 0 with scope := (u.charge 1 0).scope+1} : NState)
      ((NExpr.size (.integer i32) (.local 0)).nodes+1) hs ps1.frameBindings vf1 small
    have nv : i32.valid (items.length : Int) = true := i32_valid_nat _ hn
    have evc := Ev.cast first (v' := (items.length : Int))
      (by rw [hvn]; exact Ty.convert_of_valid _ _ nv)
    obtain ⟨next,w,p,ev',hw,hp⟩ : ∃ next w p, Ev ({u.charge 1 0 with scope := (u.charge 1 0).scope+1} : NState)
        szE next (items.length : Int) [] w p ∧ w ≤ 10 ∧ p ≤ 10 :=
      ⟨_,_,_,by simpa using evc,by simp [NExpr.nodes,Container.nodes],by simp [NExpr.nodes,Container.nodes]⟩
    have goodE := Ev.good ev'
    obtain ⟨t,run,psT,frame,cbT⟩ := assign_gen_ev (k := 3) F _ szE 2 e (items.length : Int) next w p (by decide)
      (by simp [C3]) (by simp [C3]) ev ps1 cb1 (Ev.eval ev') goodE nv (by rw [liveS_scope_eq]; omega)
    have cells : (C3 v b e).set 2 ⟨i32,(items.length : Int)⟩ = C3 v b (items.length : Int) := by simp [C3]
    rw [cells] at psT
    have vfT : VF F L0 T0 t.frame := vf1.of_eq frame
    have eqs : (u.charge 1 0).scope = S.scope := psU.scope
    obtain ⟨restored,leaveEq,psR,vfR,cbR⟩ := leave_set F (u.charge 1 0) t hsc psU
      psT (by simp [C3]) vfT hL cbC cbT (by omega)
    apply RunsTo.seqSkip
    apply RunsTo.scopeSimple
    apply RunsTo.seq
    apply RunsTo.primitive run
    refine ⟨rfl,rfl,?_⟩
    apply RunsTo.skip
    refine ⟨rfl,rfl,?_⟩
    refine ⟨restored,leaveEq,rfl,rfl,rfl,rfl,?_,vfR,cbR.mono (by omega)⟩
    rw [if_pos h]
    exact psR
  · have ival : (if e = -1 then (1 : Int) else 0) = 0 := by simp [h]
    apply RunsTo.branch (next := u) (value := if e = -1 then 1 else 0) hu
    rw [ival, if_pos rfl, self]
    apply RunsTo.skip
    rw [if_neg h]
    exact ⟨rfl,rfl,psU,vfU,cbC.mono (by omega)⟩


theorem live_k (F : Fixed) {sc : Nat} {rw0 : List Bool} {cells : List Cell} {k : Nat} (S : NState)
    (ps : PS F sc rw0 S cells (bn F k) (sl k)) : liveS S = F.P.length+cells.length-F.B+k := by
  rw [ps.live_eq,bn_length]

theorem body_run (F : Fixed) (items : List Int) (hv : F.vbuf.items = items.map Value.integer)
    {rw0 : List Bool} {L0 T0 W : Nat} {v e : Int} {b E : Nat} (S : NState)
    (hn : items.length < 2147483648) (hvn : F.vbuf.items.length = items.length)
    (hE : (if e = -1 then (items.length : Int) else e) = (E : Int)) (hEl : E ≤ items.length)
    (hb : b < 2147483648) (hev : i32.valid e = true) (hsc : F.sc ≤ S.scope) (hL : L0 ≤ F.TPB) (vv : i32.valid v = true)
    (hB : F.B ≤ F.P.length) (hspb : F.P.length+130-F.B ≤ F.SPB)
    (ps : PS F S.scope rw0 S (C3 v b e) (bn F 3) (sl 3)) (vf : VF F L0 T0 S.frame) (cb : Cb F W S) :
    RunsTo cbody S fun step => step.returned = some (.scalar ((cntU items v b (E-b) : Nat) : Int)) ∧
      step.breaking = false ∧
      PS F S.scope rw0 step.state (C3 v b E ++ [⟨i32,(cntU items v b (E-b) : Nat)⟩]) (bn F 4) (sl 4) ∧
      VF F L0 T0 step.state.frame ∧ Cb F (W+(E-b)*108+200) step.state := by
  have live3 : liveS S = F.P.length+3-F.B+3 := by rw [live_k F S ps]; simp [C3]
  have bv : i32.valid (b : Int) = true := i32_valid_nat b hb
  have Ev' : i32.valid (E : Int) = true := i32_valid_nat E (by omega)
  have lit0 : i32.valid (0 : Int) = true := by simp [Ty.valid]
  -- the end index is fixed up
  apply RunsTo.seq
  refine (fix_phase F items (e := e) S hn hvn hsc hL hev ps vf cb (by omega)).mono ?_
  intro s1 ⟨nr,nb,ps1,vf1,cb1⟩
  refine ⟨nr,nb,?_⟩
  rw [hE] at ps1
  have live1 : liveS s1.state = F.P.length+3-F.B+3 := by rw [live_k F _ ps1]; simp [C3]
  -- the count starts at zero
  obtain ⟨s2,run2,ps2,fr2,cb2⟩ := decl_gen F s1.state (.literal i32 0) 0 (by simp [C3]) ps1 cb1
    (by simp [NExpr.scalarOnly]) (by simp [NExpr.denote,lit0]) lit0 (by simp [NExpr.nodes]; omega)
  have vf2 : VF F L0 T0 s2.frame := vf1.of_eq fr2
  have live2 : liveS s2 = F.P.length+4-F.B+4 := by rw [live_k F _ ps2]; simp [C3]
  apply RunsTo.seq
  apply RunsTo.primitive run2
  refine ⟨rfl,rfl,?_⟩
  -- the scope holding the loop variable
  apply RunsTo.seq
  have ps3 := ps2.enter
  have cb3 := cb2.enter
  have e1 := env_gen F ({s2 with scope := s2.scope+1} : NState) ps3 1 (b : Int) (by decide) (by simp [C3]) bv
  obtain ⟨s4,run4,ps4,fr4,cb4⟩ := decl_gen F ({s2 with scope := s2.scope+1} : NState) (.variable i32 2) (b : Int) (by simp [C3])
    ps3 cb3 (by simp [NExpr.scalarOnly]) (by simp [NExpr.denote,e1]) bv
    (by rw [liveS_scope_eq]; simp [NExpr.nodes]; omega)
  have vf4 : VF F L0 T0 s4.frame := vf2.of_eq (by simpa using fr4)
  have cells5 : C3 v b E ++ [⟨i32,(0 : Int)⟩] ++ [⟨i32,(b : Int)⟩] = C5 v b E 0 b := by
    simp [C3,C5]
  rw [cells5] at ps4
  have live4 : liveS s4 = F.P.length+5-F.B+5 := by rw [live_k F _ ps4]; simp [C5]
  have sc4 : s4.scope = S.scope+1 := ps4.scope
  have scs2 : s2.scope = S.scope := ps2.scope
  apply RunsTo.scopeSimple
  apply RunsTo.seq
  apply RunsTo.primitive run4
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.seqSkip
  have loop := count_loop F items hv (W := W+60+1+1+2) s4 hEl hn hb (by rw [sc4]; omega) hL vv
    ps4.self vf4 (cb4.mono (by simp only [NExpr.nodes]; omega)) (by omega)
  refine loop.mono ?_
  intro st ⟨nr2,nb2,psL,vfL,cbL⟩
  refine ⟨nr2,nb2,?_⟩
  rw [sc4] at psL
  have psB : PS F (S.scope+1) rw0 st.state (C3 v b E ++ [⟨i32,(cntU items v b (E-b) : Nat)⟩] ++ [⟨i32,(b+(E-b) : Nat)⟩])
      (bn F 5) (sl 5) := by
    have : C3 v b E ++ [⟨i32,(cntU items v b (E-b) : Nat)⟩] ++ [⟨i32,(b+(E-b) : Nat)⟩] =
        C5 v b E (cntU items v b (E-b) : Nat) (b+(E-b) : Nat) := by simp [C3,C5]
    rw [this]; exact psL
  obtain ⟨restored,leaveEq,psR,vfR,cbR⟩ := leave_ext F s2 st.state (by omega) ps2 psB (by simp [C3])
    vfL hL cb2 cbL (by omega)
  refine ⟨rfl,rfl,restored,leaveEq,rfl,rfl,?_⟩
  have cle := cntU_le items v b (E-b)
  have cv : i32.valid ((cntU items v b (E-b) : Nat) : Int) = true := i32_valid_nat _ (by omega)
  have e4 := env_gen F restored psR 3 ((cntU items v b (E-b) : Nat) : Int) (by decide) (by simp [C3]) cv
  have liveR : liveS restored = F.P.length+4-F.B+4 := by rw [live_k F _ psR]; simp [C3]
  obtain ⟨u,hu,good⟩ := scalar_eval (.variable i32 4) restored ((cntU items v b (E-b) : Nat) : Int)
    (by simp [NExpr.scalarOnly]) (by simp [NExpr.denote,e4])
  have self := release_self good.1.1
  have run : (NStmt.ret (.variable i32 4)).run restored = some ⟨u.charge 1 0,some (.scalar ((cntU items v b (E-b) : Nat) : Int)),false⟩ := by
    simp [NStmt.run,hu,self]
  have coreU : Core restored (u.charge 1 0) := good.1.trans (core_charge u 1 0)
  have cbU : Cb F _ u := cbR.good good (by simp [NExpr.nodes]; omega)
  have cbC : Cb F _ (u.charge 1 0) := cbU.good (Good.charge u 1 0) (by rw [liveS_core good.1]; omega)
  apply RunsTo.sequence
  apply RunsTo.primitive run
  refine Or.inl ⟨Or.inl rfl,rfl,rfl,psR.core coreU,vfR.of_eq (by simpa using good.1.1),?_⟩
  refine cbC.mono ?_
  simp [NExpr.nodes]
  omega

end Proofs.CountLoop
