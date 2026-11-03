import Proofs.InvPermEval

namespace Proofs.InvPermLoop
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppMixedInvoke
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.FlatVectorStmt Proofs.FillWriteStmt
open Proofs.InvPermFrame Proofs.InvPermMath Proofs.InvPermEval
open Proofs.CppState (Cell)

theorem _root_.Proofs.InvPermEval.St.of_good {F : Fixed} {items rw0 sc L0 Tw i ib S b} (st : St F items rw0 sc L0 Tw i ib S b) {r : NState}
    {w p : Nat} (g : Good S r w p) : St F items rw0 sc L0 Tw i ib r b :=
  ⟨st.pt.core g.1,by rw [g.1.1]; exact st.fb,st.vb,st.itemsB,st.cap,st.small,st.scope⟩

theorem _root_.Proofs.InvPermEval.St.enter {F : Fixed} {items rw0 sc L0 Tw i ib S b} (st : St F items rw0 sc L0 Tw i ib S b) :
    St F items rw0 (sc+1) L0 Tw i ib {S with scope := S.scope+1} b :=
  ⟨st.pt.enter,st.fb,st.vb,st.itemsB,st.cap,st.small,by have := st.scope; omega⟩

theorem _root_.Proofs.InvPermEval.St.live {F : Fixed} {items rw0 sc L0 Tw i ib S b} (st : St F items rw0 sc L0 Tw i ib S b) :
    liveS S = F.P.length+2-F.B+2 := by
  rw [st.pt.live_eq]; simp [cellsNI,bindsNI]

-- A check that passes.
theorem check_step {F : Fixed} {items rw0 sc L0 Tw i ib S b W k} (st : St F items rw0 sc L0 Tw i ib S b)
    (cb : Cb F W S) (e : NExpr) (h : EvB k S e 1) (cap : liveS S+k ≤ F.SPB) :
    ∃ r, (NStmt.check e).run S = some ⟨r,none,false⟩ ∧ St F items rw0 sc L0 Tw i ib r b ∧ Cb F (W+k+1) r := by
  obtain ⟨t,ev⟩ := h
  obtain ⟨r,run,good⟩ := check_of_ev e S t 1 k k ev (by decide)
  exact ⟨r,run,st.of_good good,cb.good good cap⟩


theorem pinv_succ_map (items : List Int) (n i : Nat) (x : Int) (hx : items[i]? = some x) :
    ((pinv items n i).map Value.integer).set x.toNat (Value.integer (i : Int)) =
      (pinv items n (i+1)).map Value.integer := by
  simp [pinv,hx,List.map_set]

-- `inv[v[i]] = i;`
theorem write_step {F : Fixed} {items rw0 sc L0 Tw i W} {S : NState} {b : Buffer Value}
    (st : St F items rw0 sc L0 Tw i i S b) (hi : i < items.length)
    (x : Int) (hx : items[i]? = some x) (h0 : 0 ≤ x) (h1 : x < items.length)
    (cb : Cb F W S) (cap : liveS S+60 ≤ F.SPB) (space : L0+items.length+3 ≤ F.TPB) :
    ∃ r b', wrStmt.run S = some ⟨r,none,false⟩ ∧
      St F items rw0 sc L0 (Tw+1) i (i+1) r b' ∧ Cb F (W+60) r := by
  have sm := st.small
  have hs : S.vectorSlot 2 = some 1 := by simp [NState.vectorSlot,st.pt.slots,slotsNRI]
  have fbind : S.frame.bindings[1]? = some (flatBinding F.R i32 F.sc) := by
    rw [st.pt.frameBindings]; simp [vbind,atom,flatBinding]
  have idx : ∀ u : NState, Core S u → ∃ t, Ev u rvCast t (x.toNat : Int) [] 20 20 := by
    intro u c
    obtain ⟨t,ev⟩ := rvCast_evB st hi x hx h0 h1 (u := u) c
    exact ⟨t,by rw [Int.toNat_of_nonneg h0]; exact ev⟩
  have lenB : b.items.length = items.length := by rw [st.itemsB]; simp [pinv_length]
  have inside : x.toNat < b.items.length := by omega
  have iv : i32.valid (i : Int) = true := i32_valid_nat i (by omega)
  obtain ⟨t,run,tf,tsl,tsc,tm,tb,tbase,gw1,gw2,gp1,gp2,gq1,gq2⟩ := write_flat_stmt S 2 1 rvCast iV x.toNat (i : Int) F.R F.sc
    i32 b 20 20 (by simp [NExpr.scalarOnly]) (by simp [NExpr.denote]; exact st.env_i (by omega))
    (fun u c => idx u c) hs fbind st.fb.valid (by simpa using st.fb.tag) st.fb.found st.fb.lengths st.fb.flag iv inside
  have newValid := CppVector.writeRef_preserves_valid b (accepts (.integer i32)) x.toNat (Value.integer (i : Int))
    st.fb.bufferValid (by simpa [accepts] using iv)
  have fb' := st.fb.update ⟨{b with items := b.items.set x.toNat (Value.integer (i : Int))},(),1,b.capacity+2⟩
    (by simpa using st.fb.owner) newValid (by simpa using st.fb.limit)
  rw [← tf] at fb'
  have tfs : t.frame.bindings = S.frame.bindings := by rw [tf]; simp [Frame.updated]
  have tfr : t.frame.rootWritable = S.frame.rootWritable := by rw [tf]; simp [Frame.updated]
  have storageT : t.frame.state.storage.peak = max S.frame.state.storage.peak
      (S.frame.state.liveSpace+(b.capacity+2-(b.capacity+1))-S.frame.state.storage.baseSpace) := by
    rw [tf]; simp [Frame.updated]
  have liveS0 := st.fb.live
  have capEq := st.cap
  have spB := cb.scalarPeak
  have stB := cb.storagePeak
  have opB := cb.outerPeak
  have nC : rvCast.nodes ≤ 10 := by simp [NExpr.nodes,Container.nodes]
  have nV : iV.nodes = 1 := by simp [NExpr.nodes]
  refine ⟨t,{b with items := b.items.set x.toNat (Value.integer (i : Int))},run,⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,fb',st.vb,?_,?_,st.small,st.scope⟩,?_⟩
  · rw [tsl]; exact st.pt.slots
  · rw [tm]; exact st.pt.memory
  · rw [tb]; exact st.pt.bindings
  · rw [tbase]; exact st.pt.base
  · rw [tsc]; exact st.pt.scope
  · rw [tfs]; exact st.pt.frameBindings
  · rw [tfr]; exact st.pt.writable
  · simp only [st.itemsB]; exact pinv_succ_map items items.length i x hx
  · exact st.cap
  · refine ⟨?_,?_,?_,?_⟩
    · have := cb.work; omega
    · omega
    · rw [storageT]
      omega
    · omega


-- `i++` (as `i = i + 1`)
theorem iinc_step {F : Fixed} {items rw0 sc L0 Tw i ib W} {S : NState} {b : Buffer Value}
    (st : St F items rw0 sc L0 Tw i ib S b) (hi : i+1 < 2147483648)
    (cb : Cb F W S) (cap : liveS S+12 ≤ F.SPB) :
    ∃ r, (NStmt.assign 3 i32 incIE).run S = some ⟨r,none,false⟩ ∧ St F items rw0 sc L0 Tw (i+1) ib r b ∧
      Cb F (W+4) r := by
  have vi := i32_valid_nat i (by omega)
  have vi1 := i32_valid_nat (i+1) hi
  have e3 := st.env_i (by omega)
  have lit : i32.valid (1 : Int) = true := by simp [Ty.valid]
  have value : incIE.denote (envOf S) = some ((i : Int)+1) := by
    have vi1' : i32.valid ((i : Int)+1) = true := by simp [Ty.valid]; omega
    exact denote_inc (envOf S) 3 i32 i e3 lit (Ty.convert_of_valid _ _ vi1')
  obtain ⟨t,run,frame,sl,sc',me,bi,ba,wl,wu,pl,pu,ql,qu,live⟩ := assign_good incIE 3 1 i32 S _ ((i : Int)+1)
    ⟨F.P.length+1,true⟩ ⟨i32,i⟩ (by simp [NExpr.scalarOnly]) value
    (Ty.convert_of_valid _ _ (by simp [Ty.valid]; omega))
    (by simp [st.pt.slots,slotsNRI]) (by simp [st.pt.bindings,bindsNI]) (by simp [st.pt.memory,cellsNI]) rfl vi rfl
  have sm := st.small
  refine ⟨t,run,⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,?_,st.vb,st.itemsB,st.cap,st.small,st.scope⟩,?_⟩
  · rw [sl]; exact st.pt.slots
  · rw [me,st.pt.memory]; simp [cellsNI,List.set_append_right]
  · rw [bi]; exact st.pt.bindings
  · rw [ba]; exact st.pt.base
  · rw [sc']; exact st.pt.scope
  · rw [frame]; exact st.pt.frameBindings
  · rw [frame]; exact st.pt.writable
  · rw [frame]; exact st.fb
  · have wu' : t.scalars.work ≤ S.scalars.work+4 := by simp [NExpr.nodes] at wu; omega
    have pu' : t.scalars.peak ≤ max S.scalars.peak (liveS S+12) := by simp [NExpr.nodes] at pu; omega
    exact cb.step frame wu' pu' cap qu


-- Leaving a scope that declared nothing: scalar cells and the frame return to the outer shape.
theorem leave_st {F : Fixed} {items rw0 sc L0 Tw Tw' i ib ib' W W'} (T tB : NState) {b b' : Buffer Value}
    (hsc : F.sc ≤ sc) (st : St F items rw0 sc L0 Tw i ib T b) (stB : St F items rw0 (sc+1) L0 Tw' i ib' tB b')
    (co : Cb F W T) (ci : Cb F W' tB) (cap : liveS T ≤ F.SPB) (hL : L0+1+items.length ≤ F.TPB) :
    ∃ restored, T.leave tB none = some restored ∧ St F items rw0 sc L0 Tw' i ib' restored b' ∧
      Cb F (W'+1) restored := by
  have take : tB.scalars.memory.take T.scalars.memory.length = T.scalars.memory := by
    rw [stB.pt.memory,st.pt.memory]; exact List.take_length
  have fits : T.scalars.memory.length ≤ tB.scalars.memory.length := by
    rw [stB.pt.memory,st.pt.memory]; exact Nat.le_refl _
  have fresh : ∀ owner, tB.frame.state.forest.context owner ≠ some (T.scope+1) := by
    intro owner h
    rcases stB.fb.ctx owner _ h with lt | ⟨eq,_⟩
    · have := st.pt.scope; omega
    · have := st.pt.scope; omega
  have leaveEq : T.leave tB none = some (T.left tB) :=
    leave_scalar T tB none (by simp) fits (by rw [take]) stB.fb.valid fresh
  have sameBind : tB.frame.bindings = T.frame.bindings := by rw [stB.pt.frameBindings,st.pt.frameBindings]
  have lengthTake : (tB.scalars.memory.take T.scalars.memory.length).length = T.scalars.memory.length := by
    rw [take]
  have fbNew : IF (T.left tB).frame F.V F.vsc F.R F.sc L0 Tw' F.vbuf b' := by
    refine stB.fb.noop ?_ ?_ ?_
    · rw [left_state]
    · rw [left_rootWritable]
    · rw [left_frameBindings,sameBind]; simp
  refine ⟨T.left tB,leaveEq,⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,fbNew,stB.vb,stB.itemsB,stB.cap,stB.small,st.scope⟩,?_⟩
  · rw [left_slots]; exact st.pt.slots
  · rw [left_memory,take]; exact st.pt.memory
  · rw [left_bindings]; exact st.pt.bindings
  · rw [left_baseMemory]; exact st.pt.base
  · rw [left_scope]; exact st.pt.scope
  · rw [left_frameBindings,sameBind]; simpa using st.pt.frameBindings
  · rw [left_rootWritable]; exact stB.pt.writable
  · refine co.left ci lengthTake cap ?_
    rw [stB.fb.live,stB.cap]; omega


theorem hinv_of {items : List Int} {i : Nat} (hrange : ∀ (j : Nat) (x : Int), items[j]? = some x → 0 ≤ x ∧ x < items.length)
    (hinj : ∀ (j k : Nat) (x : Int), items[j]? = some x → items[k]? = some x → j = k)
    (hi : i < items.length) (x : Int) (hx : items[i]? = some x) {b : Buffer Value}
    (hb : b.items = (pinv items items.length i).map Value.integer) :
    b.items[x.toNat]? = some (Value.integer (-1)) := by
  have xr := hrange i x hx
  have untouched := pinv_untouched items items.length hrange i (by omega) x.toNat (by omega) (by
    intro j y lt item h
    have yr := hrange j y item
    have eq : y = x := by omega
    exact absurd (hinj j i x (eq ▸ item) hx) (by omega))
  rw [hb]
  simp [List.getElem?_map,untouched]

-- The body scope of one iteration.
theorem scope_phase {F : Fixed} {items rw0 sc L0 Tw i W} {S : NState} {b : Buffer Value}
    (hrange : ∀ (j : Nat) (x : Int), items[j]? = some x → 0 ≤ x ∧ x < items.length)
    (hinj : ∀ (j k : Nat) (x : Int), items[j]? = some x → items[k]? = some x → j = k)
    (st : St F items rw0 sc L0 Tw i i S b) (hi : i < items.length)
    (cb : Cb F W S) (cap : liveS S+200 ≤ F.SPB) (space : L0+items.length+3 ≤ F.TPB) :
    RunsTo ibodyScope S fun step => step.returned = none ∧ step.breaking = false ∧
      ∃ b', St F items rw0 sc L0 (Tw+1) i (i+1) step.state b' ∧ Cb F (W+300) step.state := by
  obtain ⟨x,hx⟩ : ∃ x, items[i]? = some x := ⟨items[i],by simp [hi]⟩
  obtain ⟨h0,h1⟩ := hrange i x hx
  have hinvB := hinv_of hrange hinj hi x hx st.itemsB
  have st1 := st.enter
  have cb1 := cb.enter
  have liveEq : liveS ({S with scope := S.scope+1} : NState) = liveS S := rfl
  have live2 := st.live
  have sm := st.small
  obtain ⟨r1,run1,st2,cb2⟩ := check_step st1 cb1 c1E (c1_evB st1 hi x hx h0 h1 (Core.refl _)) (by omega)
  have l2 : liveS r1 = liveS S := by rw [st2.live,live2]
  obtain ⟨r2,run2,st3,cb3⟩ := check_step st2 cb2 c2E (c2_evB st2 hi x hx h0 h1 hinvB (Core.refl _)) (by omega)
  have l3 : liveS r2 = liveS S := by rw [st3.live,live2]
  obtain ⟨r3,b',run3,st4,cb4⟩ := write_step st3 hi x hx h0 h1 cb3 (by omega) space
  have l4 : liveS r3 = liveS S := by rw [st4.live,live2]
  obtain ⟨restored,leaveEq,st5,cb5⟩ := leave_st S r3 (st.scope) st st4 cb cb4 (by omega) (by omega)
  apply RunsTo.scopeSimple
  apply RunsTo.seq
  apply RunsTo.primitive run1
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.seq
  apply RunsTo.primitive run2
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.seqSkip
  apply RunsTo.primitive run3
  refine ⟨rfl,rfl,rfl,rfl,restored,leaveEq,rfl,rfl,b',st5,cb5.mono ?_⟩
  omega


theorem inv_loop {F : Fixed} {items rw0 sc L0 T0 W} {S : NState} {b0 : Buffer Value}
    (hrange : ∀ (j : Nat) (x : Int), items[j]? = some x → 0 ≤ x ∧ x < items.length)
    (hinj : ∀ (j k : Nat) (x : Int), items[j]? = some x → items[k]? = some x → j = k)
    (st : St F items rw0 sc L0 T0 0 0 S b0) (cb : Cb F W S)
    (cap : F.P.length+2-F.B+2+200 ≤ F.SPB) (space : L0+items.length+3 ≤ F.TPB) :
    RunsTo iloopC S fun step => step.returned = none ∧ step.breaking = false ∧
      ∃ b', St F items rw0 sc L0 (T0+items.length) items.length items.length step.state b' ∧
        Cb F (W+items.length*320+8) step.state := by
  have sm := st.small
  refine RunsTo.whileGhost (fun g t => ∃ k, g = items.length-k ∧ k ≤ items.length ∧
      ∃ b', St F items rw0 sc L0 (T0+k) k k t b' ∧ Cb F (W+k*320) t) _ ?_ items.length items.length S (Nat.le_refl _)
    ⟨0,by omega,by omega,b0,by simpa using st,by simpa using cb⟩
  intro g t ⟨k,hg,hk,b,stt,cbt⟩
  have liveT : liveS t = F.P.length+2-F.B+2 := stt.live
  have ei := stt.env_i (by omega)
  have en := stt.env_n
  have value : icondE.denote (envOf t) = some (if (k : Int) < (items.length : Int) then 1 else 0) :=
    denote_lt (envOf t) 3 1 i32 _ _ ei en
  obtain ⟨u,hu,good⟩ := scalar_eval icondE t _ (by simp [NExpr.scalarOnly]) value
  have self := release_self good.1.1
  have cbU : Cb F (W+k*320+4) u := (cbt.good good (by simp [NExpr.nodes]; omega)).mono (by simp [NExpr.nodes])
  have cbC : Cb F (W+k*320+8) (u.charge 1 0) :=
    (cbU.good (Good.charge u 1 0) (by rw [liveS_core good.1]; omega)).mono (by omega)
  have coreU : Core t (u.charge 1 0) := good.1.trans (core_charge u 1 0)
  have stU : St F items rw0 sc L0 (T0+k) k k (u.charge 1 0) b := stt.of_good (good.trans (Good.charge u 1 0))
  refine ⟨u,_,hu,?_,?_⟩
  · intro zero
    have notLt : ¬ k < items.length := by
      intro h
      have : ((k : Int) < (items.length : Int)) := by omega
      rw [if_pos this] at zero
      exact absurd zero (by decide)
    have eq : k = items.length := by omega
    subst eq
    rw [self]
    exact ⟨rfl,rfl,b,stU,cbC.mono (by omega)⟩
  · intro nonzero
    have lt : k < items.length := by
      by_cases h : k < items.length
      · exact h
      · have : ¬ ((k : Int) < (items.length : Int)) := by omega
        rw [if_neg this] at nonzero
        exact absurd rfl nonzero
    rw [self]
    have liveU : liveS (u.charge 1 0) = liveS t := liveS_core coreU
    have scope := scope_phase hrange hinj stU lt cbC (by omega) space
    apply RunsTo.seq
    refine scope.mono ?_
    intro mid ⟨nr,nb,b',stM,cbM⟩
    refine ⟨nr,nb,?_⟩
    obtain ⟨r,run,stR,cbR⟩ := iinc_step stM (by omega) cbM (by rw [stM.live]; omega)
    apply RunsTo.seqSkip
    apply RunsTo.primitive run
    refine ⟨rfl,rfl,rfl,rfl,items.length-(k+1),by omega,k+1,rfl,by omega,b',?_,cbR.mono (by omega)⟩
    have : T0+k+1 = T0+(k+1) := by omega
    rw [this] at stR
    exact stR


-- `int i = 0;` inside the loop-variable scope.
theorem declI_step {F : Fixed} {rw0 : List Bool} {sc L0 Tw W : Nat} {S : NState} {b : Buffer Value} (items : List Int)
    (pt : PT F sc rw0 S (cellsN items.length) (bindsN F) slotsNR) (fb : IF S.frame F.V F.vsc F.R F.sc L0 Tw F.vbuf b)
    (vb : F.vbuf.items = items.map Value.integer) (hb : b.items = List.replicate items.length (Value.integer (-1)))
    (hc : b.capacity = items.length) (small : items.length < 2147483648) (hsc : F.sc ≤ sc)
    (cb : Cb F W S) (cap : liveS S+12 ≤ F.SPB) :
    ∃ t, declIStmt.run S = some ⟨t,none,false⟩ ∧ St F items rw0 sc L0 Tw 0 0 t b ∧ Cb F (W+2) t := by
  have lit : i32.valid 0 = true := by simp [Ty.valid]
  obtain ⟨t,run,frame,sl,sc',me,bi,ba,wl,wu,pl,pu,ql,qu⟩ := declare_good (.literal i32 0) i32 true S 0 0
    (by simp [NExpr.scalarOnly]) (by simp [NExpr.denote,lit]) (Ty.convert_of_valid _ _ lit)
  have memLen : S.scalars.memory.length = F.P.length+1 := by simp [pt.memory,cellsN]
  have bindLen : S.scalars.bindings.length = 1 := by simp [pt.bindings,bindsN]
  refine ⟨t,run,⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,?_,vb,?_,hc,small,hsc⟩,?_⟩
  · rw [sl,bindLen,pt.slots]; rfl
  · rw [me,pt.memory]; simp [cellsN,cellsNI]
  · rw [bi,memLen,pt.bindings]; simp [bindsN,bindsNI]
  · rw [ba]; exact pt.base
  · rw [sc']; exact pt.scope
  · rw [frame]; exact pt.frameBindings
  · rw [frame]; exact pt.writable
  · rw [frame]; exact fb
  · rw [hb]; simp [pinv,List.map_replicate]
  · have wu' : t.scalars.work ≤ S.scalars.work+2 := by simp [NExpr.nodes] at wu; omega
    have pu' : t.scalars.peak ≤ max S.scalars.peak (liveS S+12) := by simp [NExpr.nodes] at pu; omega
    exact cb.step frame wu' pu' cap qu


-- Leaving the scope that held the loop variable `i`.
theorem leave_scope_i {F : Fixed} {rw0 : List Bool} {sc L0 Tw W W' : Nat} {n : Nat} {i : Int} (T tB : NState)
    {b : Buffer Value} (hsc : F.sc ≤ sc)
    (pt : PT F sc rw0 T (cellsN n) (bindsN F) slotsNR) (ptB : PT F (sc+1) rw0 tB (cellsNI n i) (bindsNI F) slotsNRI)
    (fbB : IF tB.frame F.V F.vsc F.R F.sc L0 Tw F.vbuf b) (co : Cb F W T) (ci : Cb F W' tB)
    (cap : liveS T ≤ F.SPB) (hL : L0+1+b.capacity ≤ F.TPB) :
    ∃ restored, T.leave tB none = some restored ∧ PT F sc rw0 restored (cellsN n) (bindsN F) slotsNR ∧
      IF restored.frame F.V F.vsc F.R F.sc L0 Tw F.vbuf b ∧ Cb F (W'+1) restored := by
  have memEq : tB.scalars.memory = T.scalars.memory ++ [⟨i32,i⟩] := by
    rw [ptB.memory,pt.memory]; simp [cellsN,cellsNI]
  have take : tB.scalars.memory.take T.scalars.memory.length = T.scalars.memory := by
    rw [memEq]; exact List.take_left
  have fits : T.scalars.memory.length ≤ tB.scalars.memory.length := by rw [memEq]; simp
  have fresh : ∀ owner, tB.frame.state.forest.context owner ≠ some (T.scope+1) := by
    intro owner h
    rcases fbB.ctx owner _ h with lt | ⟨eq,_⟩
    · have := pt.scope; omega
    · have := pt.scope; omega
  have leaveEq : T.leave tB none = some (T.left tB) :=
    leave_scalar T tB none (by simp) fits (by rw [take]) fbB.valid fresh
  have sameBind : tB.frame.bindings = T.frame.bindings := by rw [ptB.frameBindings,pt.frameBindings]
  have lengthTake : (tB.scalars.memory.take T.scalars.memory.length).length = T.scalars.memory.length := by
    rw [take]
  refine ⟨T.left tB,leaveEq,⟨?_,?_,?_,?_,?_,?_,?_⟩,?_,?_⟩
  · rw [left_slots]; exact pt.slots
  · rw [left_memory,take]; exact pt.memory
  · rw [left_bindings]; exact pt.bindings
  · rw [left_baseMemory]; exact pt.base
  · rw [left_scope]; exact pt.scope
  · rw [left_frameBindings,sameBind]; simpa using pt.frameBindings
  · rw [left_rootWritable]; exact ptB.writable
  · refine fbB.noop ?_ ?_ ?_
    · rw [left_state]
    · rw [left_rootWritable]
    · rw [left_frameBindings,sameBind]; simp
  · refine co.left ci lengthTake cap ?_
    rw [fbB.live]; omega


theorem inv_body {F : Fixed} {items rw0 L0 T0 W} {S : NState}
    (hv : F.vbuf.items = items.map Value.integer) (hvn : F.vbuf.items.length = items.length)
    (small : items.length < 2147483648) (hV : F.V < F.R) (hscope : S.scope = F.sc)
    (hrange : ∀ (j : Nat) (x : Int), items[j]? = some x → 0 ≤ x ∧ x < items.length)
    (hinj : ∀ (j k : Nat) (x : Int), items[j]? = some x → items[k]? = some x → j = k)
    (ps : PS F F.sc rw0 S [] [] [.vector 0]) (vf : VF F L0 T0 S.frame) (cb : Cb F W S)
    (cap : F.P.length-F.B+300 ≤ F.SPB) (hB : F.B ≤ F.P.length) (space : L0+items.length+3 ≤ F.TPB) :
    RunsTo invBody S fun step => step.returned = some (.vector F.R (.integer i32)) ∧ step.breaking = false ∧
      ∃ D b, step.state = D.charge 1 0 ∧ PT F F.sc rw0 D (cellsN items.length) (bindsN F) slotsNR ∧
        IF D.frame F.V F.vsc F.R F.sc L0 (T0+items.length+1+items.length) F.vbuf b ∧
        b.items = (pinv items items.length items.length).map Value.integer ∧ b.capacity = items.length ∧
        Cb F (W+items.length*320+400) D := by
  have liveS0 : liveS S = F.P.length-F.B := by rw [ps.live_eq]; simp
  obtain ⟨t1,run1,ps1,fr1,cb1⟩ := declN_step F S items.length hvn small ps vf cb (by omega)
  have vf1 : VF F L0 T0 t1.frame := vf.of_eq fr1
  have scope1 : t1.scope = F.sc := by rw [ps1.scope]
  have live1 : liveS t1 = F.P.length+1-F.B+1 := by rw [ps1.live_eq]; simp [cellsN,bindsN]
  obtain ⟨t2,b0,run2,pt2,fb2,hb0,hc0,cb2⟩ := fill_phase F t1 items.length small scope1 hV ps1 vf1 cb1 (by omega) (by omega)
  have live2 : liveS t2 = F.P.length+1-F.B+1 := by rw [pt2.live_eq]; simp [cellsN,bindsN]
  apply RunsTo.seq
  apply RunsTo.primitive run1
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.seq
  apply RunsTo.primitive run2
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.seq
  have pt3 := pt2.enter
  have cb3 := cb2.enter
  have liveEq : liveS ({t2 with scope := t2.scope+1} : NState) = liveS t2 := rfl
  obtain ⟨t3,run3,st3,cb4⟩ := declI_step (S := ({t2 with scope := t2.scope+1} : NState)) items pt3 fb2 hv hb0 hc0 small
    (by omega) cb3 (by rw [liveEq]; omega)
  have live3 : liveS t3 = F.P.length+2-F.B+2 := st3.live
  have sc3 : t3.scope = F.sc+1 := st3.pt.scope
  have loop := inv_loop hrange hinj st3 cb4 (by omega) space
  apply RunsTo.scopeSimple
  apply RunsTo.seq
  apply RunsTo.primitive run3
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.seqSkip
  refine loop.mono ?_
  intro stp ⟨nr,nb,b',stF,cbF⟩
  refine ⟨nr,nb,?_⟩
  obtain ⟨restored,leaveEq,ptR,fbR,cbR⟩ := leave_scope_i (n := items.length) (i := (items.length : Int)) t2 stp.state
    (Nat.le_refl _) pt2 stF.pt stF.fb cb2 cbF (by omega) (by rw [stF.cap]; omega)
  refine ⟨rfl,rfl,restored,leaveEq,rfl,rfl,?_⟩
  -- return the result vector
  have hv2 : restored.vectorSlot 2 = some 1 := by simp [NState.vectorSlot,ptR.slots,slotsNR]
  have run : (NStmt.retVector 2).run restored = some ⟨restored.charge 1 0,some (.vector F.R (.integer i32)),false⟩ := by
    simp [NStmt.run,hv2,ptR.frameBindings,flatBinding,vbind,atom]
  apply RunsTo.sequence
  apply RunsTo.primitive run
  refine Or.inl ⟨Or.inl rfl,rfl,rfl,restored,b',rfl,ptR,fbR,stF.itemsB,stF.cap,?_⟩
  exact cbR.mono (by omega)

end Proofs.InvPermLoop
