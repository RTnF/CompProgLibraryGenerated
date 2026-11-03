import Proofs.DoublingInvoke

namespace Proofs.DoublingPrologue
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppMixedInvoke
open Proofs.DoublingNested
open Proofs.CppState (Cell)

-- A new root with `count` empty rows adds exactly `count+1` abstract cells.
theorem construct_live (s next : Proofs.CppNestedVectorStore.State) (ty : Ty) (scope count : Nat)
    (ran : s.constructRows ty scope count = some next) : next.liveSpace = s.liveSpace+count+1 := by
  obtain ⟨valid,_,_,_⟩ := constructRows_inv s ty scope count next ran
  obtain ⟨lengths,_,_⟩ := wellFormed_parts s valid
  have forestEq := constructRows_forest s ty scope count next ran
  have objLen := constructRows_objects_length s ty scope count next ran
  have oldSpace : ∀ o, o < s.storage.objects.length → next.nodeSpace o = s.nodeSpace o := by
    intro o inside
    simp only [State.nodeSpace]
    rw [forestEq,constructRows_old s.forest ty scope count o (by omega),
      constructRows_storage_old s ty scope count o next ran inside]
  have rootSpace : next.nodeSpace s.storage.objects.length = count+1 := by
    simp only [State.nodeSpace]
    have rl := constructRows_root s.forest ty scope count
    rw [lengths] at rl
    rw [forestEq,rl,constructRows_storage_root s ty scope count next ran]
    simp [rootBuffer,rootTag]
  have rowSpace : ∀ j, j < count → next.nodeSpace (s.storage.objects.length+1+j) = 0 := by
    intro j hj
    simp only [State.nodeSpace]
    have rr := constructRows_row s.forest ty scope count j hj
    rw [lengths] at rr
    rw [forestEq,rr,constructRows_storage_row s ty scope count j next ran hj]
    simp [rowBuffer,rowTag]
  have grow : ∀ m, m ≤ count → ((List.range (s.storage.objects.length+1+m)).map next.nodeSpace).sum =
      s.liveSpace+count+1 := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [Nat.add_zero,List.range_succ,List.map_append,List.sum_append]
      have sumOld : ((List.range s.storage.objects.length).map next.nodeSpace).sum = s.liveSpace := by
        unfold State.liveSpace
        congr 1
        apply List.map_congr_left
        intro o member
        exact oldSpace o (List.mem_range.mp member)
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      rw [sumOld,rootSpace]
      omega
    | succ m ih =>
      intro hm
      have step : s.storage.objects.length+1+(m+1) = (s.storage.objects.length+1+m)+1 := by omega
      rw [step,List.range_succ,List.map_append,List.sum_append,ih (by omega)]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      rw [rowSpace m (by omega)]
      omega
  unfold State.liveSpace
  rw [objLen]
  exact grow count (Nat.le_refl _)

abbrev ccount : NExpr := .cast u64 (.variable i32 4)
abbrev consStmt : NStmt := .constructRows i32 true ccount

structure ConsInv (F : Fixed) (L0 W T : Nat) (S : NState) : Prop where
  shape : ShRet S F.P F.B F.K F.n F.w F.V F.vsc F.R F.sc F.sc F.rw
  ctx : Ctx S F.R F.sc F.w
  bnd : Bnd S.frame.state F.sc
  rows : RowsOK S.frame.state F.R F.n F.w F.items F.V F.vbuf 0 [] 0
  live : S.frame.state.liveSpace = L0+F.w+1
  scalarWork : S.scalars.work ≤ W
  storageWork : S.frame.state.storage.work = T
  scalarPeak : S.scalars.peak ≤ F.SPB
  storagePeak : S.frame.state.storage.peak ≤ F.TPB
  outerPeak : S.peak ≤ F.SPB+F.TPB
  vtag : S.frame.state.forest.lookup F.V = some ⟨.integer i32,none,some F.vsc,[]⟩
  vflag : ∃ m, S.frame.rootWritable[F.V]? = some m

theorem ccount_value (F : Fixed) (ok : FixedOK F) {sc : Nat} {rw0 : List Bool} (S : NState)
    (ps : PS F sc rw0 S (cells4 F) (binds4 F) slots5) : ccount.denote (envOf S) = some (F.w : Int) := by
  have wv := i32_valid_nat F.w ok.wSmall
  have env : envOf S 4 i32 = some (F.w : Int) :=
    envOf_at S 4 3 ⟨F.P.length+3,false⟩ i32 (F.w : Int) (by simp [ps.slots,slots5])
      (by simp [ps.bindings,binds4,binds3w,binds2]) (by simp [ps.memory,cells4,cells3w,cells2]) wv
  have uv : u64.valid (F.w : Int) = true := u64_valid_nat F.w (by have := ok.wSmall; omega)
  simp [NExpr.denote,env,Ty.convert_of_valid _ _ uv]

theorem construct_step (F : Fixed) (ok : FixedOK F) {rw0 : List Bool} {L0 T0 W T : Nat} (S : NState)
    (hrw : F.rw = rw0 ++ [true] ++ List.replicate F.w false) (hw1 : 1 ≤ F.w)
    (hv : F.vbuf.items = F.items.map Value.integer) (space : L0+F.w+F.n*F.w+3 ≤ F.TPB)
    (ps : PS F F.sc rw0 S (cells4 F) (binds4 F) slots5) (vf : VF F L0 T0 S.frame) (cb : Cb F W S)
    (stw : S.frame.state.storage.work = T) (cap : liveS S+12 ≤ F.SPB) :
    ∃ t, consStmt.run S = some ⟨t,none,false⟩ ∧ ConsInv F L0 (W+8) (T+F.w+1) t := by
  have supported : CppVectorBindings.supported i32 := by simp [CppVectorBindings.supported,i32]
  have limit : F.w ≤ rowLimit := by
    have : rowLimit = 384307168202282325 := by simp [rowLimit]
    have := ok.wSmall; omega
  obtain ⟨t,next,ran,run,frame,sl,sc',me,bi,ba,wl,wu,pl,pu,ql,qu⟩ := construct_rows_stmt S ccount F.w i32
    (by simp [NExpr.scalarOnly]) (ccount_value F ok S ps) supported limit vf.valid vf.lengths
  refine ⟨t,run,?_⟩
  have hlen := (wellFormed_parts _ vf.valid).1
  have hR : F.R = S.frame.state.storage.objects.length := vf.rootId
  have hscope : S.scope = F.sc := ps.scope
  have fl : S.frame.bindings.length = 1 := by simp [ps.frameBindings]
  have rwLen : rw0.length = S.frame.state.storage.objects.length := by
    have := vf.lengths; rw [ps.writable] at this; omega
  have forestEq := constructRows_forest S.frame.state i32 S.scope F.w next ran
  have objLen := constructRows_objects_length S.frame.state i32 S.scope F.w next ran
  have nextValid := constructRows_state_wellFormed S.frame.state i32 S.scope F.w next ran
  obtain ⟨_,_,_,nextEq⟩ := constructRows_inv S.frame.state i32 S.scope F.w next ran
  have tstate : t.frame.state = next := by rw [frame]
  have trw : t.frame.rootWritable = rw0 ++ [true] ++ List.replicate F.w false := by
    rw [frame]; simp [ps.writable]
  have tbind : t.frame.bindings = [vbind F.V F.vsc,rbind F.R F.sc] := by
    rw [frame]; simp [ps.frameBindings,vbind,rbind,atom,hR,hscope]
  have rootTagEq : next.forest.lookup F.R = some (rootTag i32 F.sc F.R F.w) := by
    rw [forestEq,hR,← hlen,constructRows_root,hlen,hscope]
  have rootFound : next.storage.lookup F.R = some (rootBuffer F.R F.w) := by
    rw [hR]; exact constructRows_storage_root S.frame.state i32 S.scope F.w next ran
  have graph : RootGraph next F.R i32 F.w F.sc :=
    ⟨nextValid,rootTagEq,rootBuffer F.R F.w,rootFound,rfl,rfl⟩
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,⟨?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [sl,fl,ps.slots]; simp [slots5,mainSlots]
  · rw [me,ps.memory]; simp [cells4,cells3w,cells2]
  · rw [bi,ps.bindings]; simp [binds4,binds3w,binds2]
  · rw [ba]; exact ps.base
  · rw [sc']; exact ps.scope
  · exact tbind
  · rw [trw,hrw]
  · simp [NState.vectorSlot,sl,fl,ps.slots,slots5]
  · rw [tbind]; simp [rbind,atom]
  · rw [tstate]; exact graph
  · rw [trw,tstate,forestEq,constructRows_length]; simp [rwLen,hlen]; omega
  · have hr0 : F.R = rw0.length := by omega
    rw [trw,hr0]; simp [List.append_assoc]
  · rw [tstate]
    have b := bnd_construct S.frame.state next i32 S.scope F.w ran (by rw [hscope]; exact vf.strict)
    rw [hscope] at b
    exact b
  · rw [tstate]
    have vOld : next.storage.lookup F.V = S.frame.state.storage.lookup F.V :=
      constructRows_storage_old S.frame.state i32 S.scope F.w F.V next ran (by have := ok.before; omega)
    refine ⟨by rw [vOld]; exact vf.vfound,fun k hk => absurd hk (Nat.not_lt_zero k),?_,?_⟩
    · intro hw
      refine ⟨rowBuffer i32 (F.R+1+0),?_,by simp [rowBuffer],by simp [rowBuffer],rfl⟩
      rw [hR]; exact constructRows_storage_row S.frame.state i32 S.scope F.w 0 next ran hw
    · intro k hk hkw
      refine ⟨rowBuffer i32 (F.R+1+k),?_,by simp [rowBuffer],by simp [rowBuffer],rfl⟩
      rw [hR]; exact constructRows_storage_row S.frame.state i32 S.scope F.w k next ran hkw
  · rw [tstate,construct_live S.frame.state next i32 S.scope F.w ran,vf.live]
  · have := cb.work; simp [NExpr.nodes] at wu; omega
  · rw [tstate,nextEq]; simp [stw]
  · have := cb.scalarPeak; simp [NExpr.nodes] at pu; omega
  · rw [tstate,nextEq]
    have := cb.storagePeak; have := vf.live
    simp only [List.length_append]
    show max S.frame.state.storage.peak (S.frame.state.liveSpace+(F.w+2)-S.frame.state.storage.baseSpace) ≤ F.TPB
    omega
  · have sp : t.scalars.peak ≤ F.SPB := by have := cb.scalarPeak; simp [NExpr.nodes] at pu; omega
    have st : t.frame.state.storage.peak ≤ F.TPB := by
      rw [tstate,nextEq]
      have := cb.storagePeak; have := vf.live
      show max S.frame.state.storage.peak (S.frame.state.liveSpace+(F.w+2)-S.frame.state.storage.baseSpace) ≤ F.TPB
      omega
    have := cb.outerPeak
    omega
  · rw [tstate,forestEq,constructRows_old S.frame.state.forest i32 S.scope F.w F.V (by have := ok.before; omega)]
    exact vf.vtag
  · obtain ⟨m,hm⟩ := vf.flag
    refine ⟨m,?_⟩
    rw [trw,List.append_assoc,List.getElem?_append_left (by have := ok.before; omega)]
    rw [ps.writable] at hm
    exact hm

abbrev cidx0 : NExpr := .cast u64 (.literal i32 0)
abbrev assignStmt : NStmt := .assignRange (.row (.local 5) (.integer i32) cidx0) 0 0 i32 false true

theorem assign_row0 (F : Fixed) (ok : FixedOK F) {L0 W T : Nat} (S : NState)
    (hv : F.vbuf.items = F.items.map Value.integer) (hw1 : 1 ≤ F.w) (space : L0+F.w+F.n*F.w+3 ≤ F.TPB)
    (inv : ConsInv F L0 W T S) (cap : liveS S+12 ≤ F.SPB) :
    ∃ t, assignStmt.run S = some ⟨t,none,false⟩ ∧ RetInv F F.sc L0 (W+10) (T+F.n+1) t := by
  have hs5 : S.vectorSlot 5 = some 1 := inv.ctx.slot
  have hs0 : S.vectorSlot 0 = some 0 := by simp [NState.vectorSlot,inv.shape.slots,mainSlots]
  have lit : i32.valid 0 = true := by simp [Ty.valid]
  have zero : u64.valid 0 = true := by simp [Ty.valid]
  have idxValue : cidx0.denote (envOf S) = some ((0 : Nat) : Int) := by
    simp [NExpr.denote,lit,Ty.convert_of_valid _ _ zero]
  obtain ⟨m,hm⟩ := inv.vflag
  obtain ⟨rowBuf,rowFound,rowItems,rowCap,rowLimit⟩ := inv.rows.current (by omega)
  have vlen : F.vbuf.items.length = F.n := by rw [hv]; simp [ok.nEq]
  have limit : F.vbuf.items.length ≤ rowBuf.limit := by
    rw [rowLimit,vlen]
    have := sizeLimit_i32 F.n ok.nSmall
    exact this
  obtain ⟨t,run,tframe,sl,sc',me,bi,ba,wl,wu,pl,pu,ql,qu⟩ := assign_range_stmt S 5 1 0 0 cidx0 0 F.R F.w F.sc F.V F.vsc i32
    false m rowBuf F.vbuf (by simp [NExpr.scalarOnly]) idxValue hs5 hs0 inv.ctx.binding
    (by rw [inv.shape.frameBindings]; simp [vbind,atom]) inv.ctx.graph inv.ctx.lengths inv.ctx.flag hw1
    (by simpa using rowFound) inv.vtag inv.rows.vFound hm (by simp) ok.before limit
  refine ⟨t,run,?_⟩
  -- validity of the replaced row buffer
  obtain ⟨objectBuffer,object,foundObject⟩ := row_object S.frame F.R i32 F.w F.sc 0 inv.ctx.graph hw1
  have sameCur : objectBuffer = rowBuf := by
    have h : S.frame.state.storage.lookup (F.R+1+0) = some rowBuf := by simpa using rowFound
    rw [h] at foundObject
    exact (Option.some.inj foundObject).symm
  subst sameCur
  obtain ⟨_,rowOwner,rowValid,_,_⟩ := buffer_facts S.frame (F.R+1+0) i32 objectBuffer _ object
  have vbinding : S.frame.bindings[0]? = some ⟨F.V,.integer i32,false,.root F.vsc⟩ := by
    rw [inv.shape.frameBindings]; simp [vbind,atom]
  obtain ⟨_,vobject,_⟩ := resolve_vroot S.frame 0 F.V F.vsc i32 false m F.vbuf vbinding inv.ctx.graph.valid
    inv.vtag inv.rows.vFound inv.ctx.lengths hm (by simp)
  obtain ⟨_,_,vValid,_,_⟩ := buffer_facts S.frame F.V i32 F.vbuf _ vobject
  have newValid := CppVectorRange.assign_preserves_valid objectBuffer F.vbuf (accepts (.integer i32)) 0
    F.vbuf.items.length rowValid vValid (by omega) (by omega) (by omega)
  have owns : (CppVectorRange.assignResult objectBuffer F.vbuf 0 F.vbuf.items.length).buffer.owner = F.R+1+0 := by
    simpa [CppVectorRange.assign_owner] using rowOwner
  have wf := row_update_valid S.frame F.R i32 F.w F.sc 0 inv.ctx.graph hw1 objectBuffer _
    (CppVectorRange.assignResult objectBuffer F.vbuf 0 F.vbuf.items.length) (by simpa using rowFound) rfl owns newValid
  have foundCur : S.frame.state.storage.lookup (F.R+1+0) = some objectBuffer := by simpa using rowFound
  have bound := CppVectorStore.lookup_bound S.frame.state.storage (F.R+1+0) objectBuffer foundCur
  have updatedSelf := CppNestedOps.updated_lookup_self S.frame (F.R+1+0) objectBuffer
    (CppVectorRange.assignResult objectBuffer F.vbuf 0 F.vbuf.items.length) bound
  have updatedOther : ∀ o, o ≠ F.R+1+0 → (S.frame.updated (F.R+1+0) objectBuffer
      (CppVectorRange.assignResult objectBuffer F.vbuf 0 F.vbuf.items.length)).state.storage.lookup o =
        S.frame.state.storage.lookup o := fun o different =>
    CppNestedOps.updated_lookup_other S.frame (F.R+1+0) o objectBuffer _ (by omega)
  have tstate : t.frame.state = (S.frame.updated (F.R+1+0) objectBuffer
      (CppVectorRange.assignResult objectBuffer F.vbuf 0 F.vbuf.items.length)).state := by rw [tframe]
  have tbind : t.frame.bindings = S.frame.bindings := by simp [tframe,Frame.updated]
  have trw : t.frame.rootWritable = S.frame.rootWritable := by simp [tframe,Frame.updated]
  have lengthsEq : t.frame.state.storage.objects.length = S.frame.state.storage.objects.length := by
    rw [tstate]; simp [Frame.updated]
  have forestEq : t.frame.state.forest = S.frame.state.forest := by rw [tstate]; rfl
  have rootGraph := rootGraph_updated S.frame F.R i32 F.w F.sc inv.ctx.graph (F.R+1+0) objectBuffer
    (CppVectorRange.assignResult objectBuffer F.vbuf 0 F.vbuf.items.length) (by omega) wf
  have rowTagS := row_tag S.frame F.R i32 F.w F.sc 0 inv.ctx.graph hw1
  have live := liveSpace_update S.frame.state t.frame.state (F.R+1+0) bound lengthsEq forestEq
    (by intro o ho; rw [tstate]; exact updatedOther o ho)
  have nodeS := nodeSpace_row S.frame.state i32 F.R 0 objectBuffer rowTagS foundCur
  have nodeT := nodeSpace_row t.frame.state i32 F.R 0
    (CppVectorRange.assignResult objectBuffer F.vbuf 0 F.vbuf.items.length).buffer
    (by rw [forestEq]; exact rowTagS) (by rw [tstate]; exact updatedSelf)
  have storageT : t.frame.state.storage.work = S.frame.state.storage.work+(F.vbuf.items.length-0+1) ∧
      t.frame.state.storage.peak = max S.frame.state.storage.peak
        (S.frame.state.liveSpace+((if objectBuffer.capacity < F.vbuf.items.length-0 then
          objectBuffer.capacity+(F.vbuf.items.length-0)+2 else objectBuffer.capacity+2)-(objectBuffer.capacity+1))-
          S.frame.state.storage.baseSpace) ∧
      t.frame.state.storage.baseSpace = S.frame.state.storage.baseSpace := by
    rw [tstate]; simp [Frame.updated,CppVectorRange.assignResult]
  have capN : (CppVectorRange.assignResult objectBuffer F.vbuf 0 F.vbuf.items.length).buffer.capacity = F.n := by
    simp [CppVectorRange.assignResult,rowCap,vlen]
  have itemsN : (CppVectorRange.assignResult objectBuffer F.vbuf 0 F.vbuf.items.length).buffer.items =
      ((tableRow F.items 0).take F.n).map Value.integer := by
    have full : (tableRow F.items 0).take F.n = F.items := by
      apply List.take_of_length_le
      simp [tableRow,ok.nEq]
    rw [full,← hv]
    simp [CppVectorRange.assignResult,CppVectorRange.slice,vlen]
    exact List.take_of_length_le (by omega)
  have limitN : (CppVectorRange.assignResult objectBuffer F.vbuf 0 F.vbuf.items.length).buffer.limit =
      CppVectorBindings.sizeLimit i32 := by
    simp [CppVectorRange.assignResult,rowLimit]
  have rows0 : RowsOK t.frame.state F.R F.n F.w F.items F.V F.vbuf 0 ((tableRow F.items 0).take F.n) F.n :=
    rowsOK_set _ _ inv.rows ok.before hw1 _ (by rw [tstate]; exact updatedSelf)
      (by intro o ho; rw [tstate]; exact updatedOther o ho) itemsN capN limitN
  have rowsN := rowsOK_advance ok.nEq hw1 rows0
  have liveN : t.frame.state.liveSpace = L0+F.w+1+F.n := by
    have a := inv.live
    rw [nodeS,nodeT,rowCap,capN] at live
    omega
  have nSpace : F.n ≤ F.n*F.w := Nat.le_mul_of_pos_right _ hw1
  have storagePeak : t.frame.state.storage.peak ≤ F.TPB := by
    have h := storageT.2.1
    have s1 := inv.storagePeak
    have lv := inv.live
    rw [h]
    simp only [rowCap,vlen]
    split <;> omega
  have sp : t.scalars.peak ≤ F.SPB := by
    have := inv.scalarPeak; simp [NExpr.nodes,Container.nodes] at pu; omega
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,⟨?_,?_,?_,?_,?_⟩,?_,rowsN,liveN,space,?_,?_,sp,storagePeak,?_⟩
  · rw [sl]; exact inv.shape.slots
  · rw [me]; exact inv.shape.memory
  · rw [bi]; exact inv.shape.bindings
  · rw [ba]; exact inv.shape.base
  · rw [sc']; exact inv.shape.scope
  · rw [tbind]; exact inv.shape.frameBindings
  · rw [trw]; exact inv.shape.writable
  · simpa [NState.vectorSlot,sl] using hs5
  · rw [tbind]; exact inv.ctx.binding
  · rw [tstate]; exact rootGraph
  · rw [trw,forestEq]; exact inv.ctx.lengths
  · rw [trw]; exact inv.ctx.flag
  · exact inv.bnd.of_forest forestEq
  · have := inv.scalarWork; simp [NExpr.nodes,Container.nodes] at wu; omega
  · rw [storageT.1,inv.storageWork]; simp [vlen]; omega
  · have := inv.outerPeak; omega

end Proofs.DoublingPrologue
