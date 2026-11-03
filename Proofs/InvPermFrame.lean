import Proofs.FillWriteStmt
import Proofs.InvPermMath

namespace Proofs.InvPermFrame
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppMixedInvoke
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.FlatVectorStmt Proofs.FillWriteStmt
open Proofs.CppState (Cell)

-- Every owner of the extended forest is an old owner or the new root itself.
theorem fill_ctx (T next : Proofs.CppNestedVectorStore.State) (ty : Ty) (scope count : Nat) (x : Int)
    (ran : T.fillVector ty scope count x = some next) (owner context : Nat)
    (h : next.forest.context owner = some context) :
    T.forest.context owner = some context ∨ (owner = T.forest.objects.length ∧ context = scope) := by
  have forestEq := fillVector_forest T ty scope count x next ran
  rw [forestEq] at h
  by_cases old : owner < T.forest.objects.length
  · have agree : ∀ i, i < T.forest.objects.length →
        (T.forest.declareRoot ty scope).lookup i = T.forest.lookup i :=
      fun i hi => declareRoot_old T.forest ty scope i hi
    rw [context_agree T.forest _ _ agree owner old] at h
    exact Or.inl h
  · by_cases isNew : owner = T.forest.objects.length
    · subst isNew
      have rooted : (T.forest.declareRoot ty scope).rootOwner T.forest.objects.length =
          some T.forest.objects.length := by
        rw [rootOwner_eq]
        simp [declareRoot_new,flatTag]
      simp [Forest.context,rooted,declareRoot_new,flatTag] at h
      exact Or.inr ⟨rfl,by omega⟩
    · have absent : (T.forest.declareRoot ty scope).lookup owner = none := by
        simp only [Forest.lookup]
        have : (T.forest.declareRoot ty scope).objects[owner]? = none :=
          List.getElem?_eq_none (by rw [declareRoot_length]; omega)
        simp [this]
      have ro : (T.forest.declareRoot ty scope).rootOwner owner = none := by
        rw [rootOwner_eq,absent]; rfl
      simp [Forest.context,ro] at h

theorem fill_live (s next : Proofs.CppNestedVectorStore.State) (ty : Ty) (scope count : Nat) (x : Int)
    (ran : s.fillVector ty scope count x = some next) : next.liveSpace = s.liveSpace+1+count := by
  obtain ⟨valid,_,_,_,_⟩ := fillVector_inv s ty scope count x next ran
  obtain ⟨lengths,_,_⟩ := wellFormed_parts s valid
  have forestEq := fillVector_forest s ty scope count x next ran
  have objLen := fillVector_objects_length s ty scope count x next ran
  have oldSpace : ∀ o, o < s.storage.objects.length → next.nodeSpace o = s.nodeSpace o := by
    intro o inside
    simp only [State.nodeSpace]
    rw [forestEq,declareRoot_old s.forest ty scope o (by omega),
      fillVector_storage_old s ty scope count x o next ran inside]
  have newSpace : next.nodeSpace s.storage.objects.length = count+1 := by
    simp only [State.nodeSpace]
    have rl := declareRoot_new s.forest ty scope
    rw [lengths] at rl
    rw [forestEq,rl,fillVector_storage_new s ty scope count x next ran]
    simp [flatTag]
  unfold State.liveSpace
  rw [objLen,List.range_succ,List.map_append,List.sum_append]
  have sumOld : ((List.range s.storage.objects.length).map next.nodeSpace).sum = s.liveSpace := by
    unfold State.liveSpace
    congr 1
    apply List.map_congr_left
    intro o member
    exact oldSpace o (List.mem_range.mp member)
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  rw [sumOld,newSpace]
  unfold State.liveSpace
  omega

theorem nodeSpace_flat_ty (T : Proofs.CppNestedVectorStore.State) (R sc : Nat) (ty : Ty) (b : Buffer Value)
    (tag : T.forest.lookup R = some (flatTag ty sc)) (found : T.storage.lookup R = some b) :
    T.nodeSpace R = b.capacity + 1 := by
  simp [State.nodeSpace,tag,found,flatTag]

-- Frame facts once the result vector's root exists next to the input vector `v`.
structure IF (fr : Frame) (V vsc R sc L0 T0 : Nat) (vbuf b : Buffer Value) : Prop where
  valid : fr.state.wellFormed = true
  lengths : fr.rootWritable.length = fr.state.forest.objects.length
  vtag : fr.state.forest.lookup V = some ⟨.integer i32,none,some vsc,[]⟩
  vfound : fr.state.storage.lookup V = some vbuf
  tag : fr.state.forest.lookup R = some (flatTag i32 sc)
  found : fr.state.storage.lookup R = some b
  vflag : ∃ m, fr.rootWritable[V]? = some m
  flag : fr.rootWritable[R]? = some true
  bindings : fr.bindings = [vbind V vsc,flatBinding R i32 sc]
  ctx : ∀ owner c, fr.state.forest.context owner = some c → c < sc ∨ (c = sc ∧ owner = R)
  live : fr.state.liveSpace = L0 + 1 + b.capacity
  work : fr.state.storage.work = T0
  limit : b.limit = CppVectorBindings.sizeLimit i32
  owner : b.owner = R
  count : fr.state.storage.objects.length = R + 1
  before : V < R

theorem IF.bufferValid {fr : Frame} {V vsc R sc L0 T0 : Nat} {vbuf b : Buffer Value}
    (fb : IF fr V vsc R sc L0 T0 vbuf b) : b.Valid (accepts (.integer i32)) := by
  have object := object_runs fr R (.integer i32) b (flatTag i32 sc) fb.valid fb.found fb.tag rfl
  obtain ⟨_,_,valid,_,_⟩ := buffer_facts fr R i32 b _ object
  exact valid

-- Replacing the root's buffer by another valid buffer.
theorem IF.update {fr : Frame} {V vsc R sc L0 T0 : Nat} {vbuf b : Buffer Value}
    (fb : IF fr V vsc R sc L0 T0 vbuf b) (res : CppVector.Result Value Unit) (owns : res.buffer.owner = R)
    (valid' : res.buffer.Valid (accepts (.integer i32)))
    (limit' : res.buffer.limit = CppVectorBindings.sizeLimit i32) :
    IF (fr.updated R b res) V vsc R sc L0 (T0+res.work) vbuf res.buffer := by
  have bound : R < fr.state.storage.objects.length := CppVectorStore.lookup_bound _ R b fb.found
  have lengthsEq : (fr.updated R b res).state.storage.objects.length = fr.state.storage.objects.length := by
    simp [Frame.updated]
  have forestEq : (fr.updated R b res).state.forest = fr.state.forest := rfl
  have other : ∀ o, o ≠ R → (fr.updated R b res).state.storage.lookup o = fr.state.storage.lookup o :=
    fun o ho => CppNestedOps.updated_lookup_other fr R o b res (by omega)
  have self := CppNestedOps.updated_lookup_self fr R b res bound
  have live := liveSpace_update fr.state (fr.updated R b res).state R bound lengthsEq forestEq other
  have n0 := nodeSpace_flat_ty fr.state R sc i32 b fb.tag fb.found
  have n1 := nodeSpace_flat_ty (fr.updated R b res).state R sc i32 res.buffer (by rw [forestEq]; exact fb.tag) self
  have vne : V ≠ R := by have := fb.before; omega
  refine ⟨?_,?_,?_,?_,?_,self,?_,?_,?_,?_,?_,?_,limit',owns,?_,fb.before⟩
  · exact updated_wellFormed fr R b (flatTag i32 sc) res fb.valid fb.tag bound owns
      (by simp [payloadOK,flatTag,valid'])
  · simpa [Frame.updated] using fb.lengths
  · exact fb.vtag
  · rw [other V vne]; exact fb.vfound
  · exact fb.tag
  · simpa [Frame.updated] using fb.vflag
  · simpa [Frame.updated] using fb.flag
  · simpa [Frame.updated] using fb.bindings
  · intro owner c h
    exact fb.ctx owner c h
  · rw [n0,n1] at live
    have := fb.live
    omega
  · simp [Frame.updated,fb.work]
  · rw [lengthsEq]; exact fb.count

theorem IF.noop {fr fr' : Frame} {V vsc R sc L0 T0 : Nat} {vbuf b : Buffer Value}
    (fb : IF fr V vsc R sc L0 T0 vbuf b)
    (hs : fr'.state = (noopRetired fr).state) (hrw : fr'.rootWritable = fr.rootWritable)
    (hb : fr'.bindings = fr.bindings) : IF fr' V vsc R sc L0 T0 vbuf b := by
  have same : SameObjects fr.state fr'.state := by rw [hs]; exact noopRetired_same fr
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,fb.limit,fb.owner,?_,fb.before⟩
  · rw [same.wellFormed]; exact fb.valid
  · rw [hrw,same.1]; exact fb.lengths
  · rw [same.1]; exact fb.vtag
  · rw [same.lookup]; exact fb.vfound
  · rw [same.1]; exact fb.tag
  · rw [same.lookup]; exact fb.found
  · rw [hrw]; exact fb.vflag
  · rw [hrw]; exact fb.flag
  · rw [hb]; exact fb.bindings
  · intro owner c h
    rw [same.1] at h
    exact fb.ctx owner c h
  · rw [same.liveSpace]; exact fb.live
  · rw [hs]; exact fb.work
  · rw [same.2.1]; exact fb.count


-- Scalar shape of the states once the result root exists: `v` then the result vector.
structure PT (F : Fixed) (scope : Nat) (rw0 : List Bool) (S : NState) (cells : List Cell)
    (binds : List CppState.Binding) (slots : List Location) : Prop where
  slots : S.slots = slots
  memory : S.scalars.memory = F.P ++ cells
  bindings : S.scalars.bindings = binds
  base : S.scalars.baseMemory = F.B
  scope : S.scope = scope
  frameBindings : S.frame.bindings = [vbind F.V F.vsc,flatBinding F.R i32 F.sc]
  writable : S.frame.rootWritable = rw0 ++ [true]

theorem PT.core {F : Fixed} {scope : Nat} {rw0 : List Bool} {S t : NState} {cells binds slots}
    (ps : PT F scope rw0 S cells binds slots) (core : Core S t) : PT F scope rw0 t cells binds slots := by
  obtain ⟨frame,sl,sc,me,bi,ba⟩ := core
  exact ⟨by rw [sl]; exact ps.slots,by rw [me]; exact ps.memory,by rw [bi]; exact ps.bindings,
    by rw [ba]; exact ps.base,by rw [sc]; exact ps.scope,by rw [frame]; exact ps.frameBindings,
    by rw [frame]; exact ps.writable⟩

theorem PT.live_eq {F : Fixed} {scope : Nat} {rw0 : List Bool} {S : NState} {cells binds slots}
    (ps : PT F scope rw0 S cells binds slots) : liveS S = F.P.length+cells.length-F.B+binds.length := by
  simp [liveS,ps.memory,ps.bindings,ps.base]

theorem PT.enter {F : Fixed} {sc : Nat} {rw0 : List Bool} {S : NState} {cells binds slots}
    (ps : PT F sc rw0 S cells binds slots) : PT F (sc+1) rw0 {S with scope := S.scope+1} cells binds slots :=
  ⟨ps.slots,ps.memory,ps.bindings,ps.base,by simp [ps.scope],ps.frameBindings,ps.writable⟩

theorem PT.self {F : Fixed} {sc : Nat} {rw0 : List Bool} {S : NState} {cells binds slots}
    (ps : PT F sc rw0 S cells binds slots) : PT F S.scope rw0 S cells binds slots :=
  ⟨ps.slots,ps.memory,ps.bindings,ps.base,rfl,ps.frameBindings,ps.writable⟩

def cellsN (n : Int) : List Cell := [⟨i32,n⟩]
def cellsNI (n i : Int) : List Cell := [⟨i32,n⟩,⟨i32,i⟩]
def bindsN (F : Fixed) : List CppState.Binding := [⟨F.P.length,true⟩]
def bindsNI (F : Fixed) : List CppState.Binding := [⟨F.P.length,true⟩,⟨F.P.length+1,true⟩]
def slotsN : List Location := [.vector 0,.scalar 0]
def slotsNR : List Location := [.vector 0,.scalar 0,.vector 1]
def slotsNRI : List Location := [.vector 0,.scalar 0,.vector 1,.scalar 1]

abbrev fcE : NExpr := .cast u64 (.variable i32 1)
abbrev fvE : NExpr := .unary i32 .neg (.literal i32 1)
abbrev fillStmt : NStmt := .fillVector i32 true fcE fvE

theorem fcE_scalar : fcE.scalarOnly = true := by simp [NExpr.scalarOnly]
theorem fvE_scalar : fvE.scalarOnly = true := by simp [NExpr.scalarOnly]

theorem fvE_value (env : Nat → Ty → Option Int) : fvE.denote env = some (-1) := by
  have lit : i32.valid (1 : Int) = true := by simp [Ty.valid]
  have neg : i32.valid (-1 : Int) = true := by simp [Ty.valid]
  have c1 := Ty.convert_of_valid i32 (-1) neg
  simp [NExpr.denote,lit,unaryValue,c1]

theorem fcE_value (env : Nat → Ty → Option Int) (n : Nat) (h : env 1 i32 = some (n : Int)) (hn : n < 2147483648) :
    fcE.denote env = some (n : Int) := by
  have valid : u64.valid (n : Int) = true := u64_valid_nat n (by omega)
  simp [NExpr.denote,h,Ty.convert_of_valid _ _ valid]


-- `int n = v.size();`
abbrev nE : NExpr := .cast i32 (.size (.integer i32) (.local 0))
abbrev declNStmt : NStmt := .declare i32 true nE

theorem declN_step (F : Fixed) {rw0 : List Bool} {L0 T0 W : Nat} (S : NState) (n : Nat)
    (hvn : F.vbuf.items.length = n) (hn : n < 2147483648)
    (ps : PS F F.sc rw0 S [] [] [.vector 0]) (vf : VF F L0 T0 S.frame) (cb : Cb F W S)
    (cap : liveS S+12 ≤ F.SPB) :
    ∃ t, declNStmt.run S = some ⟨t,none,false⟩ ∧ PS F F.sc rw0 t (cellsN n) (bindsN F) slotsN ∧
      t.frame = S.frame ∧ Cb F (W+10) t := by
  have hs : S.vectorSlot 0 = some 0 := by simp [NState.vectorSlot,ps.slots]
  obtain ⟨t1,first⟩ := sizeV_ev F S ((NExpr.size (.integer i32) (.local 0)).nodes+1) hs ps.frameBindings vf (by omega)
  have valid : i32.valid (n : Int) = true := i32_valid_nat n hn
  have ev := Ev.cast first (v' := (n : Int)) (by rw [hvn]; exact Ty.convert_of_valid _ _ valid)
  have good := Ev.good (by simpa using ev : Ev S nE _ (n : Int) [] _ _)
  obtain ⟨t,run,frame,sl,sc,me,bi,ba,wl,wu,pl,pu,ql,qu⟩ := declare_of_good nE i32 true S _ _ _ _ _ (Ev.eval ev) good
    (Nat.le_trans (by omega) (Nat.le_max_right _ _)) (Ty.convert_of_valid _ _ valid)
  have memLen : S.scalars.memory.length = F.P.length := by simp [ps.memory]
  have bindLen : S.scalars.bindings.length = 0 := by simp [ps.bindings]
  refine ⟨t,run,⟨?_,?_,?_,?_,?_,?_,?_⟩,frame,?_⟩
  · rw [sl,bindLen,ps.slots]; rfl
  · rw [me,ps.memory]; simp [cellsN]
  · rw [bi,memLen,ps.bindings]; simp [bindsN]
  · rw [ba]; exact ps.base
  · rw [sc]; exact ps.scope
  · rw [frame]; exact ps.frameBindings
  · rw [frame]; exact ps.writable
  · have pu' : t.scalars.peak ≤ max S.scalars.peak (liveS S+12) := by
      try simp [NExpr.nodes,Container.nodes] at pu ⊢
      omega
    have wu' : t.scalars.work ≤ S.scalars.work+10 := by
      try simp [NExpr.nodes,Container.nodes] at wu ⊢
      omega
    exact cb.step frame wu' pu' cap qu


-- `std::vector<int> inv(n, -1);`
theorem fill_phase (F : Fixed) {rw0 : List Bool} {L0 T0 W : Nat} (S : NState) (n : Nat)
    (hn : n < 2147483648) (hscope : S.scope = F.sc) (hV : F.V < F.R)
    (ps : PS F F.sc rw0 S (cellsN n) (bindsN F) slotsN) (vf : VF F L0 T0 S.frame) (cb : Cb F W S)
    (cap : liveS S+60 ≤ F.SPB) (space : L0+n+2 ≤ F.TPB) :
    ∃ t b, fillStmt.run S = some ⟨t,none,false⟩ ∧ PT F F.sc rw0 t (cellsN n) (bindsN F) slotsNR ∧
      IF t.frame F.V F.vsc F.R F.sc L0 (T0+n+1) F.vbuf b ∧
      b.items = List.replicate n (Value.integer (-1)) ∧ b.capacity = n ∧ Cb F (W+30) t := by
  have e1 : envOf S 1 i32 = some (n : Int) :=
    envOf_at S 1 0 ⟨F.P.length,true⟩ i32 n (by simp [ps.slots,slotsN]) (by simp [ps.bindings,bindsN])
      (by simp [ps.memory,cellsN]) (i32_valid_nat n hn)
  have supported : CppVectorBindings.supported i32 := by simp [CppVectorBindings.supported,i32]
  have limit : n ≤ CppVectorBindings.sizeLimit i32 := by
    simp [CppVectorBindings.sizeLimit,i32]; omega
  have xv : i32.valid (-1) = true := by simp [Ty.valid]
  obtain ⟨t,next,declared,run,tf,sl,sc',me,bi,ba,wl,wu,pl,pu,ql,qu⟩ := fill_vec_stmt S i32 fcE fvE n (-1)
    fcE_scalar fvE_scalar (fcE_value _ n e1 hn) (fvE_value _) supported limit xv vf.valid vf.lengths
  obtain ⟨lengthsEq,_,_⟩ := wellFormed_parts S.frame.state vf.valid
  obtain ⟨_,_,_,_,hnextDef⟩ := fillVector_inv S.frame.state i32 S.scope n (-1) next declared
  have forestEq := fillVector_forest S.frame.state i32 S.scope n (-1) next declared
  have nextValid := fillVector_wellFormed S.frame.state i32 S.scope n (-1) next declared
  have objLen := fillVector_objects_length S.frame.state i32 S.scope n (-1) next declared
  have found := fillVector_storage_new S.frame.state i32 S.scope n (-1) next declared
  have liveN := fill_live S.frame.state next i32 S.scope n (-1) declared
  have workN := fillVector_work S.frame.state i32 S.scope n (-1) next declared
  have rootId : S.frame.state.storage.objects.length = F.R := vf.rootId.symm
  have tagLookup : next.forest.lookup F.R = some (flatTag i32 F.sc) := by
    rw [forestEq,← rootId,← lengthsEq,← hscope]; exact declareRoot_new _ i32 S.scope
  have rwLen : S.frame.rootWritable.length = F.R := by rw [vf.lengths,lengthsEq,rootId]
  have tfs : t.frame.state = next := by rw [tf]
  have tfr : t.frame.rootWritable = S.frame.rootWritable ++ [true] := by rw [tf]
  have tfb : t.frame.bindings = [vbind F.V F.vsc,flatBinding F.R i32 F.sc] := by
    rw [tf]; simp only []; rw [ps.frameBindings,rootId,hscope]; rfl
  have vbound : F.V < S.frame.state.forest.objects.length := by omega
  have vbound' : F.V < S.frame.state.storage.objects.length := by omega
  refine ⟨t,⟨F.R,List.replicate n (Value.integer (-1)),n,CppVectorBindings.sizeLimit i32,0⟩,run,⟨?_,?_,?_,?_,?_,?_,?_⟩,⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hV⟩,?_,?_,?_⟩
  · rw [sl,ps.slots,ps.frameBindings]; rfl
  · rw [me,ps.memory]
  · rw [bi,ps.bindings]
  · exact ba.trans ps.base
  · exact sc'.trans hscope
  · exact tfb
  · rw [tfr,ps.writable]
  · rw [tfs]; exact nextValid
  · simp [tfr,tfs,forestEq,declareRoot_length,vf.lengths]
  · rw [tfs,forestEq,declareRoot_old _ _ _ _ vbound]; exact vf.vtag
  · rw [tfs,fillVector_storage_old S.frame.state i32 S.scope n (-1) F.V next declared vbound']; exact vf.vfound
  · rw [tfs]; exact tagLookup
  · rw [tfs,← rootId]; exact found
  · obtain ⟨m,hm⟩ := vf.flag
    refine ⟨m,?_⟩
    rw [tfr,List.getElem?_append_left (by omega)]; exact hm
  · rw [tfr,List.getElem?_append_right (by omega)]; simp [rwLen]
  · exact tfb
  · intro owner c h
    rw [tfs] at h
    rcases fill_ctx S.frame.state next i32 S.scope n (-1) declared owner c h with old | ⟨ho,hc⟩
    · left; exact vf.strict owner c old
    · right; exact ⟨by rw [hc,hscope],by rw [ho,lengthsEq,rootId]⟩
  · rw [tfs,liveN,vf.live] <;> omega
  · rw [tfs,workN,vf.work]
  · rfl
  · rw [← rootId]
  · rw [tfs,objLen,rootId]
  · rfl
  · rfl
  · have nextPeak : next.storage.peak = max S.frame.state.storage.peak
        (S.frame.state.liveSpace+(n+2)-S.frame.state.storage.baseSpace) := by
      rw [hnextDef]
    have spB := cb.scalarPeak
    have stB := cb.storagePeak
    have opB := cb.outerPeak
    have nodesC : fcE.nodes = 2 := by simp [NExpr.nodes]
    have nodesV : fvE.nodes = 2 := by simp [NExpr.nodes]
    have stT : next.storage.peak ≤ F.TPB := by
      rw [nextPeak]
      have := vf.live
      omega
    refine ⟨?_,?_,?_,?_⟩
    · have := cb.work; omega
    · omega
    · rw [tfs]; exact stT
    · have : t.peak ≤ max S.peak (t.scalars.peak+next.storage.peak) := by omega
      omega

end Proofs.InvPermFrame
