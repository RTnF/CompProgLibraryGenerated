import Proofs.DoublingProgram
import Proofs.CppNestedCall

namespace Proofs.DoublingCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope
open Proofs.CppNestedCall Proofs.DoublingNested Proofs.DoublingPrologue Proofs.CppNestedFacts
open Proofs.CppState (Cell)

-- What the caller must provide: a bound root vector `v` holding the table's first row.
structure CallerOK (caller : NState) (vslot vb V vsc : Nat) (wV m : Bool) (vbuf : Buffer Value) : Prop where
  valid : caller.frame.state.wellFormed = true
  slot : caller.vectorSlot vslot = some vb
  binding : caller.frame.bindings[vb]? = some ⟨V,.integer i32,wV,.root vsc⟩
  vtag : caller.frame.state.forest.lookup V = some ⟨.integer i32,none,some vsc,[]⟩
  vfound : caller.frame.state.storage.lookup V = some vbuf
  lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length
  flag : caller.frame.rootWritable[V]? = some m
  perm : wV = true → m = true
  strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope
  base : caller.scalars.baseMemory ≤ caller.scalars.memory.length

theorem resolve_vec (caller : NState) {vslot vb V vsc : Nat} {wV m : Bool} {vbuf : Buffer Value}
    (ok : CallerOK caller vslot vb V vsc wV m vbuf) :
    resolve caller (.vector i32 false) (.vectorReference vslot) =
      some (caller.charge 1 1,.vector V vsc i32 false) := by
  obtain ⟨resolved,_,_⟩ := resolve_vroot caller.frame vb V vsc i32 wV m vbuf ok.binding ok.valid ok.vtag ok.vfound
    ok.lengths ok.flag ok.perm
  simp [resolve,ok.slot,ok.binding,resolved]

theorem resolve_val (caller : NState) (kexpr : NExpr) (K : Int) (hs : kexpr.scalarOnly = true)
    (ty : kexpr.resultType = u64) (value : kexpr.denote (envOf caller) = some K) :
    ∃ t, Good (caller.charge 1 1) t kexpr.nodes kexpr.nodes ∧
      resolve (caller.charge 1 1) (.scalar u64 false true) (.value kexpr) = some (t,.scalar u64 true K) := by
  obtain ⟨t,ran,good⟩ := scalar_eval kexpr (caller.charge 1 1) K hs
    (by rw [envOf_core (core_charge caller 1 1)]; exact value)
  exact ⟨t,good,by simp [resolve,ty,ran]⟩

def callerP (caller : NState) : List Cell :=
  caller.scalars.memory ++ List.replicate (caller.scalars.bindings.length+caller.frame.bindings.length)
    ⟨⟨1,false,true⟩,0⟩

theorem bindRoot_v (state : Proofs.CppNestedVectorStore.State) (rw : List Bool) {V vsc : Nat} {m : Bool}
    {vbuf : Buffer Value} (valid : state.wellFormed = true)
    (vtag : state.forest.lookup V = some ⟨.integer i32,none,some vsc,[]⟩)
    (vfound : state.storage.lookup V = some vbuf) (lengths : rw.length = state.forest.objects.length)
    (flag : rw[V]? = some m) :
    (⟨state,rw,[]⟩ : Frame).bindRoot V (.integer i32) vsc false = some (⟨state,rw,[vbind V vsc]⟩,0) := by
  have vobject : (⟨state,rw,[]⟩ : Frame).object V (.integer i32) = some (vbuf,⟨.integer i32,none,some vsc,[]⟩) :=
    object_runs _ V _ vbuf _ valid vfound vtag rfl
  have vrooted : state.forest.rootOwner V = some V := CppVectorOwnership.root_runs _ V _ vtag rfl
  have vmax : (⟨state,rw,[]⟩ : Frame).maximum V = some m := maximum_runs _ V V m lengths vrooted flag
  simp only [Frame.bindRoot,vobject,vmax,Bind.bind,Option.bind]
  simp [Frame.addBinding,vbind,atom]

theorem prepare_doubling (caller : NState) {vslot vb V vsc : Nat} {wV m : Bool} {vbuf : Buffer Value}
    (ok : CallerOK caller vslot vb V vsc wV m vbuf) (kexpr : NExpr) (K : Int) (hs : kexpr.scalarOnly = true)
    (ty : kexpr.resultType = u64) (value : kexpr.denote (envOf caller) = some K) (kv : u64.valid K = true) :
    ∃ t, Good (caller.charge 1 1) t kexpr.nodes kexpr.nodes ∧
      ∃ Sinit, prepare caller DoublingNestedInstance.doubling.parameters [.vectorReference vslot,.value kexpr] =
        some Sinit ∧ Sinit.slots = entrySlots ∧ Sinit.scalars.memory = callerP caller ++ [⟨u64,K⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[vbind V vsc]⟩ ∧
        Sinit.scalars.work = t.scalars.work+3 ∧ t.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨t,good,rv⟩ := resolve_val caller kexpr K hs ty value
  have rvec := resolve_vec caller ok
  refine ⟨t,good,?_⟩
  have frameT : t.frame = caller.frame := good.1.1
  simp [prepare,ok.valid,resolveAll,rvec,rv,DoublingNestedInstance.doubling]
  have fs : t.frame.state = caller.frame.state := by rw [frameT]
  have fr : t.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t.scalars.memory = caller.scalars.memory := good.1.2.2.2.1
  have hbind : t.scalars.bindings = caller.scalars.bindings := good.1.2.2.2.2.1
  have hbase : t.scalars.baseMemory = caller.scalars.baseMemory := good.1.2.2.2.2.2
  have bound := bindRoot_v caller.frame.state caller.frame.rootWritable ok.valid ok.vtag ok.vfound ok.lengths ok.flag
  simp [fs,fr,fb,hmem,hbind,hbase,bindAll,bindOne,bound,CppState.bindArgument,kv,callerP,entrySlots,
    NState.observe,CppState.State.observe,vbind,atom]
  exact Nat.le_max_left _ _

-- The table's root keeps its scope tag after the call: it is owned by exactly that tree.
theorem root_context (D : NState) {F : Fixed} {L0 Wd Td : Nat} (hD : Done F F.sc L0 Wd Td D) :
    D.frame.state.forest.context F.R = some F.sc := by
  have tag := hD.ctx.graph.tag
  have rooted : D.frame.state.forest.rootOwner F.R = some F.R := CppVectorOwnership.root_runs _ F.R _ tag rfl
  simp [Forest.context,rooted,tag,rootTag]

theorem tree_unique (D : NState) {F : Fixed} {L0 Wd Td : Nat} (hD : Done F F.sc L0 Wd Td D) (owner : Nat)
    (h : D.frame.state.forest.context owner = some F.sc) : D.frame.state.forest.rootOwner owner = some F.R := by
  obtain ⟨_,root,tree⟩ := hD.bnd
  have rooted : D.frame.state.forest.rootOwner F.R = some F.R :=
    CppVectorOwnership.root_runs _ F.R _ hD.ctx.graph.tag rfl
  have same := tree F.R (root_context D hD)
  rw [rooted] at same
  have eq : F.R = root := Option.some.inj same
  rw [tree owner h,eq]

theorem moved_fresh (D : NState) {F : Fixed} {L0 Wd Td : Nat} (hD : Done F F.sc L0 Wd Td D) (caller : Nat)
    (hscope : F.sc = caller+1) :
    ∀ owner, (D.frame.state.forest.transferred F.R caller (rootTag i32 F.sc F.R F.w)).context owner ≠ some F.sc := by
  intro owner h
  rw [context_transferred D.frame.state.forest F.R caller (rootTag i32 F.sc F.R F.w) hD.ctx.graph.tag rfl owner] at h
  by_cases inTree : D.frame.state.forest.rootOwner owner = some F.R
  · simp [inTree] at h
    omega
  · simp [inTree] at h
    exact inTree (tree_unique D hD owner h)

def movedFrame (f : Frame) (forest' : Forest) : Frame := {f with state := {f.state with forest := forest'}}

def finishResult (caller D : NState) (forest' : Forest) : NState :=
  let callee := D.charge 1 0
  let moved : Frame := movedFrame callee.frame forest'
  let scalars : CppState.State := {caller.scalars with
    memory := callee.scalars.memory.take caller.scalars.memory.length,
    work := callee.scalars.work+1,peak := max caller.scalars.peak callee.scalars.peak}
  let frame : Frame := {noopRetired moved with bindings := caller.frame.bindings}
  (⟨scalars.observe 0,frame,caller.slots,caller.scope,max caller.peak callee.peak⟩ : NState).observe

theorem moved_valid (D : NState) {F : Fixed} {L0 Wd Td : Nat} (hD : Done F F.sc L0 Wd Td D) (caller : Nat) :
    (movedFrame D.frame (D.frame.state.forest.transferred F.R caller (rootTag i32 F.sc F.R F.w))).state.wellFormed = true := by
  have tag := hD.ctx.graph.tag
  have := wellFormed_transferred D.frame.state F.R caller _ tag rfl (by simp [rootTag])
  exact this.trans hD.ctx.graph.valid

theorem moved_live (D : NState) {F : Fixed} {L0 Wd Td : Nat} (hD : Done F F.sc L0 Wd Td D) (caller : Nat) :
    (movedFrame D.frame (D.frame.state.forest.transferred F.R caller (rootTag i32 F.sc F.R F.w))).state.liveSpace =
      D.frame.state.liveSpace := by
  have tag := hD.ctx.graph.tag
  unfold State.liveSpace
  congr 1
  apply List.map_congr_left
  intro o _
  simp only [movedFrame,State.nodeSpace]
  by_cases same : o = F.R
  · subst same
    rw [transferred_lookup_root D.frame.state.forest F.R caller _ tag,tag]
    cases D.frame.state.storage.lookup F.R <;> rfl
  · rw [transferred_lookup_other D.frame.state.forest F.R o caller _ same]

theorem finish_doubling (caller D : NState) {F : Fixed} {L0 Wd Td : Nat} (hD : Done F F.sc L0 Wd Td D)
    (hP : F.P = callerP caller) (hscope : F.sc = caller.scope+1) :
    finish caller (D.charge 1 0) (.vector (.vector (.integer i32))) (some (.vector F.R (.vector atom))) =
      some (finishResult caller D (D.frame.state.forest.transferred F.R caller.scope (rootTag i32 F.sc F.R F.w)),
        .vector F.R (.vector atom)) := by
  have memD : D.scalars.memory = callerP caller ++ [⟨u64,F.K⟩,⟨i32,(F.n : Int)⟩,⟨i32,(F.w : Int)⟩,⟨i32,(F.w : Int)⟩] := by
    rw [hD.shape.memory,hP]
  have take : (D.scalars.memory.take caller.scalars.memory.length) = caller.scalars.memory := by
    rw [memD]
    simp only [callerP,List.append_assoc]
    exact List.take_left
  have tag := hD.ctx.graph.tag
  have transfer := Proofs.CppNestedVectorStore.transfer_valid_root D.frame.state F.R (.vector (.integer i32)) F.sc caller.scope
    (rootTag i32 F.sc F.R F.w) hD.ctx.graph.valid tag rfl rfl rfl
  have validMoved : (movedFrame D.frame (D.frame.state.forest.transferred F.R caller.scope
      (rootTag i32 F.sc F.R F.w))).state.wellFormed = true := by
    have := wellFormed_transferred D.frame.state F.R caller.scope _ tag rfl (by simp [rootTag])
    exact this.trans hD.ctx.graph.valid
  have fresh := retireScope_fresh (movedFrame D.frame (D.frame.state.forest.transferred F.R caller.scope
      (rootTag i32 F.sc F.R F.w))) F.sc validMoved (moved_fresh D hD caller.scope hscope)
  have scopeEq : (D.charge 1 0).scope = F.sc := hD.shape.scope
  have chargeMem : (D.charge 1 0).scalars.memory = D.scalars.memory := rfl
  have chargeFrame : (D.charge 1 0).frame = D.frame := rfl
  have cond : caller.scalars.memory.length ≤ (D.charge 1 0).scalars.memory.length ∧
      List.map Cell.type (List.take caller.scalars.memory.length (D.charge 1 0).scalars.memory) =
        List.map Cell.type caller.scalars.memory := by
    rw [chargeMem,take]
    refine ⟨?_,rfl⟩
    rw [memD]; simp [callerP]
  have trf : (D.charge 1 0).frame.transferRoot F.R (.vector (.integer i32)) F.sc caller.scope =
      some (movedFrame D.frame (D.frame.state.forest.transferred F.R caller.scope (rootTag i32 F.sc F.R F.w))) := by
    rw [chargeFrame]
    simp [Frame.transferRoot,transfer,movedFrame]
  unfold finish
  rw [if_pos cond]
  dsimp only
  have same : (atom.vector = (Element.integer i32).vector) := rfl
  rw [if_pos same]
  simp only [scopeEq,trf,Bind.bind,Option.bind,fresh]
  rfl

structure DoublingPost (caller Sinit res : NState) (kn : Nat) (items : List Int) (V : Nat) (vbuf : Buffer Value) (K : Int) : Prop where
  valid : res.frame.state.wellFormed = true
  vKept : res.frame.state.storage.lookup V = some vbuf
  rows : ∀ k, k < Proofs.BitWidthU64.width K.toNat → ∃ b,
    res.frame.state.storage.lookup (caller.frame.state.storage.objects.length+1+k) = some b ∧
    b.items = (tableRow items k).map Value.integer ∧ b.capacity = items.length
  root : ∃ b, res.frame.state.storage.lookup caller.frame.state.storage.objects.length = some b ∧
    b.items = (rowIds caller.frame.state.storage.objects.length (Proofs.BitWidthU64.width K.toNat)).map Value.child
  rootScope : res.frame.state.forest.context caller.frame.state.storage.objects.length = some caller.scope
  slots : res.slots = caller.slots
  scope : res.scope = caller.scope
  bindings : res.frame.bindings = caller.frame.bindings
  scalarMemory : res.scalars.memory = caller.scalars.memory
  rootWritable : res.frame.rootWritable = caller.frame.rootWritable ++ [true] ++
    List.replicate (Proofs.BitWidthU64.width K.toNat) false
  storageWork : res.frame.state.storage.work = caller.frame.state.storage.work +
    (Proofs.BitWidthU64.width K.toNat+1)+(items.length+1)+
    (Proofs.BitWidthU64.width K.toNat-1)*(2*items.length+1)
  storagePeak : res.frame.state.storage.peak ≤ max caller.frame.state.storage.peak
    (caller.frame.state.liveSpace+Proofs.BitWidthU64.width K.toNat+items.length*Proofs.BitWidthU64.width K.toNat+3)
  scalarWork : res.scalars.work ≤ caller.scalars.work+kn+
    (Proofs.BitWidthU64.width K.toNat-1)*(60*items.length+200)+100*items.length+1010
  scalarPeak : res.scalars.peak ≤ max (max Sinit.scalars.peak Sinit.peak)
    ((callerP caller).length+12-caller.scalars.baseMemory+40)
  outerPeak : res.peak ≤ max caller.peak (max (max Sinit.scalars.peak Sinit.peak)
      ((callerP caller).length+12-caller.scalars.baseMemory+40) +
    max caller.frame.state.storage.peak
      (caller.frame.state.liveSpace+Proofs.BitWidthU64.width K.toNat+items.length*Proofs.BitWidthU64.width K.toNat+3))

def mkFixed (caller Sinit : NState) (V vsc : Nat) (K : Int) (items : List Int) (vbuf : Buffer Value) : Fixed :=
  ⟨callerP caller,caller.scalars.baseMemory,K,items.length,Proofs.BitWidthU64.width K.toNat,V,vsc,
    caller.frame.state.storage.objects.length,caller.scope+1,
    caller.frame.rootWritable ++ [true] ++ List.replicate (Proofs.BitWidthU64.width K.toNat) false,items,vbuf,
    max (max Sinit.scalars.peak Sinit.peak) ((callerP caller).length+12-caller.scalars.baseMemory+40),
    max Sinit.frame.state.storage.peak
      (caller.frame.state.liveSpace+Proofs.BitWidthU64.width K.toNat+items.length*Proofs.BitWidthU64.width K.toNat+3)⟩

theorem doubling_correct (caller : NState) {vslot vb V vsc : Nat} {wV m : Bool} {vbuf : Buffer Value}
    (ok : CallerOK caller vslot vb V vsc wV m vbuf) (items : List Int)
    (hv : vbuf.items = items.map Value.integer) (hn : items.length < 2147483648)
    (hvalid : ∀ x ∈ items, 0 ≤ x ∧ x < items.length) (kexpr : NExpr) (K : Int) (hs : kexpr.scalarOnly = true)
    (ty : kexpr.resultType = u64) (value : kexpr.denote (envOf caller) = some K) (hK0 : 0 < K) (hK : K < 2^64) :
    ∃ Sinit fuel res, prepare caller DoublingNestedInstance.doubling.parameters
        [.vectorReference vslot,.value kexpr] = some Sinit ∧
      DoublingNestedInstance.doubling.callFuel fuel caller [.vectorReference vslot,.value kexpr] =
        .finished (res,.vector caller.frame.state.storage.objects.length (.vector atom)) ∧
      DoublingPost caller Sinit res kexpr.nodes items V vbuf K := by
  have kv : u64.valid K = true := by simp [Ty.valid]; omega
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prepare_doubling caller ok kexpr K hs ty value kv
  have sState : Sinit.frame.state = caller.frame.state := by rw [sFrame]
  have sRw : Sinit.frame.rootWritable = caller.frame.rootWritable := by rw [sFrame]
  have sFb : Sinit.frame.bindings = [vbind V vsc] := by rw [sFrame]
  let F := mkFixed caller Sinit V vsc K items vbuf
  have wb := Proofs.BitWidthU64.width_bound K.toNat (by omega)
  have bound : V < caller.frame.state.storage.objects.length :=
    CppVectorStore.lookup_bound caller.frame.state.storage V vbuf ok.vfound
  have fok : FixedOK F := by
    refine ⟨rfl,hvalid,hn,?_,bound,?_,?_⟩
    · show Proofs.BitWidthU64.width K.toNat < 2147483648
      omega
    · show caller.scalars.baseMemory ≤ (callerP caller).length
      have := ok.base
      simp [callerP]; omega
    · show (callerP caller).length+12-caller.scalars.baseMemory+40 ≤ max (max Sinit.scalars.peak Sinit.peak)
        ((callerP caller).length+12-caller.scalars.baseMemory+40)
      exact Nat.le_max_right _ _
  have hw1 : 1 ≤ F.w := by
    show 1 ≤ Proofs.BitWidthU64.width K.toNat
    have : K.toNat ≠ 0 := by omega
    simp [Proofs.BitWidthU64.width,this]
  have hvn : F.vbuf.items.length = F.n := by
    show vbuf.items.length = items.length
    rw [hv]; simp
  have hrw : F.rw = caller.frame.rootWritable ++ [true] ++ List.replicate F.w false := rfl
  have ps : PS F F.sc caller.frame.rootWritable Sinit [⟨u64,F.K⟩] [⟨F.P.length,true⟩] entrySlots :=
    ⟨sSlots,sMem,sBind,sBase,sScope,by rw [sFb]; rfl,sRw⟩
  have vf : VF F caller.frame.state.liveSpace caller.frame.state.storage.work Sinit.frame :=
    ⟨by rw [sState]; exact ok.valid,by rw [sState]; exact ok.vtag,by rw [sState]; exact ok.vfound,
     by rw [sState,sRw]; exact ok.lengths,⟨m,by rw [sRw]; exact ok.flag⟩,
     fun owner c h => by
       rw [sState] at h
       have := ok.strict owner c h
       show c < caller.scope+1
       omega,
     by rw [sState],by rw [sState],by rw [sState]; rfl⟩
  have cb : Cb F Sinit.scalars.work Sinit :=
    ⟨Nat.le_refl _,Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _),Nat.le_max_left _ _,
      Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) (Nat.le_add_right _ _)⟩
  have run := body_run F fok hv Sinit hrw hw1 rfl hK0 hK hvn (Nat.le_max_right _ _) ps vf cb
  obtain ⟨fuel,step,hrun,ret,brk,D,stepEq,done⟩ := run
  have fin := finish_doubling caller D done (hP := rfl) (hscope := rfl)
  refine ⟨Sinit,fuel,finishResult caller D (D.frame.state.forest.transferred F.R caller.scope (rootTag i32 F.sc F.R F.w)),hprep,?_,?_⟩
  · have hr : step.returned = some (.vector caller.frame.state.storage.objects.length (.vector atom)) := ret
    unfold NProgram.callFuel
    simp only [hprep,Proofs.CppLoop.liftChecked,Proofs.CppLoop.Outcome.bind]
    have hrun' : runFuel fuel DoublingNestedInstance.doubling.body Sinit = .finished step := hrun
    have res : DoublingNestedInstance.doubling.result = ResultKind.vector (.vector (.integer i32)) := rfl
    have fin' : finish caller (D.charge 1 0) (.vector (.vector (.integer i32)))
        (some (.vector caller.frame.state.storage.objects.length (.vector atom))) =
        some (finishResult caller D (D.frame.state.forest.transferred F.R caller.scope (rootTag i32 F.sc F.R F.w)),
          .vector caller.frame.state.storage.objects.length (.vector atom)) := fin
    simp only [Bind.bind,Proofs.CppLoop.Outcome.bind,hrun',brk,res,stepEq,hr,fin']
    simp
  · have same := noopRetired_same (movedFrame D.frame
      (D.frame.state.forest.transferred F.R caller.scope (rootTag i32 F.sc F.R F.w)))
    have hl : ∀ o, (finishResult caller D (D.frame.state.forest.transferred F.R caller.scope
        (rootTag i32 F.sc F.R F.w))).frame.state.storage.lookup o = D.frame.state.storage.lookup o :=
      fun o => same.lookup o
    have stP : (finishResult caller D (D.frame.state.forest.transferred F.R caller.scope
        (rootTag i32 F.sc F.R F.w))).frame.state.storage.peak ≤ max caller.frame.state.storage.peak
        (caller.frame.state.liveSpace+Proofs.BitWidthU64.width K.toNat+items.length*Proofs.BitWidthU64.width K.toNat+3) := by
      have a := done.storagePeak
      have b := done.live
      have ml := moved_live D done caller.scope
      show max D.frame.state.storage.peak ((movedFrame D.frame (D.frame.state.forest.transferred F.R caller.scope
        (rootTag i32 F.sc F.R F.w))).state.liveSpace-D.frame.state.storage.baseSpace) ≤ _
      rw [ml]
      have hs : Sinit.frame.state.storage.peak = caller.frame.state.storage.peak := by rw [sState]
      have hT : F.TPB = max Sinit.frame.state.storage.peak (caller.frame.state.liveSpace +
          Proofs.BitWidthU64.width K.toNat+items.length*Proofs.BitWidthU64.width K.toNat+3) := rfl
      rw [hT,hs] at a
      rw [b]
      have e1 : F.w = Proofs.BitWidthU64.width K.toNat := rfl
      have e2 : F.n = items.length := rfl
      try simp only [e1,e2] at a
      try simp only [e1,e2]
      omega
    have hs : Sinit.frame.state.storage.peak = caller.frame.state.storage.peak := by rw [sState]
    have hT : F.TPB = max caller.frame.state.storage.peak (caller.frame.state.liveSpace +
        Proofs.BitWidthU64.width K.toNat+items.length*Proofs.BitWidthU64.width K.toNat+3) := by
      show max Sinit.frame.state.storage.peak _ = _
      rw [hs]
    have memD : D.scalars.memory = callerP caller ++ [⟨u64,K⟩,⟨i32,(F.n : Int)⟩,⟨i32,(F.w : Int)⟩,⟨i32,(F.w : Int)⟩] :=
      done.shape.memory
    have lenMem : D.scalars.memory.length = (callerP caller).length+4 := by rw [memD]; simp
    have bindD : D.scalars.bindings.length = 4 := by rw [done.shape.bindings]; simp
    have baseD : D.scalars.baseMemory = caller.scalars.baseMemory := done.shape.base
    have takeLen : (D.scalars.memory.take caller.scalars.memory.length).length = caller.scalars.memory.length := by
      rw [memD]; simp only [callerP,List.append_assoc]; rw [List.take_left]
    have lenP : (callerP caller).length = caller.scalars.memory.length+
        (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
    have spC : caller.scalars.peak ≤ Sinit.scalars.peak := by
      have h1 := charge_scalar_peak caller 1 1
      have h2 := good.2.2.2.2.1
      omega
    have hB := ok.base
    have hSP := done.scalarPeak
    have e0 : F.SPB = max (max Sinit.scalars.peak Sinit.peak) ((callerP caller).length+12-caller.scalars.baseMemory+40) := rfl
    have spP : (finishResult caller D (D.frame.state.forest.transferred F.R caller.scope
        (rootTag i32 F.sc F.R F.w))).scalars.peak ≤ max (max Sinit.scalars.peak Sinit.peak)
        ((callerP caller).length+12-caller.scalars.baseMemory+40) := by
      have resSp : (finishResult caller D (D.frame.state.forest.transferred F.R caller.scope
          (rootTag i32 F.sc F.R F.w))).scalars.peak = max (max caller.scalars.peak (max D.scalars.peak
          (D.scalars.memory.length-D.scalars.baseMemory+D.scalars.bindings.length+0)))
          ((D.scalars.memory.take caller.scalars.memory.length).length-caller.scalars.baseMemory+
            caller.scalars.bindings.length+0) := rfl
      rw [resSp,lenMem,bindD,baseD,takeLen]
      rw [e0] at hSP
      omega
    refine ⟨?_,?_,?_,?_,?_,rfl,rfl,rfl,?_,?_,?_,?_,?_,?_,?_⟩
    · exact same.wellFormed.trans (moved_valid D done caller.scope)
    · rw [hl]; exact done.rows.vFound
    · intro k hk
      obtain ⟨b,found,hitems,hcap,_⟩ := done.rows.complete k hk
      exact ⟨b,by rw [hl]; exact found,hitems,hcap⟩
    · obtain ⟨b,found,_,hitems⟩ := done.ctx.graph.buffer
      exact ⟨b,by rw [hl]; exact found,hitems⟩
    · show (D.frame.state.forest.transferred F.R caller.scope (rootTag i32 F.sc F.R F.w)).context F.R = _
      have rooted : D.frame.state.forest.rootOwner F.R = some F.R :=
        CppVectorOwnership.root_runs _ F.R _ done.ctx.graph.tag rfl
      rw [context_transferred D.frame.state.forest F.R caller.scope _ done.ctx.graph.tag rfl F.R]
      simp [rooted]
    · show D.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory
      have memD : D.scalars.memory = callerP caller ++ [⟨u64,K⟩,⟨i32,(F.n : Int)⟩,⟨i32,(F.w : Int)⟩,⟨i32,(F.w : Int)⟩] :=
        done.shape.memory
      rw [memD]
      simp only [callerP,List.append_assoc]
      exact List.take_left
    · exact done.shape.writable
    · exact done.storageWork
    · exact stP
    · -- scalar work
      have wD := done.scalarWork
      have e1 : F.w = Proofs.BitWidthU64.width K.toNat := rfl
      have e2 : F.n = items.length := rfl
      have gw := good.2.2.1
      have cw : (caller.charge 1 1).scalars.work = caller.scalars.work+1 := rfl
      have rw' : (finishResult caller D (D.frame.state.forest.transferred F.R caller.scope (rootTag i32 F.sc F.R F.w))).scalars.work
          = D.scalars.work+1+1 := rfl
      rw [rw']
      rw [e1,e2] at wD
      rw [sWork] at wD
      omega
    · exact spP
    · have resPeak : (finishResult caller D (D.frame.state.forest.transferred F.R caller.scope
          (rootTag i32 F.sc F.R F.w))).peak = max (max caller.peak (D.charge 1 0).peak)
          ((finishResult caller D (D.frame.state.forest.transferred F.R caller.scope
            (rootTag i32 F.sc F.R F.w))).scalars.peak +
           (finishResult caller D (D.frame.state.forest.transferred F.R caller.scope
            (rootTag i32 F.sc F.R F.w))).frame.state.storage.peak) := rfl
      have chP := charge_peak D 1 0
      have ho := done.outerPeak
      have hst := done.storagePeak
      rw [e0] at ho hSP
      rw [hT] at hst
      rw [resPeak,chP]
      omega

end Proofs.DoublingCall
