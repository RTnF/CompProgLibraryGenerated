namespace GenericSumSetApplyRaw
open Proofs
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.StraightLine Proofs.ScalarStraight Proofs.IntSim Proofs.ModIntCall
open Proofs.ModIntExec Proofs.PowModStep Proofs.PexecKit Proofs.QuotientSearch
open Proofs.ExtremaCall
open Proofs.CppState (Cell)

open Proofs.GroupCall


open Proofs.MonoidLazyCall Proofs.MonoidCall


open Proofs.CppScalarValuePrepare
open Proofs.Mod61Body

abbrev i32 : Ty := ⟨32,true,false⟩
abbrev bl : Ty := ⟨1,false,true⟩
abbrev cn (n : Int) : Cell := ⟨i32,n⟩
abbrev cx (ty : Ty) (x : Int) : Cell := ⟨ty,x⟩
abbrev cf (f : Int) : Cell := ⟨bl,f⟩
variable (ty : Ty)
def refs (a b : Nat) : List CppState.Binding := [⟨a,true⟩,⟨b,true⟩]
def selected (f x q : Int) : Int := if f=0 then q else x
def product : NExpr := .binary ty .mul (.variable ty 0) (Proofs.GenericLazy.castTo ty i32 (.variable i32 3))
def condition : NExpr := .unary bl .not (.variable bl 1)
def arm : Command := .sequence (.scope (.sequence (.primitive (.assign 2 ty (product ty))) Sk)) Sk
def update : Command := .branch condition (arm ty) Sk
def tailBody : Command := .sequence (.primitive (.declare ty true (.variable ty 2)))
  (.sequence (.primitive (.declare i32 true (.variable i32 3))) Sk)
def rawBody : Command := .sequence (update ty) (tailBody ty)


theorem update_exec (P : List Cell) (a b : Nat) (v f x n : Int)
    (receiver : P[a]? = some (cx ty v)) (flag : P[b]? = some (cf f))
    (hv : ty.valid v = true) (hf : bl.valid f = true)
    (hx : ty.valid x = true) (hn : i32.valid n = true) (hnt : ty.valid n = true)
    (q : Int) (hcm : f=0 → ty.convert (v*n) = some q) :
    ∃ r, pexec 1 (update ty) (ws P (refs a b) [cx ty x,cn n]) = some r ∧
      r.ret = none ∧ r.cost ≤ (if f=0 then 9 else 3) ∧ r.need ≤ P.length+12 ∧
      r.ps = ws P (refs a b) [cx ty (selected f x q),cn n] := by
  let R := refs a b
  let L : List Cell := [cx ty x,cn n]
  have readf : (NExpr.variable bl 1).denote (penv (ws P R L)) = some f := by
    rw [den_variable]
    exact ws_env_ref P R L 1 b true bl f rfl flag hf
  by_cases zero : f=0
  · have readv : (NExpr.variable ty 0).denote (penv (ws P R L)) = some v := by
      rw [den_variable]
      exact ws_env_ref P R L 0 a true ty v rfl receiver hv
    have readn : (NExpr.variable i32 3).denote (penv (ws P R L)) = some n := by
      rw [den_variable]
      exact ws_env_loc P R L 1 (cn n) i32 rfl rfl hn
    have mul : (product ty).denote (penv (ws P R L)) = some q := by
      rw [product,den_binary,readv,Proofs.GenericLazy.castTo_den ty i32 (.variable i32 3) _ n (by rw [den_variable]; exact readn) hnt]
      simpa [binaryValue] using hcm zero
    have cond : condition.denote (penv (ws P R L)) = some 1 := by
      change ((penv (ws P R L) 1 bl).bind fun value => bl.convert (unaryValue .not value)) = _
      have envf : penv (ws P R L) 1 bl = some f := readf
      rw [envf]
      simp [zero,unaryValue,Ty.convert]
    have st := pstmt_assign_ok (ws P R L) 2 ty (product ty) q mul ⟨P.length,true⟩ (cx ty x)
      (by simp [ws,R,refs,L,List.range_succ]) (by simp [ws,L,cx]) rfl hx rfl q
      (Proofs.GenericCall.convG ty q (Proofs.GenericCall.convert_valid ty _ _ (hcm zero)))
    have br := pexec_braced 1 (.assign 2 ty (product ty)) (ws P R L) _ st rfl
      (by simp) rfl
    have run := pexec_branch_true 1 condition (arm ty) Sk (ws P R L) 1 cond (by decide) _ br
    have hn' := Proofs.GenericLazy.castTo_nodes ty i32 (.variable i32 3)
    simp only [NExpr.nodes] at hn'
    refine ⟨_,run,rfl,?_,?_,?_⟩
    · simp [condition,product,NExpr.nodes,zero] <;> omega
    · simp [ws,R,refs,L,condition,product,NExpr.nodes] <;> omega
    · simp [ws,R,refs,L,selected,zero,cx,cn,List.range_succ]
  · have cond : condition.denote (penv (ws P R L)) = some 0 := by
      change ((penv (ws P R L) 1 bl).bind fun value => bl.convert (unaryValue .not value)) = _
      have envf : penv (ws P R L) 1 bl = some f := readf
      rw [envf]
      simp [zero,unaryValue,Ty.convert]
    have run := pexec_branch_false 1 condition (arm ty) Sk (ws P R L) cond _ (pexec_skip 1 _)
    refine ⟨_,run,rfl,?_,?_,?_⟩
    · simp [condition,NExpr.nodes,zero]
    · simp [ws,R,refs,L,condition,NExpr.nodes] <;> omega
    · simp [selected,zero,R,L]

theorem raw_exec (P : List Cell) (a b : Nat) (v f x n : Int)
    (receiver : P[a]? = some (cx ty v)) (flag : P[b]? = some (cf f))
    (hv : ty.valid v = true) (hf : bl.valid f = true)
    (hx : ty.valid x = true) (hn : i32.valid n = true) (hnt : ty.valid n = true)
    (q : Int) (hcm : f=0 → ty.convert (v*n) = some q) :
    ∃ r, pexec 1 (rawBody ty) (ws P (refs a b) [cx ty x,cn n]) = some r ∧
      r.ret = none ∧ r.cost ≤ (if f=0 then 13 else 7) ∧ r.need ≤ P.length+13 ∧
      r.ps = ws P (refs a b) [cx ty (selected f x q),cn n,cx ty (selected f x q),cn n] := by
  let R := refs a b
  let y := selected f x q
  let L2 : List Cell := [cx ty y,cn n]
  let L3 : List Cell := L2 ++ [cx ty y]
  let L4 : List Cell := L3 ++ [cn n]
  have hy : ty.valid y = true := by unfold y selected; split; exact Proofs.GenericCall.convert_valid ty _ _ (hcm ‹f=0›); exact hx
  obtain ⟨u,qu,ru,cu,nu,pu⟩ := update_exec ty P a b v f x n receiver flag hv hf hx hn hnt q hcm
  have readx : (NExpr.variable ty 2).denote (penv (ws P R L2)) = some y := by
    rw [den_variable]
    exact ws_env_loc P R L2 0 (cx ty y) ty rfl rfl hy
  have readn : (NExpr.variable i32 3).denote (penv (ws P R L3)) = some n := by
    rw [den_variable]
    exact ws_env_loc P R L3 1 (cn n) i32 rfl rfl hn
  have q0 := (pexec_prim 1 _ _).trans (ws_declare P R L2 ty (.variable ty 2) y readx (Ty.convert_of_valid _ _ hy))
  have q1 := (pexec_prim 1 _ _).trans (ws_declare P R L3 i32 (.variable i32 3) n readn (Ty.convert_of_valid _ _ hn))
  have tail := seq_some q0 rfl (seq_some q1 rfl (pexec_skip 1 _))
  have qt : pexec 1 (tailBody ty) u.ps = some ⟨ws P R L4,none,4,P.length+13⟩ := by
    rw [pu]
    simpa [tailBody,ws,R,refs,L2,L3,L4,NExpr.nodes,Nat.add_assoc] using tail
  have run := seq_some qu ru qt
  refine ⟨⟨ws P R L4,none,u.cost+4,max u.need (P.length+13)⟩,?_,rfl,?_,?_,rfl⟩
  · simpa [rawBody] using run
  · by_cases h : f = 0 <;> simp [h] at cu ⊢ <;> omega
  · simp only [Nat.max_le]; constructor; exact Nat.le_trans nu (by omega); exact Nat.le_refl _
end GenericSumSetApplyRaw

namespace GenericSumSetApplyCall
open Proofs
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.StraightLine Proofs.ScalarStraight Proofs.IntSim Proofs.ModIntCall
open Proofs.ModIntExec Proofs.PowModStep Proofs.PexecKit Proofs.QuotientSearch
open Proofs.ExtremaCall
open Proofs.CppState (Cell)

open Proofs.GroupCall


open Proofs.MonoidLazyCall Proofs.MonoidCall


open OriginalMemberResult
open GenericSumSetApplyRaw
open MemberPrepareGeneral
open Proofs.CppScalarValuePrepare
open Proofs.Mod61Body

abbrev i32 : Ty := ⟨32,true,false⟩

abbrev bl : Ty := ⟨1,false,true⟩
def gSumApply (ty : Ty) : NProgram :=
  ⟨[.scalar ty true true, .scalar bl true true, .scalar ty false true, .scalar i32 false true], .unit, GenericSumSetApplyRaw.rawBody ty⟩
def gApplyFields (ty : Ty) : List Proofs.CppConstructorFinish.ScalarField := [⟨4,ty⟩,⟨5,i32⟩]
def gPerm (ty : Ty) (targetConst : Bool) : List (Proofs.CppScalar.Ty × Bool) :=
  [(ty,(true && (!targetConst || false))),(i32,(true && (!targetConst || false)))]
def gApplyView (ty : Ty) (fuel : Nat) (caller : NState) (arguments : List NArgument) (targetConst : Bool) :
    Proofs.CppLoop.Outcome (NState × Proofs.CppConstructorMultiFinish.ObjectRef) :=
  MemberView.constructViewFuel (gSumApply ty) fuel caller arguments [] (gApplyFields ty)
    (vectorPermissions targetConst) (gPerm ty targetConst)
def gApplyObjects (ty : Ty) (fuel : Nat) (caller : NState)
    (objects : List Proofs.CppConstructorMultiFinish.ObjectRef) (targetConst : Bool) :
    Proofs.CppLoop.Outcome (NState × Proofs.CppConstructorMultiFinish.ObjectRef) :=
  match MemberFactory.objectArguments caller [(false,[(ty,true),(bl,true)]),(true,[(ty,true),(i32,true)])] objects with
  | none => .fault
  | some args => gApplyView ty fuel caller args targetConst

variable {ty : Ty}
abbrev cn (n : Int) : Cell := ⟨i32,n⟩

theorem caller_cell (caller : NState) (slot : Nat) (ty : Ty) (binding : CppState.Binding) (v : Int)
    (found : caller.scalarCell slot ty = some (binding,⟨ty,v⟩)) :
    (callerP caller)[binding.address]? = some ⟨ty,v⟩ ∧ ty.valid v = true := by
  obtain ⟨index,sl,bs,mem,ht,hv⟩ := scalarCell_facts found
  refine ⟨?_,hv⟩
  simp only [callerP,List.getElem?_append_left (List.getElem?_eq_some_iff.mp mem).1]
  exact mem

def scalarBound (caller initial : NState) : Nat :=
  max (max initial.scalars.peak initial.peak) ((callerP caller).length+20-caller.scalars.baseMemory+100)
def storageBound (caller : NState) : Nat :=
  max caller.frame.state.storage.peak caller.frame.state.liveSpace

def fieldBindings (P : List Cell) : List CppState.Binding :=
  (List.range 4).map fun i => ⟨P.length+i,true⟩
def fields (ty : Ty) (x n : Int) : List Cell := [cx ty x,cn n,cx ty x,cn n]
structure StageState (ty : Ty) (caller initial callee : NState) (a b : Nat) (x n : Int) : Prop where
  scalar : QS callee [] caller.scalars.baseMemory (caller.scope+1)
    (callerP caller ++ fields ty x n) (refs a b ++ fieldBindings (callerP caller)) (ssl 6)
  frame : FA callee.frame caller.frame.state.liveSpace caller.frame.state.storage.work
    (caller.scope+1) caller.frame.state.storage.objects.length
  counters : Cq (scalarBound caller initial) (storageBound caller) (caller.scalars.work+22) callee
  contents : CppScalarContents.Contents caller.frame callee.frame
  xValid : ty.valid x = true
  nValid : i32.valid n = true

theorem stage_ready (caller : NState) (receiverSlot flagSlot : Nat) (binding flagBinding : CppState.Binding) (v f x n : Int)
    (found : caller.scalarCell receiverSlot ty = some (binding,cx ty v))
    (writable : binding.writable = true)
    (flagFound : caller.scalarCell flagSlot bl = some (flagBinding,⟨bl,f⟩))
    (flagWritable : flagBinding.writable = true)
    (hx : ty.valid x = true) (hn : i32.valid n = true) (hnt : ty.valid n = true)
    (q : Int) (hcm : f=0 → ty.convert (v*n) = some q)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel callee, prepare caller (gSumApply ty).parameters
        [.scalarReference receiverSlot,.scalarReference flagSlot,.value (.literal ty x),.value (.literal i32 n)] = some initial ∧
      runFuel fuel (gSumApply ty).body initial = .finished ⟨callee,none,false⟩ ∧
      StageState ty caller initial callee binding.address flagBinding.address (selected f x q) n := by
  obtain ⟨initial,prepared,slots,mem,bindings,bas,scope,frame,work,peak⟩ :=
    prepare_references2_values2 caller (gSumApply ty).parameters ty bl ty i32 rfl
      receiverSlot flagSlot binding flagBinding v f x n found writable flagFound flagWritable hx hn valid
  obtain ⟨receiver,hv⟩ := caller_cell caller receiverSlot ty binding v found
  obtain ⟨flag,hf⟩ := caller_cell caller flagSlot bl flagBinding f flagFound
  have hy : ty.valid (selected f x q) = true := by unfold selected; split; exact Proofs.GenericCall.convert_valid ty _ _ (hcm ‹f=0›); exact hx
  obtain ⟨r,ran,ret,cost,need,ps⟩ := GenericSumSetApplyRaw.raw_exec ty (callerP caller) binding.address flagBinding.address v f x n receiver flag hv hf hx hn hnt q hcm
  have qs : QS initial [] caller.scalars.baseMemory (caller.scope+1)
      (ws (callerP caller) (refs binding.address flagBinding.address) [cx ty x,cn n]).mem
      (ws (callerP caller) (refs binding.address flagBinding.address) [cx ty x,cn n]).bs (ssl 4) := by
    refine ⟨by simpa [ssl] using slots,?_,?_,bas,scope⟩
    · simpa [ws] using mem
    · simpa [ws,refs,List.range_succ] using bindings
  have fa : FA initial.frame caller.frame.state.liveSpace caller.frame.state.storage.work
      (caller.scope+1) caller.frame.state.storage.objects.length := by
    refine ⟨by rw [frame]; exact valid,by rw [frame]; exact lengths,by rw [frame],by rw [frame],?_,by rw [frame],by rw [frame]⟩
    intro owner c h
    rw [frame] at h
    have := strict owner c h
    omega
  have cq : Cq (scalarBound caller initial) (storageBound caller) initial.scalars.work initial := by
    refine ⟨Nat.le_refl _,?_,?_,?_⟩
    · change initial.scalars.peak ≤ scalarBound caller initial
      unfold scalarBound; omega
    · change initial.frame.state.storage.peak ≤ storageBound caller
      rw [frame]; exact Nat.le_max_left _ _
    · change initial.peak ≤ scalarBound caller initial+storageBound caller
      unfold scalarBound; omega
  have hbase : caller.scalars.baseMemory ≤ (ws (callerP caller) (refs binding.address flagBinding.address) [cx ty x,cn n]).mem.length := by
    simp [ws,callerP]; omega
  have run := sound (gSumApply ty).body (by simp [gSumApply, GenericSumSetApplyRaw.rawBody, GenericSumSetApplyRaw.update, GenericSumSetApplyRaw.arm, GenericSumSetApplyRaw.condition, GenericSumSetApplyRaw.product, GenericSumSetApplyRaw.tailBody, Proofs.GenericLazy.castTo_scalar ty i32 (.variable i32 3) rfl, Scalar, NExpr.scalarOnly]) 1 _ r ran
    (L0:=caller.frame.state.liveSpace) (T0:=caller.frame.state.storage.work)
    (N:=caller.frame.state.storage.objects.length) (scq:=caller.scope+1)
    (SPB:=scalarBound caller initial) (TPB:=storageBound caller) (W:=initial.scalars.work)
    initial qs fa cq hbase
    (by simp [ws,refs]; unfold scalarBound; omega)
    (by unfold scalarBound; omega)
    (Nat.le_refl _) (by exact Nat.le_max_right _ _)
  obtain ⟨fuel,step,executed,returned,breaking,qsD,faD,cqD⟩ := run
  have typed : StageState ty caller initial step.state binding.address flagBinding.address (selected f x q) n := by
    refine ⟨?_,faD,?_,?_,hy,hn⟩
    · rw [ps] at qsD
      simpa [ws,fields,fieldBindings,ssl,refs] using qsD
    · refine ⟨?_,cqD.scalarPeak,cqD.storagePeak,cqD.outerPeak⟩
      have bound := cqD.work
      rw [work] at bound
      split at cost <;> omega
    · have stable := CppScalarContents.run_stable fuel (gSumApply ty).body initial step
        (by simp [gSumApply, GenericSumSetApplyRaw.rawBody, GenericSumSetApplyRaw.update, GenericSumSetApplyRaw.arm, GenericSumSetApplyRaw.condition, GenericSumSetApplyRaw.product, GenericSumSetApplyRaw.tailBody, CppScalarContents.Allowed, Proofs.CppScalarFrame.Scalar]) (by intro owner c found; rw [frame] at found; have h := strict owner c found; rw [scope]; omega) executed
      have initialContents : CppScalarContents.Contents caller.frame initial.frame := by
        rw [frame]; exact ⟨rfl,rfl,rfl,rfl⟩
      exact initialContents.trans stable.contents
  refine ⟨initial,fuel,step.state,prepared,?_,typed⟩
  have stepEq : step = ⟨step.state,none,false⟩ := by
    cases step
    simp only [ret,Option.map_none] at returned
    simp_all
  exact executed.trans (congrArg (fun q : NStep => Proofs.CppLoop.Outcome.finished q) stepEq)
def destinationValues (ty : Ty) (x n : Int) (targetConst : Bool) : List Proofs.CppConstructorFinish.ScalarValue :=
  [((cx ty x),!targetConst),((cn n),!targetConst)]
def exported (ty : Ty) (x n : Int) (caller callee : NState) (targetConst : Bool) : NState :=
  Proofs.CppConstructorMultiFinish.restored caller callee (Proofs.CppNestedScope.noopRetired callee.frame)
    [] (destinationValues ty x n targetConst)

structure ExportState (ty : Ty) (x n : Int) (caller initial out : NState) (targetConst : Bool) : Prop where
  valid : out.frame.state.wellFormed = true
  memory : out.scalars.memory = caller.scalars.memory ++ [(cx ty x),(cn n)]
  bindings : out.scalars.bindings = caller.scalars.bindings ++
    [⟨caller.scalars.memory.length,!targetConst⟩,⟨caller.scalars.memory.length+1,!targetConst⟩]
  slots : out.slots = caller.slots ++ Proofs.CppConstructorFinish.scalarLocations caller.scalars.bindings.length 2
  scope : out.scope = caller.scope
  frameBindings : out.frame.bindings = caller.frame.bindings
  objects : out.frame.state.storage.objects.length = caller.frame.state.storage.objects.length
  live : out.frame.state.liveSpace = caller.frame.state.liveSpace
  scalarWork : out.scalars.work ≤ caller.scalars.work+25
  storageWork : out.frame.state.storage.work = caller.frame.state.storage.work
  scalarPeak : out.scalars.peak ≤ max caller.scalars.peak (scalarBound caller initial)
  storagePeak : out.frame.state.storage.peak ≤ storageBound caller
  outerPeak : out.peak ≤ max caller.peak
    (max caller.scalars.peak (scalarBound caller initial)+storageBound caller)
  contents : CppScalarContents.Contents caller.frame out.frame
  xValid : ty.valid x = true
  nValid : i32.valid n = true

theorem finish_export (x n : Int) (a b : Nat) (caller initial callee : NState) (targetConst : Bool)
    (ready : StageState ty caller initial callee a b x n)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    MemberView.finishView caller callee [] (gApplyFields ty)
        [] (gPerm ty targetConst) =
      some (exported ty x n caller callee targetConst,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
    ExportState ty x n caller initial (exported ty x n caller callee targetConst) targetConst := by
  have mem : callee.scalars.memory = callerP caller ++ (fields ty x n) := by simpa using ready.scalar.memory
  have bs := ready.scalar.bindings
  have sl := ready.scalar.slots
  have c4 : callee.scalarCell 4 ty = some (⟨(callerP caller).length+2,true⟩,(cx ty x)) := by
    simp [NState.scalarCell,NState.scalarSlot,mem,bs,sl,fieldBindings,fields,refs,ssl,List.range_succ,cx,ready.xValid]
  have c5 : callee.scalarCell 5 i32 = some (⟨(callerP caller).length+3,true⟩,(cn n)) := by
    simp [NState.scalarCell,NState.scalarSlot,mem,bs,sl,fieldBindings,fields,refs,ssl,List.range_succ,cn,ready.nValid]
  have captured : Proofs.CppConstructorFinish.captureAll callee
      (gApplyFields ty) = some [((cx ty x),true),((cn n),true)] := by
    change Proofs.CppConstructorFinish.captureAll callee [⟨4,ty⟩,⟨5,i32⟩] = _
    simp [Proofs.CppConstructorFinish.captureAll,Proofs.CppConstructorFinish.capture,c4,c5]
  have viewed : Proofs.CppConstructorView.restrictValues [((cx ty x),true),((cn n),true)] (gPerm ty targetConst) =
      some (destinationValues ty x n targetConst) := by cases targetConst <;> simp [Proofs.CppConstructorView.restrictValues, gPerm, destinationValues, cx, cn]
  have takeM : callee.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [mem]; exact Proofs.MonoidCallCore.take_P caller (fields ty x n)
  have fits : caller.scalars.memory.length ≤ callee.scalars.memory.length := by
    rw [mem]; simp [callerP]
  have fresh : ∀ owner, callee.frame.state.forest.context owner ≠ some callee.scope := by
    intro owner h
    have bound := ready.frame.strict owner _ h
    rw [ready.scalar.scope] at bound
    omega
  have retired := retireScope_fresh callee.frame callee.scope ready.frame.valid fresh
  have finished : MemberView.finishView caller callee [] (gApplyFields ty)
      [] (gPerm ty targetConst) =
        some (exported ty x n caller callee targetConst,Proofs.CppConstructorMultiFinish.reference caller 0 2) := by
    unfold MemberView.finishView
    split
    · simp only [Proofs.CppConstructorMultiFinish.captureVectors,List.mapM_nil,captured,Bind.bind,Option.bind]
      rw [viewed]
      simp [Bind.bind,Option.bind,MemberView.restrictVectors,Proofs.CppConstructorRoots.finishRoots,
        Proofs.CppConstructorRoots.transferAll,Proofs.CppConstructorMultiFinish.descriptors,retired,
        exported,destinationValues]
    · rename_i failed
      exact (failed ⟨ready.scalar.scope,fits,by rw [takeM]⟩).elim
  refine ⟨finished,?_⟩
  have work := ready.counters.work
  have peak := ready.counters.scalarPeak
  have storagePeak := ready.counters.storagePeak
  have outerPeak := ready.counters.outerPeak
  change callee.scalars.peak ≤ scalarBound caller initial at peak
  change callee.frame.state.storage.peak ≤ storageBound caller at storagePeak
  change callee.peak ≤ scalarBound caller initial+storageBound caller at outerPeak
  have live := ready.frame.live
  have liveBound : caller.scalars.memory.length+2-caller.scalars.baseMemory+
      (caller.scalars.bindings.length+2) ≤ scalarBound caller initial := by
    unfold scalarBound
    have Psize : (callerP caller).length = caller.scalars.memory.length+
        (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
    omega
  have sp : (exported ty x n caller callee targetConst).scalars.peak ≤
      max caller.scalars.peak (scalarBound caller initial) := by
    simp only [exported,Proofs.CppConstructorMultiFinish.restored,NState.observe,CppState.State.observe]
    simp only [takeM,destinationValues,List.map_cons,List.map_nil,List.length_append,List.length_cons,List.length_nil,
      Proofs.CppConstructorFinish.scalarBindings]
    change max (max caller.scalars.peak callee.scalars.peak)
      (caller.scalars.memory.length+2-caller.scalars.baseMemory+(caller.scalars.bindings.length+2)+0) ≤ _
    omega
  have tp : (exported ty x n caller callee targetConst).frame.state.storage.peak ≤ storageBound caller := by
    change max callee.frame.state.storage.peak (callee.frame.state.liveSpace-callee.frame.state.storage.baseSpace) ≤ storageBound caller
    rw [live]
    unfold storageBound at *
    omega
  refine ⟨?_,?_,?_,?_,rfl,?_,?_,?_,?_,?_,sp,tp,?_,?_,ready.xValid,ready.nValid⟩
  · change callee.frame.state.wellFormed = true
    exact ready.frame.valid
  · simp [exported,Proofs.CppConstructorMultiFinish.restored,NState.observe,CppState.State.observe,takeM,destinationValues]
  · simp [exported,Proofs.CppConstructorMultiFinish.restored,NState.observe,CppState.State.observe,
      destinationValues,Proofs.CppConstructorFinish.scalarBindings]
  · simp [exported,Proofs.CppConstructorMultiFinish.restored,NState.observe,destinationValues,
      Proofs.CppConstructorMultiFinish.vectorLocations,Proofs.CppConstructorFinish.scalarLocations]
  · simp [exported,Proofs.CppConstructorMultiFinish.restored,NState.observe,Proofs.CppConstructorMultiFinish.rebound]
  · change callee.frame.state.storage.objects.length = caller.frame.state.storage.objects.length
    exact ready.frame.count
  · change callee.frame.state.liveSpace = caller.frame.state.liveSpace
    exact live
  · change callee.scalars.work+0+(destinationValues ty x n targetConst).length+1 ≤ caller.scalars.work+25
    simp [destinationValues]
    omega
  · change callee.frame.state.storage.work = caller.frame.state.storage.work
    exact ready.frame.work
  · change max (max caller.peak callee.peak)
      ((exported ty x n caller callee targetConst).scalars.peak+(exported ty x n caller callee targetConst).frame.state.storage.peak) ≤ _
    omega

  · exact ⟨ready.contents.forest,ready.contents.objects,ready.contents.base,ready.contents.flags⟩

theorem existing_scalar_read (x n : Int) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty x n caller initial out targetConst)
    (slot : Nat) (ty : Ty) (binding : CppState.Binding) (cell : Cell)
    (found : caller.scalarCell slot ty = some (binding,cell)) :
    out.scalarCell slot ty = some (binding,cell) := by
  obtain ⟨index,sl,bs,mem,ht,hv⟩ := scalarCell_facts found
  have slo : out.slots[slot]? = some (.scalar index) := by
    rw [post.slots,List.getElem?_append_left (List.getElem?_eq_some_iff.mp sl).1]; exact sl
  have bso : out.scalars.bindings[index]? = some binding := by
    rw [post.bindings,List.getElem?_append_left (List.getElem?_eq_some_iff.mp bs).1]; exact bs
  have mo : out.scalars.memory[binding.address]? = some cell := by
    rw [post.memory,List.getElem?_append_left (List.getElem?_eq_some_iff.mp mem).1]; exact mem
  simp [NState.scalarCell,NState.scalarSlot,slo,bso,mo,ht,hv]

theorem destination_readable (x n : Int) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty x n caller initial out targetConst) :
    out.scalarCell caller.slots.length ty = some (⟨caller.scalars.memory.length,!targetConst⟩,(cx ty x)) ∧
    out.scalarCell (caller.slots.length+1) i32 = some (⟨caller.scalars.memory.length+1,!targetConst⟩,(cn n)) := by
  have s0 : out.slots[caller.slots.length]? = some (.scalar caller.scalars.bindings.length) := by
    rw [post.slots]; simp [Proofs.CppConstructorFinish.scalarLocations]
  have s1 : out.slots[caller.slots.length+1]? = some (.scalar (caller.scalars.bindings.length+1)) := by
    rw [post.slots]; simp [Proofs.CppConstructorFinish.scalarLocations]
  have b0 : out.scalars.bindings[caller.scalars.bindings.length]? = some ⟨caller.scalars.memory.length,!targetConst⟩ := by
    rw [post.bindings]; simp
  have b1 : out.scalars.bindings[caller.scalars.bindings.length+1]? = some ⟨caller.scalars.memory.length+1,!targetConst⟩ := by
    rw [post.bindings]; simp
  have m0 : out.scalars.memory[caller.scalars.memory.length]? = some (cx ty x) := by rw [post.memory]; simp
  have m1 : out.scalars.memory[caller.scalars.memory.length+1]? = some (cn n) := by rw [post.memory]; simp
  constructor
  · simp [NState.scalarCell,NState.scalarSlot,s0,b0,m0,cx,post.xValid]
  · simp [NState.scalarCell,NState.scalarSlot,s1,b1,m1,cn,post.nValid]

theorem frame_extension (x n : Int) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty x n caller initial out targetConst)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length) :
    CppFrameExtension.Extends caller.frame out.frame := by
  refine ⟨valid,post.valid,lengths,?_,?_,?_,?_,?_⟩
  · rw [post.contents.flags,post.contents.forest]; exact lengths
  · intro owner _; rw [post.contents.forest]
  · intro owner _; simp only [CppVectorStore.Store.lookup,post.contents.objects]
  · intro owner _; rw [post.contents.flags]
  · intro slot _; rw [post.frameBindings]

theorem existing_vector_resolve (x n : Int) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty x n caller initial out targetConst)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (slot : Nat) (element : Element) (binding : CppNestedVectorBindings.Binding)
    (buffer : CppVector.Buffer Value)
    (found : caller.frame.resolve slot element = some (binding,buffer)) :
    out.frame.resolve slot element = some (binding,buffer) :=
  CppFrameResolveExtension.resolve_kept caller.frame out.frame
    (frame_extension x n caller initial out targetConst post valid lengths) slot element binding buffer found

theorem existing_vector_read (x n : Int) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty x n caller initial out targetConst)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (reference : CppNestedVectorBindings.Reference) (value : Int)
    (found : caller.frame.read reference = some value) :
    out.frame.read reference = some value :=
  CppFrameExtension.read_kept caller.frame out.frame
    (frame_extension x n caller initial out targetConst post valid lengths) reference value found



theorem view_export_correct (caller : NState) (targetConst : Bool) (receiverSlot flagSlot : Nat) (binding flagBinding : CppState.Binding) (v f x n : Int)
    (found : caller.scalarCell receiverSlot ty = some (binding,cx ty v))
    (writable : binding.writable = true)
    (flagFound : caller.scalarCell flagSlot bl = some (flagBinding,⟨bl,f⟩))
    (flagWritable : flagBinding.writable = true)
    (hx : ty.valid x = true) (hn : i32.valid n = true) (hnt : ty.valid n = true)
    (q : Int) (hcm : f=0 → ty.convert (v*n) = some q)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out, prepare caller (gSumApply ty).parameters
        [.scalarReference receiverSlot,.scalarReference flagSlot,.value (.literal ty x),.value (.literal i32 n)] = some initial ∧
      (gApplyView ty) fuel caller
        [.scalarReference receiverSlot,.scalarReference flagSlot,.value (.literal ty x),.value (.literal i32 n)] targetConst =
          .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
      ExportState ty (selected f x q) n caller initial out targetConst := by
  obtain ⟨initial,fuel,callee,prepared,ran,ready⟩ := stage_ready caller receiverSlot flagSlot binding flagBinding v f x n
    found writable flagFound flagWritable hx hn hnt q hcm valid lengths strict base
  obtain ⟨fin,post⟩ := finish_export (selected f x q) n binding.address flagBinding.address caller initial callee targetConst ready base
  refine ⟨initial,fuel,exported ty (selected f x q) n caller callee targetConst,prepared,?_,post⟩
  exact MemberView.constructView_of_steps (gSumApply ty) fuel caller initial callee _
    [.scalarReference receiverSlot,.scalarReference flagSlot,.value (.literal ty x),.value (.literal i32 n)] []
    (gApplyFields ty) [] (gPerm ty targetConst)
    (Proofs.CppConstructorMultiFinish.reference caller 0 2) none prepared ran (Or.inl rfl) fin

theorem object_export_correct (caller : NState) (targetConst : Bool)
    (receiverSlot flagSlot xSlot nSlot : Nat) (binding flagBinding bx bn : CppState.Binding) (v f x n : Int)
    (found : caller.scalarCell receiverSlot ty = some (binding,cx ty v))
    (writable : binding.writable = true)
    (flagFound : caller.scalarCell flagSlot bl = some (flagBinding,⟨bl,f⟩))
    (flagWritable : flagBinding.writable = true)
    (sourceX : caller.scalarCell xSlot ty = some (bx,cx ty x))
    (sourceN : caller.scalarCell nSlot i32 = some (bn,cn n))
    (hnt : ty.valid n = true) (q : Int) (hcm : f=0 → ty.convert (v*n) = some q)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out,
      prepare caller (gSumApply ty).parameters
        [.scalarReference receiverSlot,.scalarReference flagSlot,.value (.literal ty x),.value (.literal i32 n)] = some initial ∧
      (gApplyObjects ty) fuel caller
        [⟨[],[receiverSlot,flagSlot]⟩,⟨[],[xSlot,nSlot]⟩] targetConst =
          .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
      ExportState ty (selected f x q) n caller initial out targetConst := by
  have hx := (caller_cell caller xSlot ty bx x sourceX).2
  have hn := (caller_cell caller nSlot i32 bn n sourceN).2
  obtain ⟨initial,fuel,out,prepared,ran,post⟩ := view_export_correct caller targetConst receiverSlot flagSlot binding flagBinding v f x n
    found writable flagFound flagWritable hx hn hnt q hcm valid lengths strict base
  have args : MemberFactory.objectArguments caller
      [(false,[(ty,true),(bl,true)]),(true,[(ty,true),(i32,true)])]
      [⟨[],[receiverSlot,flagSlot]⟩,⟨[],[xSlot,nSlot]⟩] =
        some [.scalarReference receiverSlot,.scalarReference flagSlot,.value (.literal ty x),.value (.literal i32 n)] := by
    simp [MemberFactory.objectArguments,MemberFactory.referenceFields,MemberFactory.valueFields,
      found,flagFound,sourceX,sourceN,writable,flagWritable,cx,cn]
  refine ⟨initial,fuel,out,prepared,?_,post⟩
  change (match MemberFactory.objectArguments caller
    [(false,[(ty,true),(bl,true)]),(true,[(ty,true),(i32,true)])]
    [⟨[],[receiverSlot,flagSlot]⟩,⟨[],[xSlot,nSlot]⟩] with
    | none => Proofs.CppLoop.Outcome.fault
    | some arguments => (gApplyView ty) fuel caller arguments targetConst) = _
  rw [args]
  exact ran

/-- A read-only receiver is rejected, for every type and caller. -/
theorem readonly_receiver_rejected (fuel : Nat) (caller : NState) (targetConst : Bool)
    (s1 s2 : Nat) (b : CppState.Binding) (cell : Cell)
    (second : Proofs.CppConstructorMultiFinish.ObjectRef)
    (found : caller.scalarCell s1 ty = some (b,cell)) (readonly : b.writable = false) :
    gApplyObjects ty fuel caller [⟨[],[s1,s2]⟩,second] targetConst = .fault := by
  simp [gApplyObjects, MemberFactory.objectArguments, MemberFactory.referenceFields, found, readonly]

/-- A receiver object that lacks its field slots is rejected. -/
theorem incomplete_receiver_rejected (fuel : Nat) (caller : NState) (targetConst : Bool)
    (second : Proofs.CppConstructorMultiFinish.ObjectRef) :
    gApplyObjects ty fuel caller [⟨[],[]⟩,second] targetConst = .fault := by
  simp [gApplyObjects, MemberFactory.objectArguments, MemberFactory.referenceFields]

/-- A receiver object with a vector slot is rejected. -/
theorem vector_receiver_rejected (fuel : Nat) (caller : NState) (targetConst : Bool)
    (v : Nat) (rest : List Nat) (second : Proofs.CppConstructorMultiFinish.ObjectRef) :
    gApplyObjects ty fuel caller [⟨v :: rest,[]⟩,second] targetConst = .fault := by
  simp [gApplyObjects, MemberFactory.objectArguments]

/-- Omitting the argument object is rejected. -/
theorem missing_argument_object_rejected (fuel : Nat) (caller : NState) (targetConst : Bool)
    (first : Proofs.CppConstructorMultiFinish.ObjectRef) :
    gApplyObjects ty fuel caller [first] targetConst = .fault := by
  unfold gApplyObjects
  simp only [MemberFactory.objectArguments]
  split <;> simp_all

/-- Passing more objects than the member has parameters is rejected. -/
theorem extra_argument_object_rejected (fuel : Nat) (caller : NState) (targetConst : Bool)
    (first second third : Proofs.CppConstructorMultiFinish.ObjectRef)
    (rest : List Proofs.CppConstructorMultiFinish.ObjectRef) :
    gApplyObjects ty fuel caller (first :: second :: third :: rest) targetConst = .fault := by
  unfold gApplyObjects
  simp only [MemberFactory.objectArguments]
  split <;> simp_all

/-- An argument object that lacks its scalar slots is rejected. -/
theorem incomplete_argument_rejected (fuel : Nat) (caller : NState) (targetConst : Bool)
    (first : Proofs.CppConstructorMultiFinish.ObjectRef) :
    gApplyObjects ty fuel caller [first,⟨[],[]⟩] targetConst = .fault := by
  unfold gApplyObjects
  simp only [MemberFactory.objectArguments, MemberFactory.valueFields]
  split <;> simp_all

/-- An argument object with a vector slot is rejected. -/
theorem vector_argument_rejected (fuel : Nat) (caller : NState) (targetConst : Bool)
    (first : Proofs.CppConstructorMultiFinish.ObjectRef) (v : Nat) (rest : List Nat) :
    gApplyObjects ty fuel caller [first,⟨v :: rest,[]⟩] targetConst = .fault := by
  unfold gApplyObjects
  simp only [MemberFactory.objectArguments]
  split <;> simp_all


theorem total_work (x n : Int) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty x n caller initial out targetConst) : out.work ≤ caller.work+25 := by
  have scalar := post.scalarWork
  have storage := post.storageWork
  simp only [NState.work]
  omega

end GenericSumSetApplyCall
