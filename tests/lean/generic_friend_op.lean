namespace GenericFriendReturnRaw
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


open Proofs.Mod61Body

variable (ty : Ty)
def inputs (a b c d : Nat) : List CppState.Binding := [⟨a,false⟩,⟨b,false⟩,⟨c,false⟩,⟨d,false⟩]
def fields (ty : Ty) (x n : Int) : List Cell := [⟨ty,x⟩,⟨i32,n⟩,⟨ty,x⟩,⟨i32,n⟩]
def add64 : NExpr := .binary ty .add (.variable ty 0) (.variable ty 2)
def add32 : NExpr := .binary i32 .add (.variable i32 1) (.variable i32 3)
def rawBody : Command :=
  .sequence (.primitive (.declare ty true (add64 ty)))
    (.sequence (.primitive (.declare i32 true add32))
      (.sequence (.primitive (.declare ty true (.variable ty 4)))
        (.sequence (.primitive (.declare i32 true (.variable i32 5)))
          (.sequence (.scope Sk) Sk))))

theorem add_value (env : Nat → Ty → Option Int) (ty : Ty) (i j : Nat) (x y : Int)
    (left : env i ty = some x) (right : env j ty = some y) (valid : ty.valid (x+y) = true) :
    (NExpr.binary ty .add (.variable ty i) (.variable ty j)).denote env = some (x+y) := by
  rw [den_binary,den_variable,den_variable,left,right]
  simpa [binaryValue] using Ty.convert_of_valid ty (x+y) valid

theorem raw_exec (P : List Cell) (a b c d : Nat) (x n y m : Int)
    (p0 : P[a]? = some ⟨ty,x⟩) (p1 : P[b]? = some ⟨i32,n⟩)
    (p2 : P[c]? = some ⟨ty,y⟩) (p3 : P[d]? = some ⟨i32,m⟩)
    (hx : ty.valid x = true) (hn : i32.valid n = true)
    (hy : ty.valid y = true) (hm : i32.valid m = true)
    (hs : ty.valid (x+y) = true) (ht : i32.valid (n+m) = true) :
    ∃ r, pexec 1 (rawBody ty) ⟨P,inputs a b c d⟩ = some r ∧
      r.ret = none ∧ r.cost ≤ 13 ∧ r.need ≤ P.length+15 ∧
      r.ps = ws P (inputs a b c d) (fields ty (x+y) (n+m)) := by
  let R := inputs a b c d
  let L1 : List Cell := [⟨ty,x+y⟩]
  let L2 : List Cell := [⟨ty,x+y⟩,⟨i32,n+m⟩]
  let L3 : List Cell := [⟨ty,x+y⟩,⟨i32,n+m⟩,⟨ty,x+y⟩]
  let L4 := fields ty (x+y) (n+m)
  have d0 : (add64 ty).denote (penv (ws P R [])) = some (x+y) :=
    add_value _ ty 0 2 x y
      (ws_env_ref P R [] 0 a false ty x rfl p0 hx)
      (ws_env_ref P R [] 2 c false ty y rfl p2 hy) hs
  have d1 : add32.denote (penv (ws P R L1)) = some (n+m) :=
    add_value _ i32 1 3 n m
      (ws_env_ref P R L1 1 b false i32 n rfl p1 hn)
      (ws_env_ref P R L1 3 d false i32 m rfl p3 hm) ht
  have d2 : (NExpr.variable ty 4).denote (penv (ws P R L2)) = some (x+y) := by
    rw [den_variable]
    exact ws_env_loc P R L2 0 ⟨ty,x+y⟩ ty rfl rfl hs
  have d3 : (NExpr.variable i32 5).denote (penv (ws P R L3)) = some (n+m) := by
    rw [den_variable]
    exact ws_env_loc P R L3 1 ⟨i32,n+m⟩ i32 rfl rfl ht
  have q0 := (pexec_prim 1 _ _).trans (ws_declare P R [] ty (add64 ty) (x+y) d0 (Ty.convert_of_valid _ _ hs))
  have q1 := (pexec_prim 1 _ _).trans (ws_declare P R L1 i32 add32 (n+m) d1 (Ty.convert_of_valid _ _ ht))
  have q2 := (pexec_prim 1 _ _).trans (ws_declare P R L2 ty (.variable ty 4) (x+y) d2 (Ty.convert_of_valid _ _ hs))
  have q3 := (pexec_prim 1 _ _).trans (ws_declare P R L3 i32 (.variable i32 5) (n+m) d3 (Ty.convert_of_valid _ _ ht))
  have sc0 := pexec_scope 1 Sk (ws P R L4) _ (pexec_skip 1 _)
  have sc : pexec 1 (.scope Sk) (ws P R L4) = some ⟨ws P R L4,none,1,P.length+12⟩ := by
    simp only [List.take_length] at sc0
    simpa [ws,R,inputs,L4,fields,Nat.add_assoc] using sc0
  have all := seq_some q0 rfl (seq_some q1 rfl (seq_some q2 rfl (seq_some q3 rfl (seq_some sc rfl (pexec_skip 1 _)))))
  refine ⟨⟨ws P R L4,none,13,P.length+15⟩,?_,rfl,Nat.le_refl _,Nat.le_refl _,rfl⟩
  simpa [rawBody,ws,R,inputs,L1,L2,L3,L4,fields,add64,add32,NExpr.nodes,Nat.add_assoc] using all
end GenericFriendReturnRaw

namespace GenericFriendCall
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


open OriginalFriendSumObject
open Proofs.Mod61Body

open OriginalFriendSumObject
open GenericFriendReturnRaw

variable {ty : Ty}

def gOp (ty : Ty) : NProgram :=
  ⟨[.scalar ty true false, .scalar i32 true false, .scalar ty true false, .scalar i32 true false], .unit, GenericFriendReturnRaw.rawBody ty⟩
def gFields (ty : Ty) : List Proofs.CppConstructorFinish.ScalarField := [⟨6,ty⟩,⟨7,i32⟩]
def gPerm (ty : Ty) (targetConst : Bool) : List (Proofs.CppScalar.Ty × Bool) :=
  [(ty,(true && (!targetConst || false))),(i32,(true && (!targetConst || false)))]
def gView (ty : Ty) (fuel : Nat) (caller : NState) (arguments : List NArgument) (targetConst : Bool) :
    Proofs.CppLoop.Outcome (NState × Proofs.CppConstructorMultiFinish.ObjectRef) :=
  MemberView.constructViewFuel (gOp ty) fuel caller arguments [] (gFields ty)
    (vectorPermissions targetConst) (gPerm ty targetConst)
def gObjects (ty : Ty) (fuel : Nat) (caller : NState)
    (objects : List Proofs.CppConstructorMultiFinish.ObjectRef) (targetConst : Bool) :
    Proofs.CppLoop.Outcome (NState × Proofs.CppConstructorMultiFinish.ObjectRef) :=
  match MemberFactory.referenceArguments caller [[(ty,false),(i32,false)],[(ty,false),(i32,false)]] objects with
  | none => .fault
  | some args => gView ty fuel caller args targetConst

theorem prepare_references4 (caller : NState) (params : List CppVectorBindings.Parameter) (t1 t2 t3 t4 : Ty)
    (hp : params = [.scalar t1 true false,.scalar t2 true false,.scalar t3 true false,.scalar t4 true false])
    (s1 s2 s3 s4 : Nat) (b1 b2 b3 b4 : CppState.Binding) (v1 v2 v3 v4 : Int)
    (c1 : caller.scalarCell s1 t1 = some (b1,⟨t1,v1⟩)) (c2 : caller.scalarCell s2 t2 = some (b2,⟨t2,v2⟩))
    (c3 : caller.scalarCell s3 t3 = some (b3,⟨t3,v3⟩)) (c4 : caller.scalarCell s4 t4 = some (b4,⟨t4,v4⟩))
    (valid : caller.frame.state.wellFormed = true) :
    ∃ Sinit, prepare caller params [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] =
        some Sinit ∧
      Sinit.slots = [.scalar 0,.scalar 1,.scalar 2,.scalar 3] ∧ Sinit.scalars.memory = callerP caller ∧
      Sinit.scalars.bindings = [⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩] ∧
      Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
      Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
      Sinit.scalars.work = caller.scalars.work+9 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨i1,_,_,m1,_,w1⟩ := scalarCell_facts c1
  obtain ⟨i2,_,_,m2,_,w2⟩ := scalarCell_facts c2
  obtain ⟨i3,_,_,m3,_,w3⟩ := scalarCell_facts c3
  obtain ⟨i4,_,_,m4,_,w4⟩ := scalarCell_facts c4
  have l1 : b1.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m1).1
  have l2 : b2.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m2).1
  have l3 : b3.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m3).1
  have l4 : b4.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m4).1
  have c2' : (caller.charge 1 1).scalarCell s2 t2 = some (b2,⟨t2,v2⟩) := c2
  have c3' : ((caller.charge 1 1).charge 1 1).scalarCell s3 t3 = some (b3,⟨t3,v3⟩) := c3
  have c4' : (((caller.charge 1 1).charge 1 1).charge 1 1).scalarCell s4 t4 = some (b4,⟨t4,v4⟩) := c4
  have pad : ∀ (t : Ty) (b : CppState.Binding) (v : Int), b.address < caller.scalars.memory.length →
      caller.scalars.memory[b.address]? = some ⟨t,v⟩ →
      (caller.scalars.memory ++ List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
        (⟨bl,0⟩ : Cell))[b.address]? = some ⟨t,v⟩ := by
    intro t b v lt h; rw [List.getElem?_append_left lt]; exact h
  have h1 := pad t1 b1 v1 l1 m1
  have h2 := pad t2 b2 v2 l2 m2
  have h3 := pad t3 b3 v3 l3 m3
  have h4 := pad t4 b4 v4 l4 m4
  rw [hp]
  have wt : (true = true → True) := fun _ => trivial
  simp [prepare,valid,resolveAll,resolve,c1,c2',c3',c4']
  simp [bindAll,bindOne,CppState.bindArgument,callerP,NState.observe,CppState.State.observe,h1,h2,h3,h4,w1,w2,w3,w4]
  simp only [charge_scalar_peak, charge_work]
  refine ⟨trivial, ?_⟩
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  exact Nat.le_max_left _ _

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

structure StageState (ty : Ty) (caller initial callee : NState) (a b c d : Nat) (x n : Int) : Prop where
  scalar : QS callee [] caller.scalars.baseMemory (caller.scope+1)
    (callerP caller ++ fields ty x n) (inputs a b c d ++ fieldBindings (callerP caller)) (ssl 8)
  frame : FA callee.frame caller.frame.state.liveSpace caller.frame.state.storage.work
    (caller.scope+1) caller.frame.state.storage.objects.length
  counters : Cq (scalarBound caller initial) (storageBound caller) (caller.scalars.work+22) callee
  contents : CppScalarContents.Contents caller.frame callee.frame
  xValid : ty.valid x = true
  nValid : i32.valid n = true

theorem stage_ready (caller : NState) (s1 s2 s3 s4 : Nat)
    (b1 b2 b3 b4 : CppState.Binding) (x n y m : Int)
    (c1 : caller.scalarCell s1 ty = some (b1,⟨ty,x⟩)) (c2 : caller.scalarCell s2 i32 = some (b2,⟨i32,n⟩))
    (c3 : caller.scalarCell s3 ty = some (b3,⟨ty,y⟩)) (c4 : caller.scalarCell s4 i32 = some (b4,⟨i32,m⟩))
    (hs : ty.valid (x+y) = true) (ht : i32.valid (n+m) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel callee,
      prepare caller (gOp ty).parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some initial ∧
      runFuel fuel (gOp ty).body initial = .finished ⟨callee,none,false⟩ ∧
      StageState ty caller initial callee b1.address b2.address b3.address b4.address (x+y) (n+m) := by
  obtain ⟨initial,prepared,slots,mem,bindings,bas,scope,frame,work,peak⟩ :=
    prepare_references4 caller (gOp ty).parameters ty i32 ty i32 rfl
      s1 s2 s3 s4 b1 b2 b3 b4 x n y m c1 c2 c3 c4 valid
  obtain ⟨p0,hx⟩ := caller_cell caller s1 ty b1 x c1
  obtain ⟨p1,hn⟩ := caller_cell caller s2 i32 b2 n c2
  obtain ⟨p2,hy⟩ := caller_cell caller s3 ty b3 y c3
  obtain ⟨p3,hm⟩ := caller_cell caller s4 i32 b4 m c4
  obtain ⟨r,ran,ret,cost,need,ps⟩ := raw_exec ty (callerP caller)
    b1.address b2.address b3.address b4.address x n y m p0 p1 p2 p3 hx hn hy hm hs ht
  have qs : QS initial [] caller.scalars.baseMemory (caller.scope+1) (callerP caller)
      (inputs b1.address b2.address b3.address b4.address) (ssl 4) := by
    refine ⟨by simpa [ssl,List.range_succ] using slots,mem,bindings,bas,scope⟩
  have fa : FA initial.frame caller.frame.state.liveSpace caller.frame.state.storage.work
      (caller.scope+1) caller.frame.state.storage.objects.length := by
    refine ⟨by rw [frame]; exact valid,by rw [frame]; exact lengths,by rw [frame],by rw [frame],?_,by rw [frame],by rw [frame]⟩
    intro owner sc h
    rw [frame] at h
    have := strict owner sc h
    omega
  have cq : Cq (scalarBound caller initial) (storageBound caller) initial.scalars.work initial := by
    refine ⟨Nat.le_refl _,?_,?_,?_⟩
    · change initial.scalars.peak ≤ scalarBound caller initial
      unfold scalarBound; omega
    · change initial.frame.state.storage.peak ≤ storageBound caller
      rw [frame]; exact Nat.le_max_left _ _
    · change initial.peak ≤ scalarBound caller initial+storageBound caller
      unfold scalarBound; omega
  have hbase : caller.scalars.baseMemory ≤ (callerP caller).length := by simp [callerP]; omega
  have run := sound (gOp ty).body (by simp [gOp, GenericFriendReturnRaw.rawBody, GenericFriendReturnRaw.add64, GenericFriendReturnRaw.add32, Scalar, NExpr.scalarOnly]) 1 _ r ran
    (L0:=caller.frame.state.liveSpace) (T0:=caller.frame.state.storage.work)
    (N:=caller.frame.state.storage.objects.length) (scq:=caller.scope+1)
    (SPB:=scalarBound caller initial) (TPB:=storageBound caller) (W:=initial.scalars.work)
    initial qs fa cq hbase
    (by simp [inputs]; unfold scalarBound; omega)
    (by unfold scalarBound; omega) (Nat.le_refl _) (by exact Nat.le_max_right _ _)
  obtain ⟨fuel,step,executed,returned,breaking,qsD,faD,cqD⟩ := run
  have typed : StageState ty caller initial step.state b1.address b2.address b3.address b4.address (x+y) (n+m) := by
    refine ⟨?_,faD,?_,?_,hs,ht⟩
    · rw [ps] at qsD
      simpa [ws,fields,fieldBindings,ssl,inputs] using qsD
    · refine ⟨?_,cqD.scalarPeak,cqD.storagePeak,cqD.outerPeak⟩
      have bound := cqD.work
      rw [work] at bound
      omega
    · have stable := CppScalarContents.run_stable fuel (gOp ty).body initial step
        (by simp [gOp, GenericFriendReturnRaw.rawBody, GenericFriendReturnRaw.add64, GenericFriendReturnRaw.add32, CppScalarContents.Allowed, Proofs.CppScalarFrame.Scalar]) (by intro owner sc found; rw [frame] at found; have h := strict owner sc found; rw [scope]; omega) executed
      have initialContents : CppScalarContents.Contents caller.frame initial.frame := by
        rw [frame]; exact ⟨rfl,rfl,rfl,rfl⟩
      exact initialContents.trans stable.contents
  refine ⟨initial,fuel,step.state,prepared,?_,typed⟩
  have stepEq : step = ⟨step.state,none,false⟩ := by
    cases step
    simp only [ret,Option.map_none] at returned
    simp_all
  exact executed.trans (congrArg (fun q : NStep => Proofs.CppLoop.Outcome.finished q) stepEq)


abbrev cx (ty : Ty) (x : Int) : Cell := ⟨ty,x⟩
abbrev cn (n : Int) : Cell := ⟨i32,n⟩


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

theorem finish_export (x n : Int) (a b c d : Nat) (caller initial callee : NState) (targetConst : Bool)
    (ready : StageState ty caller initial callee a b c d x n)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    MemberView.finishView caller callee [] (gFields ty)
        [] (gPerm ty targetConst) =
      some (exported ty x n caller callee targetConst,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
    ExportState ty x n caller initial (exported ty x n caller callee targetConst) targetConst := by
  have mem : callee.scalars.memory = callerP caller ++ (fields ty x n) := by simpa using ready.scalar.memory
  have bs := ready.scalar.bindings
  have sl := ready.scalar.slots
  have c4 : callee.scalarCell 6 ty = some (⟨(callerP caller).length+2,true⟩,(cx ty x)) := by
    simp [NState.scalarCell,NState.scalarSlot,mem,bs,sl,fieldBindings,fields,inputs,ssl,List.range_succ,cx,ready.xValid]
  have c5 : callee.scalarCell 7 i32 = some (⟨(callerP caller).length+3,true⟩,(cn n)) := by
    simp [NState.scalarCell,NState.scalarSlot,mem,bs,sl,fieldBindings,fields,inputs,ssl,List.range_succ,cn,ready.nValid]
  have captured : Proofs.CppConstructorFinish.captureAll callee
      (gFields ty) = some [((cx ty x),true),((cn n),true)] := by
    change Proofs.CppConstructorFinish.captureAll callee [⟨6,ty⟩,⟨7,i32⟩] = _
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
  have finished : MemberView.finishView caller callee [] (gFields ty)
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



theorem view_export_correct (caller : NState) (targetConst : Bool) (s1 s2 s3 s4 : Nat)
    (b1 b2 b3 b4 : CppState.Binding) (x n y m : Int)
    (c1 : caller.scalarCell s1 ty = some (b1,⟨ty,x⟩)) (c2 : caller.scalarCell s2 i32 = some (b2,⟨i32,n⟩))
    (c3 : caller.scalarCell s3 ty = some (b3,⟨ty,y⟩)) (c4 : caller.scalarCell s4 i32 = some (b4,⟨i32,m⟩))
    (hs : ty.valid (x+y) = true) (ht : i32.valid (n+m) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out,
      prepare caller (gOp ty).parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some initial ∧
      (gView ty) fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] targetConst =
          .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
      ExportState ty (x+y) (n+m) caller initial out targetConst := by
  obtain ⟨initial,fuel,callee,prepared,ran,ready⟩ := stage_ready caller s1 s2 s3 s4 b1 b2 b3 b4 x n y m
    c1 c2 c3 c4 hs ht valid lengths strict base
  obtain ⟨fin,post⟩ := finish_export (x+y) (n+m) b1.address b2.address b3.address b4.address
    caller initial callee targetConst ready base
  refine ⟨initial,fuel,exported ty (x+y) (n+m) caller callee targetConst,prepared,?_,post⟩
  exact MemberView.constructView_of_steps (gOp ty) fuel caller initial callee _
    [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] []
    (gFields ty) [] (gPerm ty targetConst)
    (Proofs.CppConstructorMultiFinish.reference caller 0 2) none prepared ran (Or.inl rfl) fin

theorem object_export_correct (caller : NState) (targetConst : Bool) (s1 s2 s3 s4 : Nat)
    (b1 b2 b3 b4 : CppState.Binding) (x n y m : Int)
    (c1 : caller.scalarCell s1 ty = some (b1,⟨ty,x⟩)) (c2 : caller.scalarCell s2 i32 = some (b2,⟨i32,n⟩))
    (c3 : caller.scalarCell s3 ty = some (b3,⟨ty,y⟩)) (c4 : caller.scalarCell s4 i32 = some (b4,⟨i32,m⟩))
    (hs : ty.valid (x+y) = true) (ht : i32.valid (n+m) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out,
      prepare caller (gOp ty).parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some initial ∧
      (gObjects ty) fuel caller [⟨[],[s1,s2]⟩,⟨[],[s3,s4]⟩] targetConst =
          .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
      ExportState ty (x+y) (n+m) caller initial out targetConst := by
  obtain ⟨initial,fuel,out,prepared,ran,post⟩ := view_export_correct caller targetConst s1 s2 s3 s4
    b1 b2 b3 b4 x n y m c1 c2 c3 c4 hs ht valid lengths strict base
  have args : MemberFactory.referenceArguments caller
      [[(ty,false),(i32,false)],[(ty,false),(i32,false)]] [⟨[],[s1,s2]⟩,⟨[],[s3,s4]⟩] =
      some [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] := by
    simp [MemberFactory.referenceArguments,MemberFactory.referenceFields,c1,c2,c3,c4]
  refine ⟨initial,fuel,out,prepared,?_,post⟩
  change (match MemberFactory.referenceArguments caller
    [[(ty,false),(i32,false)],[(ty,false),(i32,false)]] [⟨[],[s1,s2]⟩,⟨[],[s3,s4]⟩] with
    | none => Proofs.CppLoop.Outcome.fault
    | some arguments => (gView ty) fuel caller arguments targetConst) = _
  rw [args]
  exact ran

theorem total_work (x n : Int) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty x n caller initial out targetConst) : out.work ≤ caller.work+25 := by
  have scalar := post.scalarWork
  have storage := post.storageWork
  simp only [NState.work]
  omega

end GenericFriendCall
