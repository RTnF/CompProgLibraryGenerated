namespace GenericSetObjectRaw
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

abbrev cx (ty : Ty) (x : Int) : Cell := ⟨ty,x⟩
variable (ty : Ty)
abbrev cf (f : Int) : Cell := ⟨bl,f⟩
def inputs (x f y g : Int) : List Cell := [cx ty x,cf f,cx ty y,cf g]
def refs (P : List Cell) : List CppState.Binding :=
  (List.range 4).map (fun i => ⟨P.length+i,true⟩) ++ [⟨P.length+4,false⟩]
def selectedValue (x f y : Int) : Int := if f=0 then x else y
def selectedFlag (f g : Int) : Int := if f=0 then f else g

def arm (ty : Ty) (dst source : Nat) : Command :=
  .sequence (.scope (.sequence (.primitive (.assign dst ty (.variable ty source))) Sk)) Sk
def choose (ty : Ty) (flag dst yes no : Nat) : Command :=
  .branch (.variable bl flag) (arm ty dst yes) (arm ty dst no)

theorem choose_assign (ps : PS) (ty : Ty) (flag dst yes no : Nat) (c x y z : Int)
    (hc : (NExpr.variable bl flag).denote (penv ps) = some c)
    (hx : (NExpr.variable ty no).denote (penv ps) = some x)
    (hy : (NExpr.variable ty yes).denote (penv ps) = some y)
    (vx : ty.valid x = true) (vy : ty.valid y = true)
    (binding : CppState.Binding) (hb : ps.bs[dst]? = some binding)
    (hm : ps.mem[binding.address]? = some ⟨ty,z⟩) (vz : ty.valid z = true)
    (hw : binding.writable = true) :
    ∃ r, pexec 1 (choose ty flag dst yes no) ps = some r ∧
      r.ret = none ∧ r.cost = 5 ∧ r.need = ps.mem.length+ps.bs.length+3 ∧
      r.ps = ⟨ps.mem.set binding.address ⟨ty,if c=0 then x else y⟩,ps.bs⟩ := by
  by_cases zero : c=0
  · have st := pstmt_assign_ok ps dst ty (.variable ty no) x hx binding ⟨ty,z⟩ hb hm rfl vz hw x
      (Ty.convert_of_valid ty x vx)
    have br := pexec_braced 1 (.assign dst ty (.variable ty no)) ps _ st rfl (by simp) rfl
    have q := pexec_branch_false 1 (.variable bl flag) (arm ty dst yes) (arm ty dst no) ps (by simpa [zero] using hc) _ br
    refine ⟨_,q,rfl,?_,?_,?_⟩
    · simp [NExpr.nodes]
    · simp [NExpr.nodes]; omega
    · simp [zero]
  · have st := pstmt_assign_ok ps dst ty (.variable ty yes) y hy binding ⟨ty,z⟩ hb hm rfl vz hw y
      (Ty.convert_of_valid ty y vy)
    have br := pexec_braced 1 (.assign dst ty (.variable ty yes)) ps _ st rfl (by simp) rfl
    have q := pexec_branch_true 1 (.variable bl flag) (arm ty dst yes) (arm ty dst no) ps c hc zero _ br
    refine ⟨_,q,rfl,?_,?_,?_⟩
    · simp [NExpr.nodes]
    · simp [NExpr.nodes]; omega
    · simp [zero]

def tailBody : Command :=
  .sequence (.primitive (.declare ty true (.literal ty 0)))
    (.sequence (choose ty 4 5 2 0)
      (.sequence (.primitive (.declare ty true (.variable ty 5)))
        (.sequence (.primitive (.declare bl true (.literal bl 0)))
          (.sequence (choose bl 4 7 3 1)
            (.sequence (.primitive (.declare bl true (.variable bl 7))) Sk)))))
def rawBody : Command :=
  .sequence (.primitive (.declare bl false (.variable bl 1))) (tailBody ty)


theorem tail_exec (P : List Cell) (x f y g : Int)
    (hx : ty.valid x = true) (hf : bl.valid f = true)
    (hy : ty.valid y = true) (hg : bl.valid g = true) :
    ∃ r, pexec 1 (tailBody ty) ⟨P ++ inputs ty x f y g ++ [cf f],refs P⟩ = some r ∧
      r.ret = none ∧ r.cost = 18 ∧ r.need = P.length+21 ∧
      r.ps = ws (P ++ inputs ty x f y g ++ [cf f]) (refs P)
        [cx ty (selectedValue x f y),cx ty (selectedValue x f y),cf (selectedFlag f g),cf (selectedFlag f g)] := by
  let M := P ++ inputs ty x f y g ++ [cf f]
  let R := refs P
  let v := selectedValue x f y
  let n := selectedFlag f g
  let L1 : List Cell := [cx ty 0]
  let L1' : List Cell := [cx ty v]
  let L2 : List Cell := [cx ty v,cx ty v]
  let L3 : List Cell := [cx ty v,cx ty v,cf 0]
  let L3' : List Cell := [cx ty v,cx ty v,cf n]
  let L4 : List Cell := [cx ty v,cx ty v,cf n,cf n]
  have vv : ty.valid v = true := by unfold v selectedValue; split <;> assumption
  have vn : bl.valid n = true := by unfold n selectedFlag; split <;> assumption
  have flag (L : List Cell) : (NExpr.variable bl 4).denote (penv (ws M R L)) = some f := by
    rw [den_variable]
    exact ws_env_ref M R L 4 (P.length+4) false bl f (by simp [R,refs]) (by simp [M,inputs,cf]) hf
  have value0 (L : List Cell) : (NExpr.variable ty 0).denote (penv (ws M R L)) = some x := by
    rw [den_variable]
    exact ws_env_ref M R L 0 P.length true ty x (by simp [R,refs,List.range_succ]) (by simp [M,inputs,cx]) hx
  have value2 (L : List Cell) : (NExpr.variable ty 2).denote (penv (ws M R L)) = some y := by
    rw [den_variable]
    exact ws_env_ref M R L 2 (P.length+2) true ty y (by simp [R,refs,List.range_succ]) (by simp [M,inputs,cx]) hy
  have flag1 (L : List Cell) : (NExpr.variable bl 1).denote (penv (ws M R L)) = some f := by
    rw [den_variable]
    exact ws_env_ref M R L 1 (P.length+1) true bl f (by simp [R,refs,List.range_succ]) (by simp [M,inputs,cf]) hf
  have flag3 (L : List Cell) : (NExpr.variable bl 3).denote (penv (ws M R L)) = some g := by
    rw [den_variable]
    exact ws_env_ref M R L 3 (P.length+3) true bl g (by simp [R,refs,List.range_succ]) (by simp [M,inputs,cf]) hg
  have z64 : ty.valid 0 = true := Proofs.GenericLazy.valid_zero ty
  have zb : bl.valid 0 = true := by decide
  have q0 := (pexec_prim 1 _ _).trans (ws_declare M R [] ty (.literal ty 0) 0
    (by simp [NExpr.denote,z64]) (Ty.convert_of_valid _ _ z64))
  obtain ⟨b1,qb1,rb1,cb1,nb1,pb1⟩ := choose_assign (ws M R L1) ty 4 5 2 0 f x y 0
    (flag L1) (value0 L1) (value2 L1) hx hy ⟨M.length,true⟩
    (by simp [ws,R,refs,L1,List.range_succ]) (by simp [ws,L1,cx]) z64 rfl
  have q1 : pexec 1 (choose ty 4 5 2 0) (ws M R L1) =
      some ⟨ws M R L1',none,5,P.length+15⟩ := by
    have eq : b1 = ⟨ws M R L1',none,5,P.length+15⟩ := by
      cases b1
      simp_all [ws,M,R,refs,L1,L1',v,selectedValue,inputs,List.set_append_right,Nat.add_assoc,cx,cf]
    simpa [eq] using qb1
  have ev : (NExpr.variable ty 5).denote (penv (ws M R L1')) = some v := by
    rw [den_variable]
    simpa [R,refs] using ws_env_loc M R L1' 0 (cx ty v) ty rfl rfl vv
  have q2 := (pexec_prim 1 _ _).trans (ws_declare M R L1' ty (.variable ty 5) v ev (Ty.convert_of_valid _ _ vv))
  have q3 := (pexec_prim 1 _ _).trans (ws_declare M R L2 bl (.literal bl 0) 0
    (by simp [NExpr.denote,zb]) (Ty.convert_of_valid _ _ zb))
  obtain ⟨b2,qb2,rb2,cb2,nb2,pb2⟩ := choose_assign (ws M R L3) bl 4 7 3 1 f f g 0
    (flag L3) (flag1 L3) (flag3 L3) hf hg ⟨M.length+2,true⟩
    (by simp [ws,R,refs,L3,List.range_succ]) (by simp [ws,L3,cf]) zb rfl
  have q4 : pexec 1 (choose bl 4 7 3 1) (ws M R L3) =
      some ⟨ws M R L3',none,5,P.length+19⟩ := by
    have eq : b2 = ⟨ws M R L3',none,5,P.length+19⟩ := by
      cases b2
      simp_all [ws,M,R,refs,L3,L3',n,selectedFlag,inputs,List.set_append_right,Nat.add_assoc,cx,cf]
    simpa [eq] using qb2
  have en : (NExpr.variable bl 7).denote (penv (ws M R L3')) = some n := by
    rw [den_variable]
    simpa [R,refs] using ws_env_loc M R L3' 2 (cf n) bl rfl rfl vn
  have q5 := (pexec_prim 1 _ _).trans (ws_declare M R L3' bl (.variable bl 7) n en (Ty.convert_of_valid _ _ vn))
  have all := seq_some q0 rfl (seq_some q1 rfl (seq_some q2 rfl (seq_some q3 rfl (seq_some q4 rfl
    (seq_some q5 rfl (pexec_skip 1 _))))))
  refine ⟨⟨ws M R L4,none,18,P.length+21⟩,?_,rfl,rfl,rfl,rfl⟩
  simpa [tailBody,ws,M,R,refs,inputs,L1,L1',L2,L3,L3',L4,v,n,cx,cf,NExpr.nodes,Nat.add_assoc] using all

theorem raw_exec (P : List Cell) (x f y g : Int)
    (hx : ty.valid x = true) (hf : bl.valid f = true)
    (hy : ty.valid y = true) (hg : bl.valid g = true) :
    ∃ r, pexec 1 (rawBody ty) (ws P [] (inputs ty x f y g)) = some r ∧
      r.ret = none ∧ r.cost = 20 ∧ r.need = P.length+21 ∧
      r.ps = ws (P ++ inputs ty x f y g ++ [cf f]) (refs P)
        [cx ty (selectedValue x f y),cx ty (selectedValue x f y),cf (selectedFlag f g),cf (selectedFlag f g)] := by
  have ev : (NExpr.variable bl 1).denote (penv (ws P [] (inputs ty x f y g))) = some f := by
    rw [den_variable]
    exact ws_env_loc P [] (inputs ty x f y g) 1 (cf f) bl rfl rfl hf
  have q0 := (pexec_prim 1 _ _).trans (pstmt_declare_ok (ws P [] (inputs ty x f y g)) bl false
    (.variable bl 1) f ev f (Ty.convert_of_valid _ _ hf))
  obtain ⟨r,ran,ret,cost,need,ps⟩ := tail_exec ty P x f y g hx hf hy hg
  have q1 : pexec 1 (tailBody ty)
      ⟨(ws P [] (inputs ty x f y g)).mem ++ [cf f],
       (ws P [] (inputs ty x f y g)).bs ++ [⟨(ws P [] (inputs ty x f y g)).mem.length,false⟩]⟩ = some r := by
    simpa [ws,refs,inputs,List.range_succ,Nat.add_assoc] using ran
  have all := seq_some q0 rfl q1
  refine ⟨⟨r.ps,none,20,P.length+21⟩,?_,rfl,rfl,rfl,ps⟩
  have peakBound : max (P.length+13) (P.length+21) = P.length+21 := Nat.max_eq_right (by omega)
  simpa [rawBody,ret,cost,need,NExpr.nodes,ws,inputs,Nat.add_assoc,peakBound] using all

end GenericSetObjectRaw

namespace GenericSetObject
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


open OriginalSetObject
open GenericSetObjectRaw
open Proofs.Mod61Body Proofs.CppScalarValuePrepare

theorem caller_cell (caller : NState) (slot : Nat) (ty : Ty) (binding : CppState.Binding) (v : Int)
    (found : caller.scalarCell slot ty = some (binding,⟨ty,v⟩)) :
    (callerP caller)[binding.address]? = some ⟨ty,v⟩ ∧ ty.valid v = true := by
  obtain ⟨index,sl,bs,mem,ht,hv⟩ := scalarCell_facts found
  refine ⟨?_,hv⟩
  simp only [callerP,List.getElem?_append_left (List.getElem?_eq_some_iff.mp mem).1]
  exact mem

variable {ty : Ty}

def gCompose (ty : Ty) : NProgram :=
  ⟨[.scalar ty false true, .scalar bl false true, .scalar ty false true, .scalar bl false true], .unit, GenericSetObjectRaw.rawBody ty⟩
def gFields (ty : Ty) : List Proofs.CppConstructorFinish.ScalarField := [⟨6,ty⟩,⟨8,bl⟩]
def gPerm (ty : Ty) (targetConst : Bool) : List (Proofs.CppScalar.Ty × Bool) :=
  [(ty,(true && (!targetConst || false))),(bl,(true && (!targetConst || false)))]
def gView (ty : Ty) (fuel : Nat) (caller : NState) (arguments : List NArgument) (targetConst : Bool) :
    Proofs.CppLoop.Outcome (NState × Proofs.CppConstructorMultiFinish.ObjectRef) :=
  MemberView.constructViewFuel (gCompose ty) fuel caller arguments [] (gFields ty)
    (vectorPermissions targetConst) (gPerm ty targetConst)
def gObjects (ty : Ty) (fuel : Nat) (caller : NState)
    (objects : List Proofs.CppConstructorMultiFinish.ObjectRef) (targetConst : Bool) :
    Proofs.CppLoop.Outcome (NState × Proofs.CppConstructorMultiFinish.ObjectRef) :=
  match MemberFactory.objectArguments caller [(true,[(ty,true),(bl,true)]),(true,[(ty,true),(bl,true)])] objects with
  | none => .fault
  | some args => gView ty fuel caller args targetConst

def scalarBound (caller initial : NState) : Nat :=
  max (max initial.scalars.peak initial.peak) ((callerP caller).length+20-caller.scalars.baseMemory+100)
def storageBound (caller : NState) : Nat :=
  max caller.frame.state.storage.peak caller.frame.state.liveSpace

def fieldCells (ty : Ty) (x f y g : Int) : List Cell :=
  inputs ty x f y g ++ [cf f,cx ty (selectedValue x f y),cx ty (selectedValue x f y),
    cf (selectedFlag f g),cf (selectedFlag f g)]
def fieldBindings (P : List Cell) : List CppState.Binding :=
  refs P ++ (List.range 4).map (fun i => ⟨P.length+5+i,true⟩)

structure StageState (ty : Ty) (caller initial callee : NState) (x f y g : Int) : Prop where
  scalar : QS callee [] caller.scalars.baseMemory (caller.scope+1)
    (callerP caller ++ fieldCells ty x f y g) (fieldBindings (callerP caller)) (ssl 9)
  frame : FA callee.frame caller.frame.state.liveSpace caller.frame.state.storage.work
    (caller.scope+1) caller.frame.state.storage.objects.length
  counters : Cq (scalarBound caller initial) (storageBound caller) (caller.scalars.work+29) callee
  contents : CppScalarContents.Contents caller.frame callee.frame
  vValid : ty.valid (selectedValue x f y) = true
  nValid : bl.valid (selectedFlag f g) = true

theorem stage_ready (caller : NState) (x f y g : Int)
    (hx : ty.valid x = true) (hf : bl.valid f = true)
    (hy : ty.valid y = true) (hg : bl.valid g = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel callee, prepare caller (gCompose ty).parameters
        [.value (.literal ty x),.value (.literal bl f),.value (.literal ty y),.value (.literal bl g)] = some initial ∧
      runFuel fuel (gCompose ty).body initial = .finished ⟨callee,none,false⟩ ∧
      StageState ty caller initial callee x f y g := by
  obtain ⟨initial,prepared,slots,mem,bindings,bas,scope,frame,work,peak⟩ :=
    prepare_literals4 ty bl ty bl caller (gCompose ty).parameters rfl x f y g hx hf hy hg valid
  obtain ⟨r,ran,ret,cost,need,ps⟩ := raw_exec ty (callerP caller) x f y g hx hf hy hg
  have hv : ty.valid (selectedValue x f y) = true := by unfold selectedValue; split <;> assumption
  have hn : bl.valid (selectedFlag f g) = true := by unfold selectedFlag; split <;> assumption
  have qs : QS initial [] caller.scalars.baseMemory (caller.scope+1)
      (ws (callerP caller) [] (inputs ty x f y g)).mem (ws (callerP caller) [] (inputs ty x f y g)).bs (ssl 4) := by
    refine ⟨by simpa [ssl,List.range_succ] using slots,?_,?_,bas,scope⟩
    · simpa [ws,inputs,cx,cf] using mem
    · simpa [ws,inputs] using bindings
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
  have hbase : caller.scalars.baseMemory ≤ (ws (callerP caller) [] (inputs ty x f y g)).mem.length := by simp [ws,callerP,inputs]; omega
  have run := sound (gCompose ty).body (by simp [gCompose, GenericSetObjectRaw.rawBody, GenericSetObjectRaw.tailBody, GenericSetObjectRaw.choose, GenericSetObjectRaw.arm, Scalar, NExpr.scalarOnly]) 1 _ r ran
    (L0:=caller.frame.state.liveSpace) (T0:=caller.frame.state.storage.work)
    (N:=caller.frame.state.storage.objects.length) (scq:=caller.scope+1)
    (SPB:=scalarBound caller initial) (TPB:=storageBound caller) (W:=initial.scalars.work)
    initial qs fa cq hbase
    (by simp [ws,inputs]; unfold scalarBound; omega)
    (by unfold scalarBound; omega) (Nat.le_refl _) (by exact Nat.le_max_right _ _)
  obtain ⟨fuel,step,executed,returned,breaking,qsD,faD,cqD⟩ := run
  have typed : StageState ty caller initial step.state x f y g := by
    refine ⟨?_,faD,?_,?_,hv,hn⟩
    · rw [ps] at qsD
      simpa [ws,fieldCells,fieldBindings,ssl,inputs,refs,Nat.add_assoc] using qsD
    · refine ⟨?_,cqD.scalarPeak,cqD.storagePeak,cqD.outerPeak⟩
      have bound := cqD.work
      rw [work] at bound
      omega
    · have stable := CppScalarContents.run_stable fuel (gCompose ty).body initial step
        (by simp [gCompose, GenericSetObjectRaw.rawBody, GenericSetObjectRaw.tailBody, GenericSetObjectRaw.choose, GenericSetObjectRaw.arm, CppScalarContents.Allowed, Proofs.CppScalarFrame.Scalar]) (by intro owner sc found; rw [frame] at found; have h := strict owner sc found; rw [scope]; omega) executed
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
abbrev cn (n : Int) : Cell := ⟨bl,n⟩


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
  scalarWork : out.scalars.work ≤ caller.scalars.work+32
  storageWork : out.frame.state.storage.work = caller.frame.state.storage.work
  scalarPeak : out.scalars.peak ≤ max caller.scalars.peak (scalarBound caller initial)
  storagePeak : out.frame.state.storage.peak ≤ storageBound caller
  outerPeak : out.peak ≤ max caller.peak
    (max caller.scalars.peak (scalarBound caller initial)+storageBound caller)
  contents : CppScalarContents.Contents caller.frame out.frame
  xValid : ty.valid x = true
  nValid : bl.valid n = true

theorem finish_export (x f y g : Int) (caller initial callee : NState) (targetConst : Bool)
    (ready : StageState ty caller initial callee x f y g)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    MemberView.finishView caller callee [] (gFields ty)
        [] (gPerm ty targetConst) =
      some (exported ty (selectedValue x f y) (selectedFlag f g) caller callee targetConst,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
    ExportState ty (selectedValue x f y) (selectedFlag f g) caller initial (exported ty (selectedValue x f y) (selectedFlag f g) caller callee targetConst) targetConst := by
  have mem : callee.scalars.memory = callerP caller ++ (fieldCells ty x f y g) := by simpa using ready.scalar.memory
  have bs := ready.scalar.bindings
  have sl := ready.scalar.slots
  have c4 : callee.scalarCell 6 ty = some (⟨(callerP caller).length+6,true⟩,(cx ty (selectedValue x f y))) := by
    simp [NState.scalarCell,NState.scalarSlot,mem,bs,sl,fieldBindings,fieldCells,inputs,refs,cf,Nat.add_assoc,ssl,List.range_succ,cx,ready.vValid]
  have c5 : callee.scalarCell 8 bl = some (⟨(callerP caller).length+8,true⟩,(cn (selectedFlag f g))) := by
    simp [NState.scalarCell,NState.scalarSlot,mem,bs,sl,fieldBindings,fieldCells,inputs,refs,cf,Nat.add_assoc,ssl,List.range_succ,cn,ready.nValid]
  have captured : Proofs.CppConstructorFinish.captureAll callee
      (gFields ty) = some [((cx ty (selectedValue x f y)),true),((cn (selectedFlag f g)),true)] := by
    change Proofs.CppConstructorFinish.captureAll callee [⟨6,ty⟩,⟨8,bl⟩] = _
    simp [Proofs.CppConstructorFinish.captureAll,Proofs.CppConstructorFinish.capture,c4,c5]
  have viewed : Proofs.CppConstructorView.restrictValues [((cx ty (selectedValue x f y)),true),((cn (selectedFlag f g)),true)] (gPerm ty targetConst) =
      some (destinationValues ty (selectedValue x f y) (selectedFlag f g) targetConst) := by cases targetConst <;> simp [Proofs.CppConstructorView.restrictValues, gPerm, destinationValues, cx, cn]
  have takeM : callee.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [mem]; exact Proofs.MonoidCallCore.take_P caller (fieldCells ty x f y g)
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
        some (exported ty (selectedValue x f y) (selectedFlag f g) caller callee targetConst,Proofs.CppConstructorMultiFinish.reference caller 0 2) := by
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
  have sp : (exported ty (selectedValue x f y) (selectedFlag f g) caller callee targetConst).scalars.peak ≤
      max caller.scalars.peak (scalarBound caller initial) := by
    simp only [exported,Proofs.CppConstructorMultiFinish.restored,NState.observe,CppState.State.observe]
    simp only [takeM,destinationValues,List.map_cons,List.map_nil,List.length_append,List.length_cons,List.length_nil,
      Proofs.CppConstructorFinish.scalarBindings]
    change max (max caller.scalars.peak callee.scalars.peak)
      (caller.scalars.memory.length+2-caller.scalars.baseMemory+(caller.scalars.bindings.length+2)+0) ≤ _
    omega
  have tp : (exported ty (selectedValue x f y) (selectedFlag f g) caller callee targetConst).frame.state.storage.peak ≤ storageBound caller := by
    change max callee.frame.state.storage.peak (callee.frame.state.liveSpace-callee.frame.state.storage.baseSpace) ≤ storageBound caller
    rw [live]
    unfold storageBound at *
    omega
  refine ⟨?_,?_,?_,?_,rfl,?_,?_,?_,?_,?_,sp,tp,?_,?_,ready.vValid,ready.nValid⟩
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
  · change callee.scalars.work+0+(destinationValues ty (selectedValue x f y) (selectedFlag f g) targetConst).length+1 ≤ caller.scalars.work+32
    simp [destinationValues]
    omega
  · change callee.frame.state.storage.work = caller.frame.state.storage.work
    exact ready.frame.work
  · change max (max caller.peak callee.peak)
      ((exported ty (selectedValue x f y) (selectedFlag f g) caller callee targetConst).scalars.peak+(exported ty (selectedValue x f y) (selectedFlag f g) caller callee targetConst).frame.state.storage.peak) ≤ _
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
    out.scalarCell (caller.slots.length+1) bl = some (⟨caller.scalars.memory.length+1,!targetConst⟩,(cn n)) := by
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



theorem view_export_correct (caller : NState) (targetConst : Bool) (x f y g : Int)
    (hx : ty.valid x = true) (hf : bl.valid f = true)
    (hy : ty.valid y = true) (hg : bl.valid g = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out, prepare caller (gCompose ty).parameters
        [.value (.literal ty x),.value (.literal bl f),.value (.literal ty y),.value (.literal bl g)] = some initial ∧
      (gView ty) fuel caller
        [.value (.literal ty x),.value (.literal bl f),.value (.literal ty y),.value (.literal bl g)] targetConst =
          .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
      ExportState ty (selectedValue x f y) (selectedFlag f g) caller initial out targetConst := by
  obtain ⟨initial,fuel,callee,prepared,ran,ready⟩ := stage_ready caller x f y g hx hf hy hg valid lengths strict base
  obtain ⟨fin,post⟩ := finish_export x f y g caller initial callee targetConst ready base
  refine ⟨initial,fuel,exported ty (selectedValue x f y) (selectedFlag f g) caller callee targetConst,prepared,?_,post⟩
  exact MemberView.constructView_of_steps (gCompose ty) fuel caller initial callee _
    [.value (.literal ty x),.value (.literal bl f),.value (.literal ty y),.value (.literal bl g)] []
    (gFields ty) [] (gPerm ty targetConst)
    (Proofs.CppConstructorMultiFinish.reference caller 0 2) none prepared ran (Or.inl rfl) fin

theorem object_export_correct (caller : NState) (targetConst : Bool) (s1 s2 s3 s4 : Nat)
    (b1 b2 b3 b4 : CppState.Binding) (x f y g : Int)
    (c1 : caller.scalarCell s1 ty = some (b1,⟨ty,x⟩)) (c2 : caller.scalarCell s2 bl = some (b2,⟨bl,f⟩))
    (c3 : caller.scalarCell s3 ty = some (b3,⟨ty,y⟩)) (c4 : caller.scalarCell s4 bl = some (b4,⟨bl,g⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out, prepare caller (gCompose ty).parameters
        [.value (.literal ty x),.value (.literal bl f),.value (.literal ty y),.value (.literal bl g)] = some initial ∧
      (gObjects ty) fuel caller [⟨[],[s1,s2]⟩,⟨[],[s3,s4]⟩] targetConst =
          .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
      ExportState ty (selectedValue x f y) (selectedFlag f g) caller initial out targetConst := by
  obtain ⟨_,hx⟩ := caller_cell caller s1 ty b1 x c1
  obtain ⟨_,hf⟩ := caller_cell caller s2 bl b2 f c2
  obtain ⟨_,hy⟩ := caller_cell caller s3 ty b3 y c3
  obtain ⟨_,hg⟩ := caller_cell caller s4 bl b4 g c4
  obtain ⟨initial,fuel,out,prepared,ran,post⟩ := view_export_correct caller targetConst x f y g hx hf hy hg valid lengths strict base
  have args : MemberFactory.objectArguments caller
      [(true,[(ty,true),(bl,true)]),(true,[(ty,true),(bl,true)])] [⟨[],[s1,s2]⟩,⟨[],[s3,s4]⟩] =
      some [.value (.literal ty x),.value (.literal bl f),.value (.literal ty y),.value (.literal bl g)] := by
    simp [MemberFactory.objectArguments,MemberFactory.valueFields,c1,c2,c3,c4]
  refine ⟨initial,fuel,out,prepared,?_,post⟩
  change (match MemberFactory.objectArguments caller
      [(true,[(ty,true),(bl,true)]),(true,[(ty,true),(bl,true)])] [⟨[],[s1,s2]⟩,⟨[],[s3,s4]⟩] with
    | none => Proofs.CppLoop.Outcome.fault
    | some arguments => (gView ty) fuel caller arguments targetConst) = _
  rw [args]; exact ran

theorem total_work (x n : Int) (caller initial out : NState) (targetConst : Bool)
    (post : ExportState ty x n caller initial out targetConst) : out.work ≤ caller.work+32 := by
  have scalar := post.scalarWork
  have storage := post.storageWork
  simp only [NState.work]
  omega

end GenericSetObject
