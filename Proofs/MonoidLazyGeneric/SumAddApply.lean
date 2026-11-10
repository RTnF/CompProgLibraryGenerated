import Proofs.CppClassCopyCommands
import Proofs.CppConstructorMultiFinish
import Proofs.CppConstructorView
import Proofs.CppFrameResolveExtension
import Proofs.CppNestedCall
import Proofs.MemberSupport
import Proofs.GenericLazy
import Proofs.MonoidLazyCall
import Proofs.CppScalarValuePrepare
import Proofs.CppScalarContents
import Proofs.GenericExtrema
import Proofs.GenericCall
import Proofs.MonoidLazyGeneric.MemberPrepare
open Proofs.CppScalar
namespace VPSumAddApply
def vectorPermissions (_targetConst : Bool) : List Bool := []
end VPSumAddApply
open VPSumAddApply
namespace GenericSumAddApplyRaw
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
abbrev cn (n : Int) : Cell := ⟨i32,n⟩
abbrev cx (ty : Ty) (x : Int) : Cell := ⟨ty,x⟩
variable (ty : Ty)
def refs (a : Nat) : List CppState.Binding := [⟨a,true⟩]
def resultCells (v x n : Int) : List Cell :=
  [cx ty x,cn n,cx ty (x+n*v),cn n,cx ty (x+n*v),cn n]
def product : NExpr := .binary ty .mul (Proofs.GenericLazy.castTo ty i32 (.variable i32 2)) (.variable ty 0)
def total : NExpr := .binary ty .add (.variable ty 1) (product ty)
def rawBody : Command :=
  .sequence (.primitive (.declare ty true (total ty)))
    (.sequence (.primitive (.declare i32 true (.variable i32 2)))
      (.sequence (.primitive (.declare ty true (.variable ty 3)))
        (.sequence (.primitive (.declare i32 true (.variable i32 4)))
          (.sequence (.scope Sk) Sk))))


theorem raw_exec (P : List Cell) (a : Nat) (v x n : Int)
    (receiver : P[a]? = some (cx ty v))
    (hv : ty.valid v = true) (hx : ty.valid x = true)
    (hn : i32.valid n = true) (hnt : ty.valid n = true)
    (hp : ty.valid (n*v) = true) (hs : ty.valid (x+n*v) = true) :
    ∃ r, pexec 1 (rawBody ty) (ws P (refs a) [cx ty x,cn n]) = some r ∧
      r.ret = none ∧ r.cost ≤ 14 ∧ r.need ≤ P.length+16 ∧
      r.ps = ws P (refs a) (resultCells ty v x n) := by
  let R := refs a
  let L2 : List Cell := [cx ty x,cn n]
  let L3 : List Cell := L2 ++ [cx ty (x+n*v)]
  let L4 : List Cell := L3 ++ [cn n]
  let L5 : List Cell := L4 ++ [cx ty (x+n*v)]
  let L6 := resultCells ty v x n
  have rv : (NExpr.variable ty 0).denote (penv (ws P R L2)) = some v := by
    rw [den_variable]
    exact ws_env_ref P R L2 0 a true ty v (by rfl) receiver hv
  have xx : (NExpr.variable ty 1).denote (penv (ws P R L2)) = some x := by
    rw [den_variable]
    exact ws_env_loc P R L2 0 (cx ty x) ty rfl rfl hx
  have nn (L : List Cell) (found : L[1]? = some (cn n)) :
      (NExpr.variable i32 2).denote (penv (ws P R L)) = some n := by
    rw [den_variable]
    exact ws_env_loc P R L 1 (cn n) i32 found rfl hn
  have castn : ((Proofs.GenericLazy.castTo ty i32 (.variable i32 2))).denote (penv (ws P R L2)) = some n := by
    exact Proofs.GenericLazy.castTo_den ty i32 (.variable i32 2) _ n (by rw [den_variable]; exact nn L2 rfl) hnt
  have mul : (product ty).denote (penv (ws P R L2)) = some (n*v) := by
    rw [product,den_binary,castn,rv]
    simpa [binaryValue] using Ty.convert_of_valid ty (n*v) hp
  have sum : (total ty).denote (penv (ws P R L2)) = some (x+n*v) := by
    rw [total,den_binary,xx,mul]
    simpa [binaryValue] using Ty.convert_of_valid ty (x+n*v) hs
  have read3 : (NExpr.variable ty 3).denote (penv (ws P R L4)) = some (x+n*v) := by
    rw [den_variable]
    exact ws_env_loc P R L4 2 (cx ty (x+n*v)) ty rfl rfl hs
  have read4 : (NExpr.variable i32 4).denote (penv (ws P R L5)) = some n := by
    rw [den_variable]
    exact ws_env_loc P R L5 3 (cn n) i32 rfl rfl hn
  have q0 := (pexec_prim 1 _ _).trans (ws_declare P R L2 ty (total ty) (x+n*v) sum (Ty.convert_of_valid _ _ hs))
  have q1 := (pexec_prim 1 _ _).trans (ws_declare P R L3 i32 (.variable i32 2) n (nn L3 rfl) (Ty.convert_of_valid _ _ hn))
  have q2 := (pexec_prim 1 _ _).trans (ws_declare P R L4 ty (.variable ty 3) (x+n*v) read3 (Ty.convert_of_valid _ _ hs))
  have q3 := (pexec_prim 1 _ _).trans (ws_declare P R L5 i32 (.variable i32 4) n read4 (Ty.convert_of_valid _ _ hn))
  have sc0 := pexec_scope 1 Sk (ws P R L6) _ (pexec_skip 1 _)
  have sc : pexec 1 (.scope Sk) (ws P R L6) = some ⟨ws P R L6,none,1,P.length+13⟩ := by
    simp only [List.take_length] at sc0
    simpa [ws,L6,resultCells,R,refs,Nat.add_assoc] using sc0
  have all := seq_some q0 rfl (seq_some q1 rfl (seq_some q2 rfl (seq_some q3 rfl (seq_some sc rfl (pexec_skip 1 _)))))
  have hn' := Proofs.GenericLazy.castTo_nodes ty i32 (.variable i32 2)
  simp only [NExpr.nodes] at hn'
  refine ⟨_,by simpa [rawBody,ws,L2,L3,L4,L5,L6,resultCells,R,refs,total,product,NExpr.nodes,Nat.add_assoc] using all,?h2,?h3,?h4,?h5⟩
  all_goals first | rfl | (simp [NExpr.nodes,ws,L6,resultCells,R,refs,total,product] <;> omega)

theorem raw_exec_conv (P : List Cell) (a : Nat) (v x n : Int)
    (receiver : P[a]? = some (cx ty v))
    (hv : ty.valid v = true) (hx : ty.valid x = true)
    (hn : i32.valid n = true) (hnt : ty.valid n = true)
    (q s : Int) (hcp : ty.convert (n*v) = some q) (hcs : ty.convert (x+q) = some s)
    (hq : ty.valid q = true) (hs : ty.valid s = true) :
    ∃ r, pexec 1 (rawBody ty) (ws P (refs a) [cx ty x,cn n]) = some r ∧
      r.ret = none ∧ r.cost ≤ 14 ∧ r.need ≤ P.length+16 ∧
      r.ps = ws P (refs a) ([cx ty x,cn n,cx ty s,cn n,cx ty s,cn n]) := by
  let R := refs a
  let L2 : List Cell := [cx ty x,cn n]
  let L3 : List Cell := L2 ++ [cx ty s]
  let L4 : List Cell := L3 ++ [cn n]
  let L5 : List Cell := L4 ++ [cx ty s]
  let L6 := [cx ty x,cn n,cx ty s,cn n,cx ty s,cn n]
  have rv : (NExpr.variable ty 0).denote (penv (ws P R L2)) = some v := by
    rw [den_variable]
    exact ws_env_ref P R L2 0 a true ty v (by rfl) receiver hv
  have xx : (NExpr.variable ty 1).denote (penv (ws P R L2)) = some x := by
    rw [den_variable]
    exact ws_env_loc P R L2 0 (cx ty x) ty rfl rfl hx
  have nn (L : List Cell) (found : L[1]? = some (cn n)) :
      (NExpr.variable i32 2).denote (penv (ws P R L)) = some n := by
    rw [den_variable]
    exact ws_env_loc P R L 1 (cn n) i32 found rfl hn
  have castn : ((Proofs.GenericLazy.castTo ty i32 (.variable i32 2))).denote (penv (ws P R L2)) = some n := by
    exact Proofs.GenericLazy.castTo_den ty i32 (.variable i32 2) _ n (by rw [den_variable]; exact nn L2 rfl) hnt
  have mul : (product ty).denote (penv (ws P R L2)) = some q := by
    rw [product,den_binary,castn,rv]
    simpa [binaryValue] using hcp
  have sum : (total ty).denote (penv (ws P R L2)) = some s := by
    rw [total,den_binary,xx,mul]
    simpa [binaryValue] using hcs
  have read3 : (NExpr.variable ty 3).denote (penv (ws P R L4)) = some s := by
    rw [den_variable]
    exact ws_env_loc P R L4 2 (cx ty s) ty rfl rfl hs
  have read4 : (NExpr.variable i32 4).denote (penv (ws P R L5)) = some n := by
    rw [den_variable]
    exact ws_env_loc P R L5 3 (cn n) i32 rfl rfl hn
  have q0 := (pexec_prim 1 _ _).trans (ws_declare P R L2 ty (total ty) s sum (Ty.convert_of_valid _ _ hs))
  have q1 := (pexec_prim 1 _ _).trans (ws_declare P R L3 i32 (.variable i32 2) n (nn L3 rfl) (Ty.convert_of_valid _ _ hn))
  have q2 := (pexec_prim 1 _ _).trans (ws_declare P R L4 ty (.variable ty 3) s read3 (Ty.convert_of_valid _ _ hs))
  have q3 := (pexec_prim 1 _ _).trans (ws_declare P R L5 i32 (.variable i32 4) n read4 (Ty.convert_of_valid _ _ hn))
  have sc0 := pexec_scope 1 Sk (ws P R L6) _ (pexec_skip 1 _)
  have sc : pexec 1 (.scope Sk) (ws P R L6) = some ⟨ws P R L6,none,1,P.length+13⟩ := by
    simp only [List.take_length] at sc0
    simpa [ws,L6,R,refs,Nat.add_assoc] using sc0
  have all := seq_some q0 rfl (seq_some q1 rfl (seq_some q2 rfl (seq_some q3 rfl (seq_some sc rfl (pexec_skip 1 _)))))
  have hn' := Proofs.GenericLazy.castTo_nodes ty i32 (.variable i32 2)
  simp only [NExpr.nodes] at hn'
  refine ⟨_,by simpa [rawBody,ws,L2,L3,L4,L5,L6,R,refs,total,product,NExpr.nodes,Nat.add_assoc] using all,?h2,?h3,?h4,?h5⟩
  all_goals first | rfl | (simp [NExpr.nodes,ws,L6,R,refs,total,product] <;> omega)


/-- Unsigned products and sums wrap modulo `2^width`: the results are the reduced values. -/
theorem raw_exec_wrap (P : List Cell) (a : Nat) (v x n : Int)
    (receiver : P[a]? = some (cx ty v))
    (hv : ty.valid v = true) (hx : ty.valid x = true)
    (hn : i32.valid n = true) (hnt : ty.valid n = true)
    (hb : ty.boolean = false) (hu : ty.signed = false) :
    ∃ q s, ty.valid q = true ∧ ty.valid s = true ∧ ty.convert (n*v) = some q ∧ ty.convert (x+q) = some s ∧
    ∃ r, pexec 1 (rawBody ty) (ws P (refs a) [cx ty x,cn n]) = some r ∧
      r.ret = none ∧ r.cost ≤ 14 ∧ r.need ≤ P.length+16 ∧
      r.ps = ws P (refs a) [cx ty x,cn n,cx ty s,cn n,cx ty s,cn n] := by
  have pos : (0 : Int) < 2 ^ ty.width := Int.pow_pos (by decide)
  have red (z : Int) : ty.convert z = some (z % 2 ^ ty.width) ∧ ty.valid (z % 2 ^ ty.width) = true := by
    have h0 : 0 ≤ z % 2 ^ ty.width := Int.emod_nonneg _ (by omega)
    have h1 : z % 2 ^ ty.width < 2 ^ ty.width := Int.emod_lt_of_pos _ pos
    exact ⟨by simp [Ty.convert, hb, hu], by simp [Ty.valid, hb, hu, h0, h1]⟩
  obtain ⟨cq, vq⟩ := red (n*v)
  obtain ⟨cs, vs⟩ := red (x + (n*v) % 2 ^ ty.width)
  obtain ⟨r, hr⟩ := raw_exec_conv ty P a v x n receiver hv hx hn hnt _ _ cq cs vq vs
  exact ⟨_, _, vq, vs, cq, cs, r, hr⟩

/-- A signed sum that leaves the range of `ty` faults at the first declaration. -/
theorem raw_sum_overflow_faults (P : List Cell) (a : Nat) (v x n : Int)
    (receiver : P[a]? = some (cx ty v))
    (hv : ty.valid v = true) (hx : ty.valid x = true)
    (hn : i32.valid n = true) (hnt : ty.valid n = true)
    (hp : ty.valid (n*v) = true)
    (hb : ty.boolean = false) (hsg : ty.signed = true) (hbad : ty.valid (x+n*v) = false) :
    pexec 1 (rawBody ty) (ws P (refs a) [cx ty x,cn n]) = none := by
  let R := refs a
  let L2 : List Cell := [cx ty x,cn n]
  have rv : (NExpr.variable ty 0).denote (penv (ws P R L2)) = some v := by
    rw [den_variable]
    exact ws_env_ref P R L2 0 a true ty v (by rfl) receiver hv
  have xx : (NExpr.variable ty 1).denote (penv (ws P R L2)) = some x := by
    rw [den_variable]
    exact ws_env_loc P R L2 0 (cx ty x) ty rfl rfl hx
  have castn : ((Proofs.GenericLazy.castTo ty i32 (.variable i32 2))).denote (penv (ws P R L2)) = some n := by
    exact Proofs.GenericLazy.castTo_den ty i32 (.variable i32 2) _ n
      (by rw [den_variable]; exact ws_env_loc P R L2 1 (cn n) i32 rfl rfl hn) hnt
  have mul : (product ty).denote (penv (ws P R L2)) = some (n*v) := by
    rw [product,den_binary,castn,rv]
    simpa [binaryValue] using Ty.convert_of_valid ty (n*v) hp
  have sum : (total ty).denote (penv (ws P R L2)) = none := by
    rw [total,den_binary,xx,mul]
    simp [binaryValue, Ty.convert, hb, hsg, hbad]
  simp only [R, L2] at sum
  rw [rawBody, pexec_seq, pexec_prim]
  simp [pstmt, sum]
end GenericSumAddApplyRaw

namespace GenericSumAddApplyCall
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


open GenericSumAddApplyRaw
open MemberPrepareGeneral
open Proofs.CppScalarValuePrepare
open Proofs.Mod61Body

abbrev i32 : Ty := ⟨32,true,false⟩

def gSumApply (ty : Ty) : NProgram :=
  ⟨[.scalar ty true true, .scalar ty false true, .scalar i32 false true], .unit, GenericSumAddApplyRaw.rawBody ty⟩
def gApplyFields (ty : Ty) : List Proofs.CppConstructorFinish.ScalarField := [⟨5,ty⟩,⟨6,i32⟩]
def gPerm (ty : Ty) (targetConst : Bool) : List (Proofs.CppScalar.Ty × Bool) :=
  [(ty,(true && (!targetConst || false))),(i32,(true && (!targetConst || false)))]
def gApplyView (ty : Ty) (fuel : Nat) (caller : NState) (arguments : List NArgument) (targetConst : Bool) :
    Proofs.CppLoop.Outcome (NState × Proofs.CppConstructorMultiFinish.ObjectRef) :=
  MemberView.constructViewFuel (gSumApply ty) fuel caller arguments [] (gApplyFields ty)
    (vectorPermissions targetConst) (gPerm ty targetConst)
def gApplyObjects (ty : Ty) (fuel : Nat) (caller : NState)
    (objects : List Proofs.CppConstructorMultiFinish.ObjectRef) (targetConst : Bool) :
    Proofs.CppLoop.Outcome (NState × Proofs.CppConstructorMultiFinish.ObjectRef) :=
  match MemberFactory.objectArguments caller [(false,[(ty,true)]),(true,[(ty,true),(i32,true)])] objects with
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
  (List.range 6).map fun i => ⟨P.length+i,true⟩
def fields (ty : Ty) (old x n : Int) : List Cell := [cx ty old,cn n,cx ty x,cn n,cx ty x,cn n]
structure StageState (ty : Ty) (caller initial callee : NState) (a : Nat) (old x n : Int) : Prop where
  scalar : QS callee [] caller.scalars.baseMemory (caller.scope+1)
    (callerP caller ++ fields ty old x n) (refs a ++ fieldBindings (callerP caller)) (ssl 7)
  frame : FA callee.frame caller.frame.state.liveSpace caller.frame.state.storage.work
    (caller.scope+1) caller.frame.state.storage.objects.length
  counters : Cq (scalarBound caller initial) (storageBound caller) (caller.scalars.work+21) callee
  contents : CppScalarContents.Contents caller.frame callee.frame
  xValid : ty.valid x = true
  nValid : i32.valid n = true

theorem stage_ready (caller : NState) (receiverSlot : Nat) (binding : CppState.Binding) (v x n : Int)
    (found : caller.scalarCell receiverSlot ty = some (binding,cx ty v))
    (writable : binding.writable = true)
    (hx : ty.valid x = true) (hn : i32.valid n = true) (hnt : ty.valid n = true)
    (hp : ty.valid (n*v) = true) (hs : ty.valid (x+n*v) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel callee, prepare caller (gSumApply ty).parameters
        [.scalarReference receiverSlot,.value (.literal ty x),.value (.literal i32 n)] = some initial ∧
      runFuel fuel (gSumApply ty).body initial = .finished ⟨callee,none,false⟩ ∧
      StageState ty caller initial callee binding.address x (x+n*v) n := by
  obtain ⟨initial,prepared,slots,mem,bindings,bas,scope,frame,work,peak⟩ :=
    prepare_references1_values2 caller (gSumApply ty).parameters ty ty i32 rfl
      receiverSlot binding v x n found writable hx hn valid
  obtain ⟨receiver,hv⟩ := caller_cell caller receiverSlot ty binding v found
  obtain ⟨r,ran,ret,cost,need,ps⟩ := GenericSumAddApplyRaw.raw_exec ty (callerP caller) binding.address v x n receiver hv hx hn hnt hp hs
  have qs : QS initial [] caller.scalars.baseMemory (caller.scope+1)
      (ws (callerP caller) (refs binding.address) [cx ty x,cn n]).mem
      (ws (callerP caller) (refs binding.address) [cx ty x,cn n]).bs (ssl 3) := by
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
  have hbase : caller.scalars.baseMemory ≤ (ws (callerP caller) (refs binding.address) [cx ty x,cn n]).mem.length := by
    simp [ws,callerP]; omega
  have run := sound (gSumApply ty).body (by simp [gSumApply, GenericSumAddApplyRaw.rawBody, GenericSumAddApplyRaw.total, GenericSumAddApplyRaw.product, Proofs.GenericLazy.castTo_scalar ty i32 (.variable i32 2) rfl, CppScalarContents.Allowed, Proofs.CppScalarFrame.Scalar, Scalar, NExpr.scalarOnly]) 1 _ r ran
    (L0:=caller.frame.state.liveSpace) (T0:=caller.frame.state.storage.work)
    (N:=caller.frame.state.storage.objects.length) (scq:=caller.scope+1)
    (SPB:=scalarBound caller initial) (TPB:=storageBound caller) (W:=initial.scalars.work)
    initial qs fa cq hbase
    (by simp [ws,refs]; unfold scalarBound; omega)
    (by unfold scalarBound; omega)
    (Nat.le_refl _) (by exact Nat.le_max_right _ _)
  obtain ⟨fuel,step,executed,returned,breaking,qsD,faD,cqD⟩ := run
  have typed : StageState ty caller initial step.state binding.address x (x+n*v) n := by
    refine ⟨?_,faD,?_,?_,hs,hn⟩
    · rw [ps] at qsD
      simpa [ws,resultCells,fields,fieldBindings,ssl,refs] using qsD
    · refine ⟨?_,cqD.scalarPeak,cqD.storagePeak,cqD.outerPeak⟩
      have bound := cqD.work
      rw [work] at bound
      omega
    · have stable := CppScalarContents.run_stable fuel (gSumApply ty).body initial step
        (by simp [gSumApply, GenericSumAddApplyRaw.rawBody, GenericSumAddApplyRaw.total, GenericSumAddApplyRaw.product, Proofs.GenericLazy.castTo_scalar ty i32 (.variable i32 2) rfl, CppScalarContents.Allowed, Proofs.CppScalarFrame.Scalar, Scalar, NExpr.scalarOnly]) (by intro owner c found; rw [frame] at found; have h := strict owner c found; rw [scope]; omega) executed
      have initialContents : CppScalarContents.Contents caller.frame initial.frame := by
        rw [frame]; exact ⟨rfl,rfl,rfl,rfl⟩
      exact initialContents.trans stable.contents
  refine ⟨initial,fuel,step.state,prepared,?_,typed⟩
  have stepEq : step = ⟨step.state,none,false⟩ := by
    cases step
    simp only [ret,Option.map_none] at returned
    simp_all
  exact executed.trans (congrArg (fun q : NStep => Proofs.CppLoop.Outcome.finished q) stepEq)
theorem stage_ready_conv (caller : NState) (receiverSlot : Nat) (binding : CppState.Binding) (v x n : Int)
    (found : caller.scalarCell receiverSlot ty = some (binding,cx ty v))
    (writable : binding.writable = true)
    (hx : ty.valid x = true) (hn : i32.valid n = true) (hnt : ty.valid n = true)
    (q s : Int) (hcp : ty.convert (n*v) = some q) (hcs : ty.convert (x+q) = some s)
    (hq : ty.valid q = true) (hs : ty.valid s = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel callee, prepare caller (gSumApply ty).parameters
        [.scalarReference receiverSlot,.value (.literal ty x),.value (.literal i32 n)] = some initial ∧
      runFuel fuel (gSumApply ty).body initial = .finished ⟨callee,none,false⟩ ∧
      StageState ty caller initial callee binding.address x s n := by
  obtain ⟨initial,prepared,slots,mem,bindings,bas,scope,frame,work,peak⟩ :=
    prepare_references1_values2 caller (gSumApply ty).parameters ty ty i32 rfl
      receiverSlot binding v x n found writable hx hn valid
  obtain ⟨receiver,hv⟩ := caller_cell caller receiverSlot ty binding v found
  obtain ⟨r,ran,ret,cost,need,ps⟩ := GenericSumAddApplyRaw.raw_exec_conv ty (callerP caller) binding.address v x n receiver hv hx hn hnt q s hcp hcs hq hs
  have qs : QS initial [] caller.scalars.baseMemory (caller.scope+1)
      (ws (callerP caller) (refs binding.address) [cx ty x,cn n]).mem
      (ws (callerP caller) (refs binding.address) [cx ty x,cn n]).bs (ssl 3) := by
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
  have hbase : caller.scalars.baseMemory ≤ (ws (callerP caller) (refs binding.address) [cx ty x,cn n]).mem.length := by
    simp [ws,callerP]; omega
  have run := sound (gSumApply ty).body (by simp [gSumApply, GenericSumAddApplyRaw.rawBody, GenericSumAddApplyRaw.total, GenericSumAddApplyRaw.product, Proofs.GenericLazy.castTo_scalar ty i32 (.variable i32 2) rfl, CppScalarContents.Allowed, Proofs.CppScalarFrame.Scalar, Scalar, NExpr.scalarOnly]) 1 _ r ran
    (L0:=caller.frame.state.liveSpace) (T0:=caller.frame.state.storage.work)
    (N:=caller.frame.state.storage.objects.length) (scq:=caller.scope+1)
    (SPB:=scalarBound caller initial) (TPB:=storageBound caller) (W:=initial.scalars.work)
    initial qs fa cq hbase
    (by simp [ws,refs]; unfold scalarBound; omega)
    (by unfold scalarBound; omega)
    (Nat.le_refl _) (by exact Nat.le_max_right _ _)
  obtain ⟨fuel,step,executed,returned,breaking,qsD,faD,cqD⟩ := run
  have typed : StageState ty caller initial step.state binding.address x s n := by
    refine ⟨?_,faD,?_,?_,hs,hn⟩
    · rw [ps] at qsD
      simpa [ws,resultCells,fields,fieldBindings,ssl,refs] using qsD
    · refine ⟨?_,cqD.scalarPeak,cqD.storagePeak,cqD.outerPeak⟩
      have bound := cqD.work
      rw [work] at bound
      omega
    · have stable := CppScalarContents.run_stable fuel (gSumApply ty).body initial step
        (by simp [gSumApply, GenericSumAddApplyRaw.rawBody, GenericSumAddApplyRaw.total, GenericSumAddApplyRaw.product, Proofs.GenericLazy.castTo_scalar ty i32 (.variable i32 2) rfl, CppScalarContents.Allowed, Proofs.CppScalarFrame.Scalar, Scalar, NExpr.scalarOnly]) (by intro owner c found; rw [frame] at found; have h := strict owner c found; rw [scope]; omega) executed
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
  scalarWork : out.scalars.work ≤ caller.scalars.work+24
  storageWork : out.frame.state.storage.work = caller.frame.state.storage.work
  scalarPeak : out.scalars.peak ≤ max caller.scalars.peak (scalarBound caller initial)
  storagePeak : out.frame.state.storage.peak ≤ storageBound caller
  outerPeak : out.peak ≤ max caller.peak
    (max caller.scalars.peak (scalarBound caller initial)+storageBound caller)
  contents : CppScalarContents.Contents caller.frame out.frame
  xValid : ty.valid x = true
  nValid : i32.valid n = true

theorem finish_export (old x n : Int) (a : Nat) (caller initial callee : NState) (targetConst : Bool)
    (ready : StageState ty caller initial callee a old x n)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    MemberView.finishView caller callee [] (gApplyFields ty)
        [] (gPerm ty targetConst) =
      some (exported ty x n caller callee targetConst,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
    ExportState ty x n caller initial (exported ty x n caller callee targetConst) targetConst := by
  have mem : callee.scalars.memory = callerP caller ++ (fields ty old x n) := by simpa using ready.scalar.memory
  have bs := ready.scalar.bindings
  have sl := ready.scalar.slots
  have c4 : callee.scalarCell 5 ty = some (⟨(callerP caller).length+4,true⟩,(cx ty x)) := by
    simp [NState.scalarCell,NState.scalarSlot,mem,bs,sl,fieldBindings,fields,refs,ssl,List.range_succ,cx,ready.xValid]
  have c5 : callee.scalarCell 6 i32 = some (⟨(callerP caller).length+5,true⟩,(cn n)) := by
    simp [NState.scalarCell,NState.scalarSlot,mem,bs,sl,fieldBindings,fields,refs,ssl,List.range_succ,cn,ready.nValid]
  have captured : Proofs.CppConstructorFinish.captureAll callee
      (gApplyFields ty) = some [((cx ty x),true),((cn n),true)] := by
    change Proofs.CppConstructorFinish.captureAll callee [⟨5,ty⟩,⟨6,i32⟩] = _
    simp [Proofs.CppConstructorFinish.captureAll,Proofs.CppConstructorFinish.capture,c4,c5]
  have viewed : Proofs.CppConstructorView.restrictValues [((cx ty x),true),((cn n),true)] (gPerm ty targetConst) =
      some (destinationValues ty x n targetConst) := by cases targetConst <;> simp [Proofs.CppConstructorView.restrictValues, gPerm, destinationValues, cx, cn]
  have takeM : callee.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [mem]; exact Proofs.MonoidCallCore.take_P caller (fields ty old x n)
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
  · change callee.scalars.work+0+(destinationValues ty x n targetConst).length+1 ≤ caller.scalars.work+24
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



theorem view_export_correct (caller : NState) (targetConst : Bool) (receiverSlot : Nat) (binding : CppState.Binding) (v x n : Int)
    (found : caller.scalarCell receiverSlot ty = some (binding,cx ty v))
    (writable : binding.writable = true)
    (hx : ty.valid x = true) (hn : i32.valid n = true) (hnt : ty.valid n = true)
    (hp : ty.valid (n*v) = true) (hs : ty.valid (x+n*v) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out, prepare caller (gSumApply ty).parameters
        [.scalarReference receiverSlot,.value (.literal ty x),.value (.literal i32 n)] = some initial ∧
      (gApplyView ty) fuel caller
        [.scalarReference receiverSlot,.value (.literal ty x),.value (.literal i32 n)] targetConst =
          .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
      ExportState ty (x+n*v) n caller initial out targetConst := by
  obtain ⟨initial,fuel,callee,prepared,ran,ready⟩ := stage_ready caller receiverSlot binding v x n
    found writable hx hn hnt hp hs valid lengths strict base
  obtain ⟨fin,post⟩ := finish_export x (x+n*v) n binding.address caller initial callee targetConst ready base
  refine ⟨initial,fuel,exported ty (x+n*v) n caller callee targetConst,prepared,?_,post⟩
  exact MemberView.constructView_of_steps (gSumApply ty) fuel caller initial callee _
    [.scalarReference receiverSlot,.value (.literal ty x),.value (.literal i32 n)] []
    (gApplyFields ty) [] (gPerm ty targetConst)
    (Proofs.CppConstructorMultiFinish.reference caller 0 2) none prepared ran (Or.inl rfl) fin

theorem object_export_correct (caller : NState) (targetConst : Bool)
    (receiverSlot xSlot nSlot : Nat) (binding bx bn : CppState.Binding) (v x n : Int)
    (found : caller.scalarCell receiverSlot ty = some (binding,cx ty v))
    (writable : binding.writable = true)
    (sourceX : caller.scalarCell xSlot ty = some (bx,cx ty x))
    (sourceN : caller.scalarCell nSlot i32 = some (bn,cn n))
    (hnt : ty.valid n = true) (hp : ty.valid (n*v) = true) (hs : ty.valid (x+n*v) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out,
      prepare caller (gSumApply ty).parameters
        [.scalarReference receiverSlot,.value (.literal ty x),.value (.literal i32 n)] = some initial ∧
      (gApplyObjects ty) fuel caller
        [⟨[],[receiverSlot]⟩,⟨[],[xSlot,nSlot]⟩] targetConst =
          .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
      ExportState ty (x+n*v) n caller initial out targetConst := by
  have hx := (caller_cell caller xSlot ty bx x sourceX).2
  have hn := (caller_cell caller nSlot i32 bn n sourceN).2
  obtain ⟨initial,fuel,out,prepared,ran,post⟩ := view_export_correct caller targetConst receiverSlot binding v x n
    found writable hx hn hnt hp hs valid lengths strict base
  have args : MemberFactory.objectArguments caller
      [(false,[(ty,true)]),(true,[(ty,true),(i32,true)])]
      [⟨[],[receiverSlot]⟩,⟨[],[xSlot,nSlot]⟩] =
        some [.scalarReference receiverSlot,.value (.literal ty x),.value (.literal i32 n)] := by
    simp [MemberFactory.objectArguments,MemberFactory.referenceFields,MemberFactory.valueFields,
      found,sourceX,sourceN,writable,cx,cn]
  refine ⟨initial,fuel,out,prepared,?_,post⟩
  change (match MemberFactory.objectArguments caller
    [(false,[(ty,true)]),(true,[(ty,true),(i32,true)])]
    [⟨[],[receiverSlot]⟩,⟨[],[xSlot,nSlot]⟩] with
    | none => Proofs.CppLoop.Outcome.fault
    | some arguments => (gApplyView ty) fuel caller arguments targetConst) = _
  rw [args]
  exact ran

theorem view_export_correct_conv (caller : NState) (targetConst : Bool) (receiverSlot : Nat) (binding : CppState.Binding) (v x n : Int)
    (found : caller.scalarCell receiverSlot ty = some (binding,cx ty v))
    (writable : binding.writable = true)
    (hx : ty.valid x = true) (hn : i32.valid n = true) (hnt : ty.valid n = true)
    (q s : Int) (hcp : ty.convert (n*v) = some q) (hcs : ty.convert (x+q) = some s)
    (hq : ty.valid q = true) (hs : ty.valid s = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out, prepare caller (gSumApply ty).parameters
        [.scalarReference receiverSlot,.value (.literal ty x),.value (.literal i32 n)] = some initial ∧
      (gApplyView ty) fuel caller
        [.scalarReference receiverSlot,.value (.literal ty x),.value (.literal i32 n)] targetConst =
          .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
      ExportState ty s n caller initial out targetConst := by
  obtain ⟨initial,fuel,callee,prepared,ran,ready⟩ := stage_ready_conv caller receiverSlot binding v x n
    found writable hx hn hnt q s hcp hcs hq hs valid lengths strict base
  obtain ⟨fin,post⟩ := finish_export x s n binding.address caller initial callee targetConst ready base
  refine ⟨initial,fuel,exported ty s n caller callee targetConst,prepared,?_,post⟩
  exact MemberView.constructView_of_steps (gSumApply ty) fuel caller initial callee _
    [.scalarReference receiverSlot,.value (.literal ty x),.value (.literal i32 n)] []
    (gApplyFields ty) [] (gPerm ty targetConst)
    (Proofs.CppConstructorMultiFinish.reference caller 0 2) none prepared ran (Or.inl rfl) fin

theorem object_export_correct_conv (caller : NState) (targetConst : Bool)
    (receiverSlot xSlot nSlot : Nat) (binding bx bn : CppState.Binding) (v x n : Int)
    (found : caller.scalarCell receiverSlot ty = some (binding,cx ty v))
    (writable : binding.writable = true)
    (sourceX : caller.scalarCell xSlot ty = some (bx,cx ty x))
    (sourceN : caller.scalarCell nSlot i32 = some (bn,cn n))
    (hnt : ty.valid n = true) (q s : Int) (hcp : ty.convert (n*v) = some q) (hcs : ty.convert (x+q) = some s)
    (hq : ty.valid q = true) (hs : ty.valid s = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out,
      prepare caller (gSumApply ty).parameters
        [.scalarReference receiverSlot,.value (.literal ty x),.value (.literal i32 n)] = some initial ∧
      (gApplyObjects ty) fuel caller
        [⟨[],[receiverSlot]⟩,⟨[],[xSlot,nSlot]⟩] targetConst =
          .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
      ExportState ty s n caller initial out targetConst := by
  have hx := (caller_cell caller xSlot ty bx x sourceX).2
  have hn := (caller_cell caller nSlot i32 bn n sourceN).2
  obtain ⟨initial,fuel,out,prepared,ran,post⟩ := view_export_correct_conv caller targetConst receiverSlot binding v x n
    found writable hx hn hnt q s hcp hcs hq hs valid lengths strict base
  have args : MemberFactory.objectArguments caller
      [(false,[(ty,true)]),(true,[(ty,true),(i32,true)])]
      [⟨[],[receiverSlot]⟩,⟨[],[xSlot,nSlot]⟩] =
        some [.scalarReference receiverSlot,.value (.literal ty x),.value (.literal i32 n)] := by
    simp [MemberFactory.objectArguments,MemberFactory.referenceFields,MemberFactory.valueFields,
      found,sourceX,sourceN,writable,cx,cn]
  refine ⟨initial,fuel,out,prepared,?_,post⟩
  change (match MemberFactory.objectArguments caller
    [(false,[(ty,true)]),(true,[(ty,true),(i32,true)])]
    [⟨[],[receiverSlot]⟩,⟨[],[xSlot,nSlot]⟩] with
    | none => Proofs.CppLoop.Outcome.fault
    | some arguments => (gApplyView ty) fuel caller arguments targetConst) = _
  rw [args]
  exact ran

/-- Unsigned products and sums wrap modulo `2^width`: the exported object holds the reduced values. -/
theorem object_export_wrap (caller : NState) (targetConst : Bool)
    (receiverSlot xSlot nSlot : Nat) (binding bx bn : CppState.Binding) (v x n : Int)
    (found : caller.scalarCell receiverSlot ty = some (binding,cx ty v))
    (writable : binding.writable = true)
    (sourceX : caller.scalarCell xSlot ty = some (bx,cx ty x))
    (sourceN : caller.scalarCell nSlot i32 = some (bn,cn n))
    (hnt : ty.valid n = true)
    (hb : ty.boolean = false) (hu : ty.signed = false)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out,
      prepare caller (gSumApply ty).parameters
        [.scalarReference receiverSlot,.value (.literal ty x),.value (.literal i32 n)] = some initial ∧
      (gApplyObjects ty) fuel caller
        [⟨[],[receiverSlot]⟩,⟨[],[xSlot,nSlot]⟩] targetConst =
          .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 2) ∧
      ExportState ty ((x + (n*v) % 2 ^ ty.width) % 2 ^ ty.width) n caller initial out targetConst := by
  have pos : (0 : Int) < 2 ^ ty.width := Int.pow_pos (by decide)
  have red (z : Int) : ty.convert z = some (z % 2 ^ ty.width) ∧ ty.valid (z % 2 ^ ty.width) = true := by
    have h0 : 0 ≤ z % 2 ^ ty.width := Int.emod_nonneg _ (by omega)
    have h1 : z % 2 ^ ty.width < 2 ^ ty.width := Int.emod_lt_of_pos _ pos
    exact ⟨by simp [Ty.convert, hb, hu], by simp [Ty.valid, hb, hu, h0, h1]⟩
  obtain ⟨cq, vq⟩ := red (n*v)
  obtain ⟨cs, vs⟩ := red (x + (n*v) % 2 ^ ty.width)
  exact object_export_correct_conv caller targetConst receiverSlot xSlot nSlot binding bx bn v x n found writable
    sourceX sourceN hnt _ _ cq cs vq vs valid lengths strict base

/-- A read-only receiver is rejected, for every type and caller. -/
theorem readonly_receiver_rejected (fuel : Nat) (caller : NState) (targetConst : Bool)
    (s1 : Nat) (b : CppState.Binding) (cell : Cell)
    (second : Proofs.CppConstructorMultiFinish.ObjectRef)
    (found : caller.scalarCell s1 ty = some (b,cell)) (readonly : b.writable = false) :
    gApplyObjects ty fuel caller [⟨[],[s1]⟩,second] targetConst = .fault := by
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
    (post : ExportState ty x n caller initial out targetConst) : out.work ≤ caller.work+24 := by
  have scalar := post.scalarWork
  have storage := post.storageWork
  simp only [NState.work]
  omega

end GenericSumAddApplyCall

