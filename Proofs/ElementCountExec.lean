import Proofs.FamilySteps
import Proofs.MultiVecDynamicScope
import Proofs.DynamicConstructRows
import Proofs.DoublingPrologue
import Proofs.RunLengthMath

/-!
Execution of the generated `element_count` body (`Proofs/Generated/ElementCount.lean`), for any element
type `ty` of the rows and any scalar expression `cv` that stores the `int` count into row 1 (the count
itself for `int`, its widening cast for `long long`).

State layout: vector slot 0 is the read-only input `v` (owner `V`), vector slot 1 the result `ret`
(owner `R`, rows `R+1` = firsts and `R+2` = counts); scalar slots 2..5 are `n`, `pre`, `cnt`, `i`.
-/

namespace Proofs.ElementCountExec
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedEval Proofs.CppNestedSim Proofs.CppNestedStmt Proofs.CppNestedHoare Proofs.CppNestedScope
open Proofs.CppNestedConstruct Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic
open Proofs.DynamicExpr Proofs.DynamicContents Proofs.RunLengthMath
open Proofs.CppState (Cell)
open Proofs.CppMixedInvoke (Location)

abbrev ti : Ty := ⟨32,true,false⟩
abbrev tu : Ty := ⟨64,false,false⟩
abbrev tb : Ty := ⟨1,false,true⟩

/-! ## The generated body -/

abbrev eN (ty : Ty) : NExpr := .cast ti (.size (.integer ty) (.local 0))
abbrev cZero : NExpr := .binary tb .eq (.variable ti 2) (.literal ti 0)
abbrev retC : Command := .sequence (.primitive (.retVector 1)) (.primitive .skip)
abbrev ePre (ty : Ty) : NExpr := .read ty (.local 0) (.cast tu (.literal ti 0))
abbrev cLoop : NExpr := .binary tb .lt (.variable ti 5) (.variable ti 2)
abbrev eAt (ty : Ty) : NExpr := .read ty (.local 0) (.cast tu (.variable ti 5))
abbrev cEq (ty : Ty) : NExpr := .binary tb .eq (.variable ty 3) (eAt ty)
abbrev incCnt : NStmt := .assign 4 ti (.binary ti .add (.variable ti 4) (.literal ti 1))
abbrev yesC : Command := .sequence (.scope (.sequence (.primitive incCnt) (.primitive .skip))) (.primitive .skip)
abbrev app0 (ty : Ty) : NStmt := .append (.row (.local 1) (.integer ty) (.literal tu 0)) ty (.variable ty 3)
abbrev app1 (ty : Ty) (cv : NExpr) : NStmt := .append (.row (.local 1) (.integer ty) (.literal tu 1)) ty cv
abbrev setPre (ty : Ty) : NStmt := .assign 3 ty (eAt ty)
abbrev setCnt : NStmt := .assign 4 ti (.literal ti 1)
abbrev noBody (ty : Ty) (cv : NExpr) : Command :=
  .sequence (.primitive (app0 ty)) (.sequence (.primitive (app1 ty cv))
    (.sequence (.primitive (setPre ty)) (.sequence (.primitive setCnt) (.primitive .skip))))
abbrev noC (ty : Ty) (cv : NExpr) : Command := .sequence (.scope (noBody ty cv)) (.primitive .skip)
abbrev incI : NStmt := .assign 5 ti (.binary ti .add (.variable ti 5) (.literal ti 1))
abbrev iterC (ty : Ty) (cv : NExpr) : Command :=
  .sequence (.scope (.sequence (.branch (cEq ty) yesC (noC ty cv)) (.primitive .skip)))
    (.sequence (.primitive incI) (.primitive .skip))
abbrev loopC (ty : Ty) (cv : NExpr) : Command :=
  .scope (.sequence (.primitive (.declare ti true (.literal ti 0)))
    (.sequence (.whileLoop cLoop (iterC ty cv)) (.primitive .skip)))
abbrev tailC (ty : Ty) (cv : NExpr) : Command :=
  .sequence (.primitive (app0 ty)) (.sequence (.primitive (app1 ty cv))
    (.sequence (.primitive (.retVector 1)) (.primitive .skip)))
abbrev body (ty : Ty) (cv : NExpr) : Command :=
  .sequence (.primitive (.constructRows ty true (.literal tu 2)))
  (.sequence (.primitive (.declare ti true (eN ty)))
  (.sequence (.branch cZero retC (.primitive .skip))
  (.sequence (.primitive (.declare ty true (ePre ty)))
  (.sequence (.primitive (.declare ti true (.literal ti 0)))
  (.sequence (loopC ty cv) (tailC ty cv))))))

/-! ## Fixed data of one call -/

/-- The input parameter (vector slot 0) and the result root (vector slot 1). -/
def pv (ty : Ty) (V vsc : Nat) (mV : Bool) : Parameter := ⟨0,V,.integer ty,vsc,false,mV⟩
def pr (ty : Ty) (R sc : Nat) : Parameter := ⟨1,R,.vector (.integer ty),sc,true,true⟩

/-- The heap once the result holds the rows `U` (firsts) and `Y` (counts). -/
def heapOf (h0 : Heap) (ty : Ty) (R sc : Nat) (U Y : List Int) : Heap :=
  put h0 R (.rows ty sc (rowIds R 2) 0 [U,Y])

def slotsN : List Location := [.vector 0,.vector 1,.scalar 0]
def slotsP : List Location := slotsN ++ [.scalar 1]
def slotsC : List Location := slotsP ++ [.scalar 2]
def slotsI : List Location := slotsC ++ [.scalar 3]

def bindsN (P : List Cell) : List CppState.Binding := [⟨P.length,true⟩]
def bindsP (P : List Cell) : List CppState.Binding := bindsN P ++ [⟨P.length+1,true⟩]
def bindsC (P : List Cell) : List CppState.Binding := bindsP P ++ [⟨P.length+2,true⟩]
def bindsI (P : List Cell) : List CppState.Binding := bindsC P ++ [⟨P.length+3,true⟩]

def cellsI (ty : Ty) (n : Nat) (pre : Int) (cnt t : Nat) : List Cell :=
  [⟨ti,(n : Int)⟩,⟨ty,pre⟩,⟨ti,(cnt : Int)⟩,⟨ti,(t : Int)⟩]

/-- The scalar layout of a state. -/
structure Sh (s : NState) (P : List Cell) (B : Nat) (slots : List Location) (cells : List Cell)
    (binds : List CppState.Binding) (scope : Nat) : Prop where
  slots : s.slots = slots
  memory : s.scalars.memory = P ++ cells
  bindings : s.scalars.bindings = binds
  base : s.scalars.baseMemory = B
  scope : s.scope = scope

theorem i32_valid_nat (n : Nat) (small : n < 2147483648) : ti.valid (n : Int) = true := by
  simp [Ty.valid]; omega

/-- The loop-state scalar environment. -/
theorem envI {s : NState} {P : List Cell} {B scope : Nat} {ty : Ty} {n : Nat} {pre : Int} {cnt t : Nat}
    (sh : Sh s P B slotsI (cellsI ty n pre cnt t) (bindsI P) scope)
    (hn : n < 2147483648) (hpre : ty.valid pre = true) (hc : cnt < 2147483648) (ht : t < 2147483648) :
    envOf s 2 ti = some (n : Int) ∧ envOf s 3 ty = some pre ∧ envOf s 4 ti = some (cnt : Int) ∧
      envOf s 5 ti = some (t : Int) := by
  refine ⟨?_,?_,?_,?_⟩
  · exact Proofs.DoublingNested.envOf_at s 2 0 ⟨P.length,true⟩ ti _ (by simp [sh.slots,slotsI,slotsC,slotsP,slotsN])
      (by simp [sh.bindings,bindsI,bindsC,bindsP,bindsN]) (by simp [sh.memory,cellsI]) (i32_valid_nat n hn)
  · exact Proofs.DoublingNested.envOf_at s 3 1 ⟨P.length+1,true⟩ ty _ (by simp [sh.slots,slotsI,slotsC,slotsP,slotsN])
      (by simp [sh.bindings,bindsI,bindsC,bindsP,bindsN]) (by simp [sh.memory,cellsI]) hpre
  · exact Proofs.DoublingNested.envOf_at s 4 2 ⟨P.length+2,true⟩ ti _ (by simp [sh.slots,slotsI,slotsC,slotsP,slotsN])
      (by simp [sh.bindings,bindsI,bindsC,bindsP,bindsN]) (by simp [sh.memory,cellsI]) (i32_valid_nat cnt hc)
  · exact Proofs.DoublingNested.envOf_at s 5 3 ⟨P.length+3,true⟩ ti _ (by simp [sh.slots,slotsI,slotsC,slotsP,slotsN])
      (by simp [sh.bindings,bindsI,bindsC,bindsP,bindsN]) (by simp [sh.memory,cellsI]) (i32_valid_nat t ht)

/-! ## Pure denotations of the vector reads -/

theorem find_pv (ty : Ty) (V vsc : Nat) (mV : Bool) (rest : List Parameter) :
    (pv ty V vsc mV :: rest).find? (fun q => q.slot == 0) = some (pv ty V vsc mV) := by
  simp [pv]

theorem erase_input (h0 : Heap) (ty : Ty) (R sc V vsc : Nat) (X U Y : List Int)
    (input : h0 V = some (.flat ty vsc X)) (different : V ≠ R) :
    eraseHeap (heapOf h0 ty R sc U Y) V = some (.flat ty vsc X) := by
  simp [eraseHeap,heapOf,put,different,input,erase]

theorem denote_read (ty : Ty) (V vsc : Nat) (mV : Bool) (rest : List Parameter) (l : Locals) (hc : ContentsHeap)
    (X : List Int) (idx : NExpr) (j : Nat) (x : Int)
    (location : l.slots[0]? = some (.vector 0)) (input : hc V = some (.flat ty vsc X))
    (idxValue : denote (pv ty V vsc mV :: rest) l hc idx = some (j : Int)) (item : X[j]? = some x)
    (valid : ty.valid x = true) :
    denote (pv ty V vsc mV :: rest) l hc (.read ty (.local 0) idx) = some x :=
  read_root _ l hc 0 (pv ty V vsc mV) ty vsc j X idx x location (find_pv ty V vsc mV rest) input rfl rfl
    idxValue item valid

theorem u64_valid_small (k : Nat) (small : k < 2147483648) : (⟨64,false,false⟩ : Ty).valid (k : Int) = true := by
  simp [Ty.valid]; omega

theorem denote_size (ty : Ty) (V vsc : Nat) (mV : Bool) (rest : List Parameter) (l : Locals) (hc : ContentsHeap)
    (X : List Int) (location : l.slots[0]? = some (.vector 0)) (input : hc V = some (.flat ty vsc X))
    (small : X.length < 2147483648) :
    denote (pv ty V vsc mV :: rest) l hc (eN ty) = some (X.length : Int) := by
  have size := size_root _ l hc 0 (pv ty V vsc mV) (.flat ty vsc X) location (find_pv ty V vsc mV rest) input rfl rfl
  rw [show (Contents.flat ty vsc X).length = X.length from rfl,
    show (Contents.flat ty vsc X).element = .integer ty from rfl,u64_valid_small _ small,if_pos rfl] at size
  rw [DynamicExprLaws.cast_eq,size,Option.bind_some]
  exact Ty.convert_of_valid _ _ (i32_valid_nat _ small)

/-- A binary expression whose left operand is scalar. -/
theorem denote_binary_left (params : List Parameter) (l : Locals) (hc : ContentsHeap) (ty : Ty) (op : Binary)
    (left right : NExpr) (a b v : Int) (scalarLeft : left.scalarOnly = true)
    (leftValue : left.denote (environment l) = some a) (rightValue : denote params l hc right = some b)
    (converted : ty.convert (binaryValue op a b) = some v) :
    denote params l hc (.binary ty op left right) = some v := by
  rw [DynamicExprLaws.binary_eq,denote_scalar params l hc left scalarLeft,leftValue,Option.bind_some,rightValue,
    Option.bind_some]
  exact converted

/-! ## The data fixed for one call, and the storage invariant -/

structure Fix where
  ty : Ty
  cv : NExpr
  X : List Int
  P : List Cell
  B : Nat
  V : Nat
  vsc : Nat
  mV : Bool
  sc : Nat
  R : Nat
  h0 : Heap
  /-- Live space, storage work and storage baseline just after `ret` is constructed. -/
  Lc : Nat
  Tc : Nat
  base : Nat
  /-- Bounds of the scalar and the storage peak. -/
  SPB : Nat
  TPB : Nat

structure FixOK (F : Fix) : Prop where
  input : F.h0 F.V = some (.flat F.ty F.vsc F.X)
  vr : F.V < F.R
  small : F.X.length < 2147483647
  valid : ∀ x ∈ F.X, F.ty.valid x = true
  counts : ∀ c : Int, ti.valid c = true → F.ty.valid c = true
  supported : CppVectorBindings.supported F.ty
  cvScalar : F.cv.scalarOnly = true
  cvValue : ∀ (env : Nat → Ty → Option Int) (c : Int), env 4 ti = some c → ti.valid c = true →
    F.cv.denote env = some c
  cvNodes : F.cv.nodes ≤ 2
  room : 2147483648 ≤ CppVectorBindings.sizeLimit F.ty
  baseLe : F.B ≤ F.P.length
  spb : F.P.length+8-F.B+40 ≤ F.SPB
  tpb : F.Lc+8*F.X.length+10-F.base ≤ F.TPB

def Fix.params (F : Fix) : List Parameter := [pv F.ty F.V F.vsc F.mV,pr F.ty F.R F.sc]

/-- The closed runs `C` as the two rows of `ret`. -/
def firsts (C : List (Int × Nat)) : List Int := C.map Prod.fst
def seconds (C : List (Int × Nat)) : List Int := C.map fun p => (p.2 : Int)

def Fix.heap (F : Fix) (C : List (Int × Nat)) : Heap := heapOf F.h0 F.ty F.R F.sc (firsts C) (seconds C)

/-- Storage while `ret` holds the closed runs `C`: the Family, the two row buffers with their capacities,
and the amortised storage work. -/
structure St (F : Fix) (s : NState) (C : List (Int × Nat)) : Prop where
  family : Family F.params (F.heap C) s.frame (resources s.frame)
  bufs : ∃ b0 b1 : Buffer Value, s.frame.state.storage.lookup (F.R+1) = some b0 ∧
    s.frame.state.storage.lookup (F.R+2) = some b1 ∧
    b0.items = (firsts C).map Value.integer ∧ b1.items = (seconds C).map Value.integer ∧
    b0.capacity ≤ 2*C.length+1 ∧ b1.capacity ≤ 2*C.length+1 ∧
    b0.limit = CppVectorBindings.sizeLimit F.ty ∧ b1.limit = CppVectorBindings.sizeLimit F.ty ∧
    s.frame.state.liveSpace = F.Lc+b0.capacity+b1.capacity ∧
    s.frame.state.storage.work+CppVectorGrowth.potential b0+CppVectorGrowth.potential b1 ≤ F.Tc+10*C.length
  base : s.frame.state.storage.baseSpace = F.base
  context : ∀ o c, s.frame.state.forest.context o = some c → c ≤ F.sc
  frameBindings : s.frame.bindings.length = 2
  storagePeak : s.frame.state.storage.peak ≤ F.TPB

/-- The scalar and outer peak bounds. -/
structure Cb (F : Fix) (s : NState) : Prop where
  scalarPeak : s.scalars.peak ≤ F.SPB
  peak : s.peak ≤ F.SPB+F.TPB

theorem put_put (h : Heap) (root : Nat) (a b : View) : put (put h root a) root b = put h root b := by
  funext o; by_cases e : o = root <;> simp [put,e]

theorem vectorSlot_ret {s : NState} (slots : s.slots[1]? = some (.vector 1)) : s.vectorSlot 1 = some 1 := by
  simp [NState.vectorSlot,slots]

theorem pr_mem (F : Fix) : pr F.ty F.R F.sc ∈ F.params := by simp [Fix.params]

theorem heap_ret (F : Fix) (C : List (Int × Nat)) :
    F.heap C (pr F.ty F.R F.sc).owner = some (.rows F.ty F.sc (rowIds F.R 2) 0 [firsts C,seconds C]) := by
  simp [Fix.heap,heapOf,put,pr]

theorem potential_le {α : Type} (b : Buffer α) : CppVectorGrowth.potential b ≤ 2*b.items.length := by
  unfold CppVectorGrowth.potential; split <;> omega

/-- `ret.emplace_back` of the first field into row 0, as part of closing the run `(x, c)`. -/
theorem append0 (F : Fix) (ok : FixOK F) (s : NState) (C : List (Int × Nat)) (x : Int)
    (st : St F s C) (cb : Cb F s) (slots : s.slots[1]? = some (.vector 1))
    (vValue : (NExpr.variable F.ty 3).denote (envOf s) = some x) (accepted : F.ty.valid x = true)
    (len : C.length < F.X.length) (live : liveS s+6 ≤ F.SPB) :
    ∃ t b0 b1 : _, (app0 F.ty).run s = some ⟨t,none,false⟩ ∧
      Family F.params (heapOf F.h0 F.ty F.R F.sc (firsts C ++ [x]) (seconds C)) t.frame (resources t.frame) ∧
      t.frame.state.storage.lookup (F.R+1) = some b0 ∧ t.frame.state.storage.lookup (F.R+2) = some b1 ∧
      b0.items = (firsts C ++ [x]).map Value.integer ∧ b1.items = (seconds C).map Value.integer ∧
      b0.capacity ≤ 2*(C.length+1)+1 ∧ b1.capacity ≤ 2*C.length+1 ∧
      b0.limit = CppVectorBindings.sizeLimit F.ty ∧ b1.limit = CppVectorBindings.sizeLimit F.ty ∧
      t.frame.state.liveSpace = F.Lc+b0.capacity+b1.capacity ∧
      t.frame.state.storage.work+CppVectorGrowth.potential b0+CppVectorGrowth.potential b1 ≤ F.Tc+10*C.length+5 ∧
      t.frame.state.storage.baseSpace = F.base ∧ t.frame.state.forest = s.frame.state.forest ∧
      t.frame.bindings = s.frame.bindings ∧ t.frame.state.storage.peak ≤ F.TPB ∧
      t.slots = s.slots ∧ t.scope = s.scope ∧ t.scalars.memory = s.scalars.memory ∧
      t.scalars.bindings = s.scalars.bindings ∧ t.scalars.baseMemory = s.scalars.baseMemory ∧
      s.scalars.work ≤ t.scalars.work ∧ t.scalars.work ≤ s.scalars.work+5 ∧ Cb F t := by
  obtain ⟨b0,b1,f0,f1,i0,i1,c0,c1,l0,l1,lv,wk⟩ := st.bufs
  have b0len : b0.items.length = C.length := by rw [i0]; simp [firsts]
  have room : b0.items.length < b0.limit := by
    rw [b0len,l0]; have := ok.room; have := ok.small; omega
  obtain ⟨r,t,run,family,wl,wu,amort,peak,cap,items,limit,self,other,objs,forest,fb,rights,sl,sc',me,bi,ba,pl,pu,ql,qu⟩ :=
    AppendCapacity.appendChild_stmt s F.params (F.heap C) (resources s.frame) st.family (pr F.ty F.R F.sc) (pr_mem F) 1
      (vectorSlot_ret slots) F.ty F.sc (rowIds F.R 2) 0 [firsts C,seconds C] (heap_ret F C) rfl rfl
      (.literal tu 0) (.variable F.ty 3) 0 (F.R+1) x (by simp [NExpr.scalarOnly]) (by simp [NExpr.denote,Ty.valid])
      (by simp [NExpr.scalarOnly]) vValue (by simp [rowIds]) b0 f0 accepted room
  have measured := family.measured
  have fam : Family F.params (heapOf F.h0 F.ty F.R F.sc (firsts C ++ [x]) (seconds C)) t.frame (resources t.frame) := by
    have := DynamicAllocateFamily.Family.remeasured family
    simpa [Fix.heap,heapOf,put_put,pr] using this
  have b1Same : t.frame.state.storage.lookup (F.R+2) = some b1 := by rw [other (F.R+2) (by omega)]; exact f1
  have liveT : t.frame.state.liveSpace = s.frame.state.liveSpace+r.buffer.capacity-b0.capacity := measured.live
  have workT : t.frame.state.storage.work = s.frame.state.storage.work+r.work := measured.work
  have peakT : t.frame.state.storage.peak = max s.frame.state.storage.peak
      (s.frame.state.liveSpace+(r.peak-(b0.capacity+1))-s.frame.state.storage.baseSpace) := measured.peak
  have baseT : t.frame.state.storage.baseSpace = s.frame.state.storage.baseSpace := measured.base
  have lenC : (firsts C).length = C.length := by simp [firsts]
  have tpT : t.frame.state.storage.peak ≤ F.TPB := by
    rw [peakT]
    have := st.storagePeak
    have := ok.tpb
    rw [st.base]
    omega
  refine ⟨t,r.buffer,b1,run,fam,self,b1Same,?_,i1,?_,c1,limit.trans l0,l1,?_,?_,by rw [baseT,st.base],forest,fb,tpT,
    sl,sc',me,bi,ba,wl,by simpa [NExpr.nodes] using wu,?_⟩
  · rw [items,i0]; simp [firsts]
  · rw [b0len] at cap; omega
  · rw [liveT,lv]; omega
  · rw [workT]
    have := potential_le b0
    omega
  · refine ⟨?_,?_⟩
    · have := cb.scalarPeak; simp [NExpr.nodes] at pu; omega
    · have := cb.peak; have := cb.scalarPeak; simp [NExpr.nodes] at pu; omega

/-- `ret.emplace_back` of the count into row 1: the run `(x, c)` is closed. -/
theorem append1 (F : Fix) (ok : FixOK F) (s : NState) (C : List (Int × Nat)) (x : Int) (c : Nat) (b0 b1 : Buffer Value)
    (family : Family F.params (heapOf F.h0 F.ty F.R F.sc (firsts C ++ [x]) (seconds C)) s.frame (resources s.frame))
    (f0 : s.frame.state.storage.lookup (F.R+1) = some b0) (f1 : s.frame.state.storage.lookup (F.R+2) = some b1)
    (i0 : b0.items = (firsts C ++ [x]).map Value.integer) (i1 : b1.items = (seconds C).map Value.integer)
    (c0 : b0.capacity ≤ 2*(C.length+1)+1) (c1 : b1.capacity ≤ 2*C.length+1)
    (l0 : b0.limit = CppVectorBindings.sizeLimit F.ty) (l1 : b1.limit = CppVectorBindings.sizeLimit F.ty)
    (lv : s.frame.state.liveSpace = F.Lc+b0.capacity+b1.capacity)
    (wk : s.frame.state.storage.work+CppVectorGrowth.potential b0+CppVectorGrowth.potential b1 ≤ F.Tc+10*C.length+5)
    (base : s.frame.state.storage.baseSpace = F.base)
    (context : ∀ o k, s.frame.state.forest.context o = some k → k ≤ F.sc)
    (fbl : s.frame.bindings.length = 2) (tp : s.frame.state.storage.peak ≤ F.TPB)
    (cb : Cb F s) (slots : s.slots[1]? = some (.vector 1))
    (cValue : envOf s 4 ti = some (c : Int)) (cSmall : c < 2147483648)
    (len : C.length < F.X.length) (live : liveS s+7 ≤ F.SPB) :
    ∃ t, (app1 F.ty F.cv).run s = some ⟨t,none,false⟩ ∧ St F t (C ++ [(x,c)]) ∧
      t.frame.state.forest = s.frame.state.forest ∧ t.frame.bindings = s.frame.bindings ∧
      t.slots = s.slots ∧ t.scope = s.scope ∧ t.scalars.memory = s.scalars.memory ∧
      t.scalars.bindings = s.scalars.bindings ∧ t.scalars.baseMemory = s.scalars.baseMemory ∧
      s.scalars.work ≤ t.scalars.work ∧ t.scalars.work ≤ s.scalars.work+6 ∧ Cb F t := by
  have b1len : b1.items.length = C.length := by rw [i1]; simp [seconds]
  have room : b1.items.length < b1.limit := by
    rw [b1len,l1]; have := ok.room; have := ok.small; omega
  have cvalid : ti.valid (c : Int) = true := i32_valid_nat c cSmall
  obtain ⟨r,t,run,fam,wl,wu,amort,peak,cap,items,limit,self,other,objs,forest,fb,rights,sl,sc',me,bi,ba,pl,pu,ql,qu⟩ :=
    AppendCapacity.appendChild_stmt s F.params (heapOf F.h0 F.ty F.R F.sc (firsts C ++ [x]) (seconds C))
      (resources s.frame) family (pr F.ty F.R F.sc) (pr_mem F) 1
      (vectorSlot_ret slots) F.ty F.sc (rowIds F.R 2) 0 [firsts C ++ [x],seconds C]
      (by simp [heapOf,put,pr]) rfl rfl
      (.literal tu 1) F.cv 1 (F.R+2) (c : Int) (by simp [NExpr.scalarOnly]) (by simp [NExpr.denote,Ty.valid])
      ok.cvScalar (ok.cvValue (envOf s) (c : Int) cValue cvalid) (by simp [rowIds]) b1 f1 (ok.counts _ cvalid) room
  have measured := fam.measured
  have famT : Family F.params (F.heap (C ++ [(x,c)])) t.frame (resources t.frame) := by
    have := DynamicAllocateFamily.Family.remeasured fam
    simpa [Fix.heap,heapOf,put_put,pr,firsts,seconds] using this
  have b0Same : t.frame.state.storage.lookup (F.R+1) = some b0 := by rw [other (F.R+1) (by omega)]; exact f0
  have liveT : t.frame.state.liveSpace = s.frame.state.liveSpace+r.buffer.capacity-b1.capacity := measured.live
  have workT : t.frame.state.storage.work = s.frame.state.storage.work+r.work := measured.work
  have peakT : t.frame.state.storage.peak = max s.frame.state.storage.peak
      (s.frame.state.liveSpace+(r.peak-(b1.capacity+1))-s.frame.state.storage.baseSpace) := measured.peak
  have baseT : t.frame.state.storage.baseSpace = s.frame.state.storage.baseSpace := measured.base
  have tpT : t.frame.state.storage.peak ≤ F.TPB := by
    rw [peakT]
    have := ok.tpb
    rw [base]
    omega
  have nodes := ok.cvNodes
  refine ⟨t,run,⟨famT,⟨b0,r.buffer,b0Same,self,?_,?_,?_,?_,l0,limit.trans l1,?_,?_⟩,by rw [baseT,base],
    by rw [forest]; exact context,by rw [fb]; exact fbl,tpT⟩,forest,fb,sl,sc',me,bi,ba,wl,
    by simp [NExpr.nodes] at wu; omega,?_⟩
  · rw [i0]; simp [firsts]
  · rw [items,i1]; simp [seconds]
  · simp; omega
  · rw [b1len] at cap; simp; omega
  · rw [liveT,lv]; omega
  · rw [workT]
    have := potential_le b1
    simp; omega
  · refine ⟨?_,?_⟩
    · have := cb.scalarPeak; simp [NExpr.nodes] at pu; omega
    · have := cb.peak; have := cb.scalarPeak; simp [NExpr.nodes] at pu; omega

theorem set_pre (P : List Cell) (ty : Ty) (n : Nat) (pre x : Int) (cnt t : Nat) :
    (P ++ cellsI ty n pre cnt t).set (P.length+1) ⟨ty,x⟩ = P ++ cellsI ty n x cnt t := by
  rw [List.set_append_right _ _ (by omega)]; simp [cellsI]

theorem set_cnt (P : List Cell) (ty : Ty) (n : Nat) (pre : Int) (cnt t c : Nat) :
    (P ++ cellsI ty n pre cnt t).set (P.length+2) ⟨ti,(c : Int)⟩ = P ++ cellsI ty n pre c t := by
  rw [List.set_append_right _ _ (by omega)]; simp [cellsI]

theorem set_i (P : List Cell) (ty : Ty) (n : Nat) (pre : Int) (cnt t c : Nat) :
    (P ++ cellsI ty n pre cnt t).set (P.length+3) ⟨ti,(c : Int)⟩ = P ++ cellsI ty n pre cnt c := by
  rw [List.set_append_right _ _ (by omega)]; simp [cellsI]

theorem liveS_sh {s : NState} {P : List Cell} {B : Nat} {slots : List Location} {cells : List Cell}
    {binds : List CppState.Binding} {scope : Nat} (sh : Sh s P B slots cells binds scope) :
    liveS s = P.length+cells.length-B+binds.length := by
  simp [liveS,sh.memory,sh.bindings,sh.base]

theorem live_loop {s : NState} {F : Fix} {ty : Ty} {n : Nat} {pre : Int} {cnt t scope : Nat}
    (sh : Sh s F.P F.B slotsI (cellsI ty n pre cnt t) (bindsI F.P) scope) (ok : FixOK F) :
    liveS s+40 ≤ F.SPB := by
  rw [liveS_sh sh]; have := ok.spb; have := ok.baseLe; simp [cellsI,bindsI,bindsC,bindsP,bindsN]; omega

/-- The value `v[t]` read through slot 5. -/
theorem denote_at (F : Fix) (ok : FixOK F) (s : NState) (C : List (Int × Nat)) (t : Nat) (x : Int)
    (slots : s.slots[0]? = some (.vector 0)) (it : envOf s 5 ti = some (t : Int)) (item : F.X[t]? = some x) :
    denote F.params (snapshot s) (eraseHeap (F.heap C)) (eAt F.ty) = some x := by
  have inside := (List.getElem?_eq_some_iff.mp item).1
  have small := ok.small
  have tv : tu.valid (t : Int) = true := by simp [Ty.valid]; omega
  apply denote_read F.ty F.V F.vsc F.mV _ (snapshot s) _ F.X _ t x (by simpa [snapshot] using slots)
    (erase_input F.h0 F.ty F.R F.sc F.V F.vsc F.X _ _ ok.input (by have := ok.vr; omega))
  · rw [denote_scalar _ _ _ _ (by simp [NExpr.scalarOnly]),snapshot_env]
    simp [NExpr.denote,it,Ty.convert_of_valid _ _ tv]
  · exact item
  · exact ok.valid x (List.mem_of_getElem? item)

/-- The body of the `else` branch: close the run `(pre, cnt)` and start the run of `v[t]`. -/
theorem noBody_run (F : Fix) (ok : FixOK F) (S : NState) (C : List (Int × Nat)) (pre : Int) (cnt t : Nat) (x : Int)
    (sh : Sh S F.P F.B slotsI (cellsI F.ty F.X.length pre cnt t) (bindsI F.P) (F.sc+3))
    (st : St F S C) (cb : Cb F S) (hpre : F.ty.valid pre = true) (hc : cnt < 2147483648) (ht : t < F.X.length)
    (len : C.length < F.X.length) (item : F.X[t]? = some x) :
    ∃ T, (∀ Q : NStep → Prop, Q ⟨T,none,false⟩ → RunsTo (noBody F.ty F.cv) S Q) ∧
      Sh T F.P F.B slotsI (cellsI F.ty F.X.length x 1 t) (bindsI F.P) (F.sc+3) ∧ St F T (C ++ [(pre,cnt)]) ∧
      Cb F T ∧ T.frame.state.forest = S.frame.state.forest ∧ T.frame.bindings = S.frame.bindings ∧
      S.scalars.work ≤ T.scalars.work ∧ T.scalars.work ≤ S.scalars.work+40 := by
  have small := ok.small
  obtain ⟨en,ep,ec,ei⟩ := envI sh (by omega) hpre hc (by omega)
  have live := live_loop sh ok
  have slot1 : S.slots[1]? = some (.vector 1) := by simp [sh.slots,slotsI,slotsC,slotsP,slotsN]
  -- row 0
  obtain ⟨t1,b0,b1,run1,fam1,f0,f1,i0,i1,c0,c1,l0,l1,lv,wk,base1,forest1,fb1,tp1,sl1,sc1,me1,bi1,ba1,wl1,wu1,cb1⟩ :=
    append0 F ok S C pre st cb slot1 (by simpa [NExpr.denote] using ep) hpre len (by omega)
  have sh1 : Sh t1 F.P F.B slotsI (cellsI F.ty F.X.length pre cnt t) (bindsI F.P) (F.sc+3) :=
    ⟨by rw [sl1]; exact sh.slots,by rw [me1]; exact sh.memory,by rw [bi1]; exact sh.bindings,
      by rw [ba1]; exact sh.base,by rw [sc1]; exact sh.scope⟩
  have ec1 : envOf t1 4 ti = some (cnt : Int) := (envI sh1 (by omega) hpre hc (by omega)).2.2.1
  -- row 1
  obtain ⟨t2,run2,st2,forest2,fb2,sl2,sc2,me2,bi2,ba2,wl2,wu2,cb2⟩ :=
    append1 F ok t1 C pre cnt b0 b1 fam1 f0 f1 i0 i1 c0 c1 l0 l1 lv wk base1
      (by rw [forest1]; exact st.context) (by rw [fb1]; exact st.frameBindings) tp1 cb1
      (by rw [sl1]; exact slot1) ec1 hc len (by rw [liveS_sh sh1]; rw [liveS_sh sh] at live; omega)
  have sh2 : Sh t2 F.P F.B slotsI (cellsI F.ty F.X.length pre cnt t) (bindsI F.P) (F.sc+3) :=
    ⟨by rw [sl2]; exact sh1.slots,by rw [me2]; exact sh1.memory,by rw [bi2]; exact sh1.bindings,
      by rw [ba2]; exact sh1.base,by rw [sc2]; exact sh1.scope⟩
  -- pre = v[t]
  have ei2 : envOf t2 5 ti = some (t : Int) := (envI sh2 (by omega) hpre hc (by omega)).2.2.2
  obtain ⟨t3,run3,fam3,state3,rights3,fb3,sl3,sc3,me3,bi3,ba3,wl3,wu3,pl3,pu3,ql3,qu3⟩ :=
    FamilySteps.assign st2.family (eAt F.ty) 3 1 F.ty x x ⟨F.P.length+1,true⟩ ⟨F.ty,pre⟩
      (denote_at F ok t2 _ t x (by simp [sh2.slots,slotsI,slotsC,slotsP,slotsN]) ei2 item)
      (Ty.convert_of_valid _ _ (ok.valid x (List.mem_of_getElem? item)))
      (by simp [sh2.slots,slotsI,slotsC,slotsP,slotsN]) (by simp [sh2.bindings,bindsI,bindsC,bindsP,bindsN])
      (by simp [sh2.memory,cellsI]) rfl hpre rfl
  have sh3 : Sh t3 F.P F.B slotsI (cellsI F.ty F.X.length x cnt t) (bindsI F.P) (F.sc+3) :=
    ⟨by rw [sl3]; exact sh2.slots,by rw [me3,sh2.memory,set_pre],by rw [bi3]; exact sh2.bindings,
      by rw [ba3]; exact sh2.base,by rw [sc3]; exact sh2.scope⟩
  -- cnt = 1
  obtain ⟨t4,run4,fam4,state4,rights4,fb4,sl4,sc4,me4,bi4,ba4,wl4,wu4,pl4,pu4,ql4,qu4⟩ :=
    FamilySteps.assign fam3 (.literal ti 1) 4 2 ti 1 1 ⟨F.P.length+2,true⟩ ⟨ti,(cnt : Int)⟩
      (by rw [denote_scalar _ _ _ _ (by simp [NExpr.scalarOnly])]; simp [NExpr.denote,Ty.valid])
      (Ty.convert_of_valid _ _ (by simp [Ty.valid]))
      (by simp [sh3.slots,slotsI,slotsC,slotsP,slotsN]) (by simp [sh3.bindings,bindsI,bindsC,bindsP,bindsN])
      (by simp [sh3.memory,cellsI]) rfl (i32_valid_nat cnt hc) rfl
  have sh4 : Sh t4 F.P F.B slotsI (cellsI F.ty F.X.length x 1 t) (bindsI F.P) (F.sc+3) :=
    ⟨by rw [sl4]; exact sh3.slots,by rw [me4,sh3.memory]; exact set_cnt F.P F.ty _ x cnt t 1,
      by rw [bi4]; exact sh3.bindings,by rw [ba4]; exact sh3.base,by rw [sc4]; exact sh3.scope⟩
  have st3 : St F t3 (C ++ [(pre,cnt)]) := by
    obtain ⟨fam,bufs,base,context,fbl,tp⟩ := st2
    refine ⟨?_,?_,by rw [state3]; exact base,by rw [state3]; exact context,by rw [fb3]; exact fbl,by rw [state3]; exact tp⟩
    · have := fam3; rwa [show resources t3.frame = resources t2.frame by simp [resources,state3]]
    · rw [state3]; exact bufs
  have st4 : St F t4 (C ++ [(pre,cnt)]) := by
    obtain ⟨fam,bufs,base,context,fbl,tp⟩ := st3
    refine ⟨?_,?_,by rw [state4]; exact base,by rw [state4]; exact context,by rw [fb4]; exact fbl,by rw [state4]; exact tp⟩
    · have := fam4; rwa [show resources t4.frame = resources t2.frame by simp [resources,state4,state3]]
    · rw [state4]; exact bufs
  have live2 : liveS t2+40 ≤ F.SPB := live_loop sh2 ok
  have live3 : liveS t3+40 ≤ F.SPB := live_loop sh3 ok
  have cb3 : Cb F t3 := by
    have := cb2.scalarPeak; have := cb2.peak; have := st3.storagePeak
    refine ⟨?_,?_⟩ <;> simp [NExpr.nodes,Container.nodes] at pu3 ⊢ <;> omega
  have cb4 : Cb F t4 := by
    have := cb3.scalarPeak; have := cb3.peak; have := st4.storagePeak
    refine ⟨?_,?_⟩ <;> simp [NExpr.nodes,Container.nodes] at pu4 ⊢ <;> omega
  refine ⟨t4,?_,sh4,st4,cb4,?_,?_,?_,?_⟩
  · intro Q post
    refine RunsTo.seq (RunsTo.primitive run1 ⟨rfl,rfl,RunsTo.seq (RunsTo.primitive run2 ⟨rfl,rfl,
      RunsTo.seq (RunsTo.primitive run3 ⟨rfl,rfl,RunsTo.seq (RunsTo.primitive run4 ⟨rfl,rfl,RunsTo.skip post⟩)⟩)⟩)⟩)
  · rw [state4,state3,forest2,forest1]
  · rw [fb4,fb3,fb2,fb1]
  · omega
  · simp [NExpr.nodes,Container.nodes] at wu3 wu4; omega

end Proofs.ElementCountExec
