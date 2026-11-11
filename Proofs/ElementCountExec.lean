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

/-! ## Leaving a block that declares nothing -/

theorem left_sh {O T : NState} {P : List Cell} {B : Nat} {slots : List Location} {cells cells' : List Cell}
    {binds : List CppState.Binding} {scope : Nat} (sh : Sh O P B slots cells binds scope)
    (memory : T.scalars.memory = P ++ cells') (len : cells'.length = cells.length) :
    Sh (O.left T) P B slots cells' binds scope := by
  refine ⟨by simp [sh.slots],?_,by simp [sh.bindings],by simp [sh.base],by simp [sh.scope]⟩
  simp only [left_memory,memory,sh.memory]
  rw [List.take_of_length_le (by simp [len])]

theorem leave_ok (F : Fix) (ok : FixOK F) (O T : NState) (C : List (Int × Nat))
    (st : St F T C) (cbT : Cb F T) (cbO : Cb F O) (lenEq : T.scalars.memory.length = O.scalars.memory.length)
    (types : T.scalars.memory.map Cell.type = O.scalars.memory.map Cell.type)
    (fbO : O.frame.bindings.length = 2) (deeper : F.sc ≤ O.scope) (liveO : liveS O ≤ F.SPB)
    (len : C.length ≤ F.X.length) :
    O.leave T none = some (O.left T) ∧ St F (O.left T) C ∧ Cb F (O.left T) ∧
      (O.left T).scalars.work = T.scalars.work+1 ∧ (O.left T).frame.state.forest = T.frame.state.forest ∧
      (O.left T).frame.bindings = T.frame.bindings := by
  have valid := st.family.valid
  have fresh : ∀ owner, T.frame.state.forest.context owner ≠ some (O.scope+1) := by
    intro owner bad; have := st.context owner _ bad; omega
  have takeT : T.scalars.memory.take O.scalars.memory.length = T.scalars.memory :=
    List.take_of_length_le (by omega)
  have leave := leave_scalar O T none (by intro o e h; cases h) (by omega)
    (by rw [takeT,types])
    valid fresh
  have same := Proofs.DoublingNested.noopRetired_same T.frame
  have bindingsT : (O.left T).frame.bindings = T.frame.bindings := by
    simp only [left_frameBindings]; rw [fbO,← st.frameBindings,List.take_length]
  have famL : Family F.params (F.heap C) (O.left T).frame (resources (O.left T).frame) := by
    have := MultiVecDynamicScope.Family.left O T st.family (by
      intro q hq; simp [Fix.params,pv,pr] at hq; rcases hq with rfl | rfl <;> simp [fbO])
    exact DynamicAllocateFamily.Family.remeasured this
  have stateL : (O.left T).frame.state = (noopRetired T.frame).state := rfl
  have lookupL : ∀ o, (O.left T).frame.state.storage.lookup o = T.frame.state.storage.lookup o := by
    intro o; rw [stateL]; exact same.lookup o
  have liveL : (O.left T).frame.state.liveSpace = T.frame.state.liveSpace := by rw [stateL]; exact same.liveSpace
  have workL : (O.left T).frame.state.storage.work = T.frame.state.storage.work := rfl
  have peakL : (O.left T).frame.state.storage.peak =
      max T.frame.state.storage.peak (T.frame.state.liveSpace-T.frame.state.storage.baseSpace) := rfl
  have baseL : (O.left T).frame.state.storage.baseSpace = T.frame.state.storage.baseSpace := rfl
  obtain ⟨b0,b1,f0,f1,i0,i1,c0,c1,l0,l1,lv,wk⟩ := st.bufs
  have tpL : (O.left T).frame.state.storage.peak ≤ F.TPB := by
    rw [peakL,lv,st.base]; have := st.storagePeak; have := ok.tpb; omega
  refine ⟨leave,⟨famL,⟨b0,b1,by rw [lookupL]; exact f0,by rw [lookupL]; exact f1,i0,i1,c0,c1,l0,l1,
    by rw [liveL]; exact lv,by rw [workL]; exact wk⟩,by rw [baseL]; exact st.base,
    by rw [stateL]; exact st.context,by rw [bindingsT]; exact st.frameBindings,tpL⟩,⟨?_,?_⟩,rfl,rfl,bindingsT⟩
  · rw [left_scalar_peak]
    have := cbO.scalarPeak; have := cbT.scalarPeak
    simp only [liveS] at liveO
    rw [takeT,lenEq]
    omega
  · rw [left_peak,left_scalar_peak]
    have := cbO.peak; have := cbT.peak; have := cbO.scalarPeak; have := cbT.scalarPeak
    simp only [liveS] at liveO
    rw [takeT,lenEq]
    have : (noopRetired T.frame).state.storage.peak ≤ F.TPB := tpL
    omega

/-! ## Moving the invariants along released expressions and scope entries -/

theorem sh_released {s u : NState} {w p : Nat} {P : List Cell} {B : Nat} {slots : List Location} {cells : List Cell}
    {binds : List CppState.Binding} {scope : Nat} (r : FamilySteps.Released s u w p)
    (sh : Sh s P B slots cells binds scope) : Sh u P B slots cells binds scope :=
  ⟨by rw [r.slots]; exact sh.slots,by rw [r.memory]; exact sh.memory,by rw [r.scalarBindings]; exact sh.bindings,
    by rw [r.base]; exact sh.base,by rw [r.scope]; exact sh.scope⟩

theorem resources_eq {f g : Frame} (state : f.state = g.state) : resources f = resources g := by
  simp [resources,state]

theorem st_frame {F : Fix} {s u : NState} {C : List (Int × Nat)} (st : St F s C)
    (family : Family F.params (F.heap C) u.frame (resources s.frame))
    (state : u.frame.state = s.frame.state) (bindings : u.frame.bindings.length = 2) : St F u C := by
  obtain ⟨_,bufs,base,context,_,tp⟩ := st
  exact ⟨by rwa [resources_eq state],by rw [state]; exact bufs,by rw [state]; exact base,
    by rw [state]; exact context,bindings,by rw [state]; exact tp⟩

theorem st_released {F : Fix} {s u : NState} {w p : Nat} {C : List (Int × Nat)} (r : FamilySteps.Released s u w p)
    (st : St F s C) : St F u C :=
  st_frame st (r.family st.family) r.state (by rw [r.bindings]; exact st.frameBindings)

theorem cb_released {F : Fix} {s u : NState} {w p : Nat} {C : List (Int × Nat)} (r : FamilySteps.Released s u w p)
    (cb : Cb F s) (st : St F s C) (live : liveS s+p ≤ F.SPB) : Cb F u := by
  have := cb.scalarPeak; have := cb.peak; have := r.peakUpper; have := r.outerUpper
  have tp : u.frame.state.storage.peak ≤ F.TPB := by rw [r.state]; exact st.storagePeak
  exact ⟨by omega,by omega⟩

theorem sh_enter {s : NState} {P : List Cell} {B : Nat} {slots : List Location} {cells : List Cell}
    {binds : List CppState.Binding} {scope : Nat} (sh : Sh s P B slots cells binds scope) :
    Sh {s with scope := s.scope+1} P B slots cells binds (scope+1) :=
  ⟨sh.slots,sh.memory,sh.bindings,sh.base,by simp [sh.scope]⟩

theorem st_enter {F : Fix} {s : NState} {C : List (Int × Nat)} (st : St F s C) :
    St F {s with scope := s.scope+1} C :=
  ⟨st.family,st.bufs,st.base,st.context,st.frameBindings,st.storagePeak⟩

theorem cb_enter {F : Fix} {s : NState} (cb : Cb F s) : Cb F {s with scope := s.scope+1} :=
  ⟨cb.scalarPeak,cb.peak⟩

theorem types_cells (P : List Cell) (ty : Ty) (n : Nat) (pre pre' : Int) (cnt cnt' t t' : Nat) :
    (P ++ cellsI ty n pre' cnt' t').map Cell.type = (P ++ cellsI ty n pre cnt t).map Cell.type := by
  simp [cellsI]

/-- `cnt++` inside its block: the `if` branch. -/
theorem yes_run (F : Fix) (ok : FixOK F) (u : NState) (C : List (Int × Nat)) (pre : Int) (cnt t : Nat)
    (sh : Sh u F.P F.B slotsI (cellsI F.ty F.X.length pre cnt t) (bindsI F.P) (F.sc+2))
    (st : St F u C) (cb : Cb F u) (hpre : F.ty.valid pre = true) (hc : cnt+1 < 2147483648) (ht : t < F.X.length)
    (len : C.length ≤ F.X.length) :
    ∃ T, (∀ Q : NStep → Prop, Q ⟨T,none,false⟩ → RunsTo yesC u Q) ∧
      Sh T F.P F.B slotsI (cellsI F.ty F.X.length pre (cnt+1) t) (bindsI F.P) (F.sc+2) ∧ St F T C ∧ Cb F T ∧
      u.scalars.work ≤ T.scalars.work ∧ T.scalars.work ≤ u.scalars.work+10 := by
  have small := ok.small
  have sh1 := sh_enter sh
  obtain ⟨_,_,ec,_⟩ := envI sh1 (by omega) hpre (by omega) (by omega)
  have live := live_loop sh1 ok
  have conv : ti.convert ((cnt : Int)+1) = some ((cnt : Int)+1) :=
    Ty.convert_of_valid _ _ (by have := i32_valid_nat (cnt+1) hc; simpa using this)
  obtain ⟨t1,run1,fam1,state1,rights1,fb1,sl1,sc1,me1,bi1,ba1,wl1,wu1,pl1,pu1,ql1,qu1⟩ :=
    FamilySteps.assign (s := {u with scope := u.scope+1}) st.family
      (.binary ti .add (.variable ti 4) (.literal ti 1)) 4 2 ti ((cnt : Int)+1) ((cnt : Int)+1)
      ⟨F.P.length+2,true⟩ ⟨ti,(cnt : Int)⟩
      (by rw [denote_scalar _ _ _ _ (by simp [NExpr.scalarOnly]),snapshot_env]
          exact denote_inc _ 4 ti _ ec (by simpa using i32_valid_nat 1 (by omega)) conv)
      conv
      (by simp [sh.slots,slotsI,slotsC,slotsP,slotsN]) (by simp [sh.bindings,bindsI,bindsC,bindsP,bindsN])
      (by simp [sh.memory,cellsI]) rfl (i32_valid_nat cnt (by omega)) rfl
  have memT : t1.scalars.memory = F.P ++ cellsI F.ty F.X.length pre (cnt+1) t := by
    rw [me1,sh1.memory]; have := set_cnt F.P F.ty F.X.length pre cnt t (cnt+1); simpa using this
  have st1 : St F t1 C := st_frame st fam1 state1 (by rw [fb1]; exact st.frameBindings)
  have pu1' : t1.scalars.peak ≤ max u.scalars.peak (liveS u+2*3) := by
    have e : liveS {u with scope := u.scope+1} = liveS u := rfl
    simpa [NExpr.nodes,e] using pu1
  have qu1' : t1.peak ≤ max u.peak (t1.scalars.peak+t1.frame.state.storage.peak) := qu1
  have wu1' : t1.scalars.work ≤ u.scalars.work+2*3+1 := by simpa [NExpr.nodes] using wu1
  have liveU := live_loop sh ok
  have cb1 : Cb F t1 := by
    have := cb.scalarPeak; have := cb.peak; have := st1.storagePeak
    exact ⟨by omega,by omega⟩
  obtain ⟨leave,stL,cbL,workL,_,_⟩ := leave_ok F ok u t1 C st1 cb1 cb
    (by rw [memT,sh.memory]; simp [cellsI]) (by rw [memT,sh.memory]; exact types_cells ..)
    st.frameBindings (by rw [sh.scope]; omega) (by have := live_loop sh ok; omega) len
  refine ⟨u.left t1,?_,left_sh sh memT (by simp [cellsI]),stL,cbL,?_,?_⟩
  · intro Q post
    apply RunsTo.seq
    apply RunsTo.scopeSimple
    apply RunsTo.seq
    refine RunsTo.primitive run1 ⟨rfl,rfl,?_⟩
    apply RunsTo.skip
    exact ⟨rfl,rfl,u.left t1,leave,rfl,rfl,RunsTo.skip post⟩
  · rw [workL]; have : u.scalars.work ≤ t1.scalars.work := wl1; omega
  · rw [workL]; omega

/-- The `else` branch with its block: close `(pre, cnt)` and start the run of `v[t]`. -/
theorem no_run (F : Fix) (ok : FixOK F) (u : NState) (C : List (Int × Nat)) (pre : Int) (cnt t : Nat) (x : Int)
    (sh : Sh u F.P F.B slotsI (cellsI F.ty F.X.length pre cnt t) (bindsI F.P) (F.sc+2))
    (st : St F u C) (cb : Cb F u) (hpre : F.ty.valid pre = true) (hc : cnt < 2147483648) (ht : t < F.X.length)
    (len : C.length < F.X.length) (item : F.X[t]? = some x) :
    ∃ T, (∀ Q : NStep → Prop, Q ⟨T,none,false⟩ → RunsTo (noC F.ty F.cv) u Q) ∧
      Sh T F.P F.B slotsI (cellsI F.ty F.X.length x 1 t) (bindsI F.P) (F.sc+2) ∧ St F T (C ++ [(pre,cnt)]) ∧
      Cb F T ∧ u.scalars.work ≤ T.scalars.work ∧ T.scalars.work ≤ u.scalars.work+41 := by
  have sh1 := sh_enter sh
  obtain ⟨T,run,shT,stT,cbT,_,_,wl,wu⟩ := noBody_run F ok {u with scope := u.scope+1} C pre cnt t x sh1 (st_enter st) (cb_enter cb) hpre hc ht
    len item
  have memT := shT.memory
  obtain ⟨leave,stL,cbL,workL,_,_⟩ := leave_ok F ok u T (C ++ [(pre,cnt)]) stT cbT cb
    (by rw [memT,sh.memory]; simp [cellsI]) (by rw [memT,sh.memory]; exact types_cells ..)
    st.frameBindings (by rw [sh.scope]; omega) (by have := live_loop sh ok; omega) (by simp; omega)
  refine ⟨u.left T,?_,left_sh sh memT (by simp [cellsI]),stL,cbL,?_,?_⟩
  · intro Q post
    apply RunsTo.seq
    apply RunsTo.scopeSimple
    refine run _ ⟨rfl,rfl,u.left T,leave,rfl,rfl,RunsTo.skip post⟩
  · rw [workL]; have : u.scalars.work ≤ T.scalars.work := wl; omega
  · rw [workL]; have : T.scalars.work ≤ u.scalars.work+40 := wu; omega

theorem bool_convert (v : Int) (h : v = 0 ∨ v = 1) : tb.convert v = some v :=
  Ty.convert_of_valid _ _ (by rcases h with rfl | rfl <;> rfl)

theorem rleAdd_eq (C : List (Int × Nat)) (pre : Int) (cnt : Nat) (x : Int) (h : pre = x) :
    rleAdd (C ++ [(pre,cnt)]) x = C ++ [(pre,cnt+1)] := by simp [rleAdd,h]

theorem rleAdd_ne (C : List (Int × Nat)) (pre : Int) (cnt : Nat) (x : Int) (h : ¬ pre = x) :
    rleAdd (C ++ [(pre,cnt)]) x = (C ++ [(pre,cnt)]) ++ [(x,1)] := by simp [rleAdd,h]

/-- One iteration of the loop body after the condition `i < n` held. -/
theorem iter_run (F : Fix) (ok : FixOK F) (u0 : NState) (C : List (Int × Nat)) (pre : Int) (cnt t : Nat) (x : Int)
    (sh : Sh u0 F.P F.B slotsI (cellsI F.ty F.X.length pre cnt t) (bindsI F.P) (F.sc+1))
    (st : St F u0 C) (cb : Cb F u0) (hpre : F.ty.valid pre = true) (hc : cnt ≤ t) (ht : t < F.X.length)
    (len : C.length ≤ t) (item : F.X[t]? = some x) :
    ∃ T C' pre' cnt', (∀ Q : NStep → Prop, Q ⟨T,none,false⟩ → RunsTo (iterC F.ty F.cv) u0 Q) ∧
      Sh T F.P F.B slotsI (cellsI F.ty F.X.length pre' cnt' (t+1)) (bindsI F.P) (F.sc+1) ∧ St F T C' ∧ Cb F T ∧
      rleAdd (C ++ [(pre,cnt)]) x = C' ++ [(pre',cnt')] ∧ C'.length ≤ t+1 ∧ cnt' ≤ t+1 ∧ F.ty.valid pre' = true ∧
      u0.scalars.work ≤ T.scalars.work ∧ T.scalars.work ≤ u0.scalars.work+80 := by
  have small := ok.small
  have xv : F.ty.valid x = true := ok.valid x (List.mem_of_getElem? item)
  have sh1 := sh_enter sh
  obtain ⟨_,ep,_,ei⟩ := envI sh1 (by omega) hpre (by omega) (by omega)
  -- the condition `pre == v[i]`
  have pure : denote F.params (snapshot {u0 with scope := u0.scope+1}) (eraseHeap (F.heap C)) (cEq F.ty) =
      some (if pre = x then 1 else 0) := by
    apply denote_binary_left _ _ _ tb .eq (.variable F.ty 3) (eAt F.ty) pre x _ (by simp [NExpr.scalarOnly])
    · rw [snapshot_env]; simpa [NExpr.denote] using ep
    · exact denote_at F ok _ C t x (by simp [sh.slots,slotsI,slotsC,slotsP,slotsN]) ei item
    · by_cases e : pre = x <;> simp [binaryValue,e] <;> exact bool_convert _ (by simp)
  obtain ⟨next,eval,rel⟩ := FamilySteps.condition (st_enter st).family (cEq F.ty) _ pure
  let u1 := (next.release {u0 with scope := u0.scope+1}).charge 1 0
  have sh2 : Sh u1 F.P F.B slotsI (cellsI F.ty F.X.length pre cnt t) (bindsI F.P) (F.sc+2) := sh_released rel sh1
  have st2 : St F u1 C := st_released rel (st_enter st)
  have cb2 : Cb F u1 := cb_released rel (cb_enter cb) (st_enter st) (by
    have := live_loop sh ok; have e : liveS {u0 with scope := u0.scope+1} = liveS u0 := rfl
    simp [NExpr.nodes,Container.nodes]; omega)
  have wRel : u1.scalars.work ≤ u0.scalars.work+2*(cEq F.ty).nodes+1 := rel.workUpper
  have wRel' : u0.scalars.work ≤ u1.scalars.work := rel.workLower
  -- the two branches
  obtain ⟨T1,C1,pre1,cnt1,run1,sh3,st3,cb3,math,len1,cnt1le,pre1v,wl1,wu1⟩ :
      ∃ T1 C1 pre1 cnt1, (∀ Q : NStep → Prop, Q ⟨T1,none,false⟩ →
          RunsTo (if (if pre = x then (1 : Int) else 0) = 0 then noC F.ty F.cv else yesC) u1 Q) ∧
        Sh T1 F.P F.B slotsI (cellsI F.ty F.X.length pre1 cnt1 t) (bindsI F.P) (F.sc+2) ∧ St F T1 C1 ∧ Cb F T1 ∧
        rleAdd (C ++ [(pre,cnt)]) x = C1 ++ [(pre1,cnt1)] ∧ C1.length ≤ t+1 ∧ cnt1 ≤ t+1 ∧
        F.ty.valid pre1 = true ∧ u1.scalars.work ≤ T1.scalars.work ∧ T1.scalars.work ≤ u1.scalars.work+41 := by
    by_cases e : pre = x
    · obtain ⟨T,run,shT,stT,cbT,wl,wu⟩ := yes_run F ok u1 C pre cnt t sh2 st2 cb2 hpre (by omega) ht (by omega)
      exact ⟨T,C,pre,cnt+1,by simpa [e] using run,shT,stT,cbT,rleAdd_eq C pre cnt x e,by omega,by omega,hpre,wl,
        by omega⟩
    · obtain ⟨T,run,shT,stT,cbT,wl,wu⟩ := no_run F ok u1 C pre cnt t x sh2 st2 cb2 hpre (by omega) ht (by omega) item
      exact ⟨T,C ++ [(pre,cnt)],x,1,by simpa [e] using run,shT,stT,cbT,rleAdd_ne C pre cnt x e,by simp; omega,
        by omega,xv,wl,wu⟩
  -- leave the iteration block
  obtain ⟨leave,stL,cbL,workL,_,_⟩ := leave_ok F ok u0 T1 C1 st3 cb3 cb
    (by rw [sh3.memory,sh.memory]; simp [cellsI]) (by rw [sh3.memory,sh.memory]; exact types_cells ..)
    st.frameBindings (by rw [sh.scope]; omega) (by have := live_loop sh ok; omega) (by omega)
  have shL : Sh (u0.left T1) F.P F.B slotsI (cellsI F.ty F.X.length pre1 cnt1 t) (bindsI F.P) (F.sc+1) :=
    left_sh sh sh3.memory (by simp [cellsI])
  -- i++
  obtain ⟨_,_,_,eiL⟩ := envI shL (by omega) pre1v (by omega) (by omega)
  have conv : ti.convert ((t : Int)+1) = some ((t : Int)+1) :=
    Ty.convert_of_valid _ _ (by have := i32_valid_nat (t+1) (by omega); simpa using this)
  obtain ⟨t2,run2,fam2,state2,rights2,fb2,sl2,sc2,me2,bi2,ba2,wl2,wu2,pl2,pu2,ql2,qu2⟩ :=
    FamilySteps.assign stL.family (.binary ti .add (.variable ti 5) (.literal ti 1)) 5 3 ti ((t : Int)+1) ((t : Int)+1)
      ⟨F.P.length+3,true⟩ ⟨ti,(t : Int)⟩
      (by rw [denote_scalar _ _ _ _ (by simp [NExpr.scalarOnly]),snapshot_env]
          exact denote_inc _ 5 ti _ eiL (by simpa using i32_valid_nat 1 (by omega)) conv)
      conv
      (by rw [shL.slots]; simp [slotsI,slotsC,slotsP,slotsN]) (by rw [shL.bindings]; simp [bindsI,bindsC,bindsP,bindsN])
      (by rw [shL.memory]; simp [cellsI]) rfl (i32_valid_nat t (by omega)) rfl
  have sh4 : Sh t2 F.P F.B slotsI (cellsI F.ty F.X.length pre1 cnt1 (t+1)) (bindsI F.P) (F.sc+1) :=
    ⟨by rw [sl2]; exact shL.slots,by rw [me2,shL.memory]; have := set_i F.P F.ty F.X.length pre1 cnt1 t (t+1); simpa using this,
      by rw [bi2]; exact shL.bindings,by rw [ba2]; exact shL.base,by rw [sc2]; exact shL.scope⟩
  have st4 : St F t2 C1 := st_frame stL fam2 state2 (by rw [fb2]; exact stL.frameBindings)
  have liveL := live_loop shL ok
  have cb4 : Cb F t2 := by
    have := cbL.scalarPeak; have := cbL.peak; have := st4.storagePeak
    simp [NExpr.nodes] at pu2
    exact ⟨by omega,by omega⟩
  refine ⟨t2,C1,pre1,cnt1,?_,sh4,st4,cb4,math,len1,cnt1le,pre1v,?_,?_⟩
  · intro Q post
    apply RunsTo.seq
    apply RunsTo.scopeSimple
    apply RunsTo.seq
    refine RunsTo.branch eval ?_
    refine run1 _ ⟨rfl,rfl,RunsTo.skip ⟨rfl,rfl,u0.left T1,leave,rfl,rfl,?_⟩⟩
    exact RunsTo.seq (RunsTo.primitive run2 ⟨rfl,rfl,RunsTo.skip post⟩)
  · have := wl2; have := workL; omega
  · have := workL
    have hn : (cEq F.ty).nodes ≤ 10 := by simp [NExpr.nodes,Container.nodes]
    have hw2 : t2.scalars.work ≤ (u0.left T1).scalars.work+2*3+1 := by simpa [NExpr.nodes] using wu2
    omega

end Proofs.ElementCountExec
