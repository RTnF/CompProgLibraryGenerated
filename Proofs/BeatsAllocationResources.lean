import Proofs.BeatsInputPrepare
import Proofs.CppNestedCopy

namespace Proofs.BeatsAllocationResources
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedConstruct Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppVectorOwnership
open Proofs.DynamicExpr Proofs.DynamicRealizes Proofs.DynamicContents Proofs.MultiVecDynamic
open Proofs.DynamicResultValid Proofs.BeatsAllocation Proofs.BeatsAllocationLayout

structure Bounds (s out : NState) (cost growth : Nat) : Prop where
  work : out.scalars.work ≤ s.scalars.work+cost
  live : liveS out = liveS s
  scalarPeak : out.scalars.peak ≤ max s.scalars.peak (liveS s+cost)
  base : out.frame.state.storage.baseSpace = s.frame.state.storage.baseSpace
  space : out.frame.state.liveSpace = s.frame.state.liveSpace+growth
  storageWork : out.frame.state.storage.work = s.frame.state.storage.work+growth
  storagePeak : out.frame.state.storage.peak ≤ max s.frame.state.storage.peak
    (s.frame.state.liveSpace+growth+1-s.frame.state.storage.baseSpace)
  peak : out.peak ≤ max s.peak (max s.scalars.peak (liveS s+cost)+max s.frame.state.storage.peak
    (s.frame.state.liveSpace+growth+1-s.frame.state.storage.baseSpace))

theorem Bounds.refl (s : NState) : Bounds s s 0 0 := by
  constructor <;> (try rfl) <;> omega

theorem Bounds.trans {s mid out : NState} {c1 c2 g1 g2 : Nat}
    (first : Bounds s mid c1 g1) (next : Bounds mid out c2 g2) : Bounds s out (c1+c2) (g1+g2) := by
  let sp := max s.scalars.peak (liveS s+(c1+c2))
  let tp := max s.frame.state.storage.peak (s.frame.state.liveSpace+(g1+g2)+1-s.frame.state.storage.baseSpace)
  have scalarFirst : max s.scalars.peak (liveS s+c1) ≤ sp := by dsimp [sp]; omega
  have storageFirst : max s.frame.state.storage.peak (s.frame.state.liveSpace+g1+1-s.frame.state.storage.baseSpace) ≤ tp := by dsimp [tp]; omega
  have scalarNext : max mid.scalars.peak (liveS mid+c2) ≤ sp := by
    have prior := first.scalarPeak
    rw [first.live]
    dsimp [sp]
    omega
  have storageNext : max mid.frame.state.storage.peak (mid.frame.state.liveSpace+g2+1-mid.frame.state.storage.baseSpace) ≤ tp := by
    have prior := first.storagePeak
    rw [first.space,first.base]
    dsimp [tp]
    omega
  have midPeak : mid.peak ≤ max s.peak (sp+tp) :=
    first.peak.trans (max_le (Nat.le_max_left _ _)
      ((Nat.add_le_add scalarFirst storageFirst).trans (Nat.le_max_right _ _)))
  refine ⟨?_,next.live.trans first.live,next.scalarPeak.trans scalarNext,next.base.trans first.base,?_,?_,
    next.storagePeak.trans storageNext,?_⟩
  · have a := first.work
    have b := next.work
    omega
  · rw [next.space,first.space]
    omega
  · rw [next.storageWork,first.storageWork]
    omega
  · exact next.peak.trans (max_le midPeak
      ((Nat.add_le_add scalarNext storageNext).trans (Nat.le_max_right _ _)))

theorem fill_resources (params : List Parameter) (l : Locals) (h : ContentsHeap)
    (s out : NState) (real : Realizes params l h s) (ty : Ty) (wr : Bool)
    (count value : NExpr) (n x : Int)
    (countPure : denote params l h count = some n) (valuePure : denote params l h value = some x)
    (actual : (NStmt.fillVector ty wr count value).run s = some ⟨out,none,false⟩) :
    Bounds s out (2*count.nodes+2*value.nodes+3) (n.toNat+1) := by
  obtain ⟨_,t1,extra1,ev1⟩ := Proofs.DynamicExprCertified.sound
    (Proofs.DynamicExprDerive.derive (Proofs.DynamicExprAuto.ready _ _ _ _) n countPure) s real
  have real1 := Proofs.DynamicExprCompose.in_extension params l h s t1 real (Ext.of_goodF ev1.2.1 ev1.2.2)
  obtain ⟨_,t2,extra2,ev2⟩ := Proofs.DynamicExprCertified.sound
    (Proofs.DynamicExprDerive.derive (Proofs.DynamicExprAuto.ready _ _ _ _) x valuePure) t1 real1
  have good := ev1.2.1.trans ev2.2.1
  let released := t2.release s
  simp only [NStmt.run,ev1.1,Bind.bind,Option.bind,ev2.1] at actual
  split at actual
  · change (released.frame.state.fillVector ty released.scope n.toNat x).bind _ = _ at actual
    obtain ⟨next,allocated,tail⟩ := bind_some _ _ _ actual
    obtain ⟨⟨frame,binding⟩,bound,final⟩ := bind_some _ _ _ tail
    have defined : out = ({released with frame := frame,slots := released.slots++[.vector binding]} : NState).charge 3 0 :=
      (congrArg NStep.state (Option.some.inj final)).symm
    have outState : out.frame.state = next := by
      rw [defined]
      exact (Proofs.DynamicOwnedLayout.bind_root _ frame _ _ _ wr binding bound).1
    obtain ⟨_,_,_,_,nextEq⟩ := fillVector_inv released.frame.state ty released.scope n.toNat x next allocated
    obtain ⟨state,_,_,scope,memory,bindings,base,_,work,_,scalarPeak,_,peak⟩ := good
    have live : liveS t2 = liveS s := liveS_of_memory memory bindings base
    have rs : released.frame.state = s.frame.state := state
    have sc : released.scope = s.scope := scope
    rw [rs,sc] at nextEq
    obtain ⟨heap,m,family,_⟩ := real.heap
    have lengths := (Proofs.CppNestedVectorStore.wellFormed_parts s.frame.state family.valid).1
    let source : Proofs.CppVector.Buffer Value :=
      ⟨0,List.replicate n.toNat (.integer x),n.toNat,Proofs.CppVectorBindings.sizeLimit ty,0⟩
    have cloneEq : Proofs.CppNestedCopy.cloned s.frame.state source ty s.scope = next := by
      rw [nextEq]
      simp only [Proofs.CppNestedCopy.cloned,Proofs.CppVectorCopy.copied,source,List.length_replicate,Nat.add_assoc]
    have space := (Proofs.CppNestedCopy.clone_cost s.frame.state source ty s.scope lengths).2.1
    simp only [source,List.length_replicate,cloneEq] at space
    have scalar : out.scalars.peak ≤ max s.scalars.peak (liveS s+(2*count.nodes+2*value.nodes+3)) := by
      rw [defined]
      change max t2.scalars.peak (liveS t2+0) ≤ _
      rw [live]
      omega
    refine ⟨?_,?_,scalar,?_,?_,?_,?_,?_⟩
    · rw [defined]
      change t2.scalars.work+3 ≤ _
      omega
    · rw [defined]
      exact live
    · rw [outState,nextEq]
    · rw [outState,space]
      omega
    · rw [outState,nextEq]
    · rw [outState,nextEq]
      dsimp only
      omega
    · rw [defined]
      have store : t2.frame.state.storage.peak = s.frame.state.storage.peak := by rw [state]
      rw [store] at peak
      change max t2.peak (max t2.scalars.peak (liveS t2+0)+frame.state.storage.peak) ≤ _
      have frameEq := (Proofs.DynamicOwnedLayout.bind_root _ frame _ _ _ wr binding bound).1
      rw [frameEq,nextEq]
      dsimp only
      rw [live]
      omega
  · simp at actual

def fieldCost (i : Nat) : Nat := 2*(countCode i).nodes+2*(valueCode i).nodes+3
def scalarCost (i : Nat) : Nat → Nat
  | 0 => 0
  | count+1 => fieldCost i+scalarCost (i+1) count

theorem scalarCost_fifteen : scalarCost 0 15 = 319 := by
  norm_num [scalarCost,fieldCost,countCode,valueCode,Proofs.BeatsExec.wideCount,NExpr.nodes,Container.nodes]

theorem prefix_bounds {st : Proofs.DynamicOwnedState.State} {p : Parameter} {a : List Int}
    (h : Input st p a) (n : Nat) (length : a.length = n) (small : 4*n < 2147483648) :
    ∀ count i (s : NState), Proofs.DynamicOwnedState.Realizes (states st n i) s →
      ∃ out, runFuel (count+1) (fillPrefix i count) s = .finished ⟨out,none,false⟩ ∧
        Proofs.DynamicOwnedState.Realizes (states st n (i+count)) out ∧
        Bounds s out (scalarCost i count) (storageWork n i count) := by
  intro count
  induction count with
  | zero => intro i s real; exact ⟨s,rfl,real,Bounds.refl s⟩
  | succ count ih =>
    intro i s real
    have input := states_input h n i
    obtain ⟨mid,head,after⟩ := Proofs.DynamicOwnedConstruct.sound (states st n i) s real (fieldStmt i)
      (states st n (i+1)) (field_construct input n length small i)
    have first : Bounds s mid (fieldCost i) (fieldCount n i+1) := by
      simpa only [fieldCost,Int.toNat_natCast] using fill_resources _ _ _ s mid real.data (fieldTy i) true
        (countCode i) (valueCode i) (fieldCount n i) (fieldValue i)
        (input_count input n length small i) (input_value _ i) head
    obtain ⟨out,tail,final,budget⟩ := ih (i+1) mid after
    refine ⟨out,?_,?_,?_⟩
    · have one : runFuel (count+1) (.primitive (fieldStmt i)) s = .finished ⟨mid,none,false⟩ := by
        simp [runFuel,head,Proofs.CppLoop.liftChecked]
      change (do
        let step ← runFuel (count+1) (.primitive (fieldStmt i)) s
        if step.returned.isSome || step.breaking then pure step
        else runFuel (count+1) (fillPrefix (i+1) count) step.state) = _
      rw [one]
      simpa only [Bind.bind,Proofs.CppLoop.Outcome.bind,Option.isSome_none,Bool.false_or,Bool.false_eq_true,ite_false] using tail
    · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using final
    · simpa only [scalarCost,storageWork] using first.trans budget

def allocationSize (n : Nat) : Nat := 12*(8*n+8)+783
def prefixScalar (s : NState) : Nat := max s.scalars.peak (liveS s+319)
def prefixStorage (s : NState) (n : Nat) : Nat := max s.frame.state.storage.peak
  (s.frame.state.liveSpace+allocationSize n+1-s.frame.state.storage.baseSpace)
def prefixPeak (s : NState) (n : Nat) : Nat := max s.peak (prefixScalar s+prefixStorage s n)
def stageScalar (s : NState) (P : List Proofs.CppState.Cell) (n : Nat) : Nat :=
  prefixPeak s n+prefixScalar s+P.length+100
def stageStorage (s : NState) (n : Nat) : Nat :=
  prefixStorage s n+s.frame.state.liveSpace+allocationSize n+1

theorem prefix_resources {st : Proofs.DynamicOwnedState.State} {p : Parameter} {a : List Int}
    (h : Input st p a) (n : Nat) (length : a.length = n) (small : 4*n < 2147483648)
    (s : NState) (real : Proofs.DynamicOwnedState.Realizes st s) :
    ∃ out, runFuel 16 (fillPrefix 0 15) s = .finished ⟨out,none,false⟩ ∧ Bounds s out 319 (allocationSize n) := by
  obtain ⟨out,ran,_,budget⟩ := prefix_bounds h n length small 15 0 s real
  exact ⟨out,ran,by simpa only [scalarCost_fifteen,storageWork_fifteen,allocationSize] using budget⟩

theorem stage_resources {st : Proofs.DynamicOwnedState.State} {p : Parameter} {a : List Int}
    (h : Input st p a) (entry : Proofs.BeatsInlineFrame.Entry st p) (n : Nat)
    (positive : 1 ≤ n) (range : 4*n < 2147483648) (length : a.length = n) (values : Proofs.BeatsModel.InRange a)
    (s : NState) (real : Proofs.DynamicOwnedState.Realizes st s)
    (strict : ∀ owner c, s.frame.state.forest.context owner = some c → c ≤ s.scope)
    (base : s.scalars.baseMemory ≤ s.scalars.memory.length)
    (buf : Proofs.CppVector.Buffer Value) (stored : s.frame.state.storage.lookup p.owner = some buf)
    (readonly : p.writable = false) (limit : buf.limit = Proofs.CppVectorBindings.sizeLimit Proofs.IntSim.s64) :
    ∃ fuel step bf heap,
      runFuel fuel (Proofs.BeatsInlineExec.stage 0 15) s = .finished step ∧
      step.returned = none ∧ step.breaking = false ∧
      Proofs.BeatsRep.BRepS n (8*n+8) 256 a bf (Proofs.BeatsModel.buildBT a 0 n) heap ∧
      step.state.scalars.work ≤ s.scalars.work+(4*n*45414+419) ∧
      step.state.frame.state.storage.work ≤ s.frame.state.storage.work+allocationSize n+(4*n*18+10) ∧
      step.state.scalars.peak ≤ stageScalar s st.core.locals.memory n ∧
      step.state.frame.state.storage.peak ≤ stageStorage s n ∧
      step.state.peak ≤ stageScalar s st.core.locals.memory n+stageStorage s n ∧
      ∀ i, i < 16 → ∃ finalBuffer, step.state.frame.state.storage.lookup (Proofs.BeatsAllocationArgs.owner st p i) = some finalBuffer ∧
        finalBuffer.items = (Proofs.BeatsExec.VVA a bf i).map Value.integer := by
  obtain ⟨out,fuel,step,bf,heap,allocated,ran,returned,breaking,rep,_,scalarWork,storageWork,scalarPeak,storagePeak,peak,vectors⟩ :=
    Proofs.BeatsInlineExec.stage_exec h entry n positive range length values s real strict base buf stored readonly limit
  obtain ⟨bounded,boundedRun,budget⟩ := prefix_resources h n length range s real
  have same : bounded = out := congrArg NStep.state (Proofs.CppLoop.Outcome.finished.inj (boundedRun.symm.trans allocated))
  subst bounded
  have sp : Proofs.BeatsInlineExec.scalarBound out st.core.locals.memory ≤ stageScalar s st.core.locals.memory n := by
    have p := budget.peak
    have q := budget.scalarPeak
    change out.peak ≤ prefixPeak s n at p
    change out.scalars.peak ≤ prefixScalar s at q
    unfold Proofs.BeatsInlineExec.scalarBound stageScalar
    omega
  have tp : Proofs.BeatsInlineExec.storageBound out ≤ stageStorage s n := by
    have p := budget.storagePeak
    change out.frame.state.storage.peak ≤ prefixStorage s n at p
    unfold Proofs.BeatsInlineExec.storageBound stageStorage
    rw [budget.space]
    omega
  refine ⟨fuel,step,bf,heap,ran,returned,breaking,rep,?_,?_,scalarPeak.trans sp,storagePeak.trans tp,
    peak.trans (Nat.add_le_add sp tp),vectors⟩
  · have p := budget.work
    omega
  · simpa only [storageWork_fifteen,allocationSize] using storageWork

theorem total_work (s out : NState) (n : Nat)
    (scalar : out.scalars.work ≤ s.scalars.work+(4*n*45414+419))
    (storage : out.frame.state.storage.work ≤ s.frame.state.storage.work+allocationSize n+(4*n*18+10)) :
    out.work ≤ s.work+181824*n+1308 := by
  unfold NState.work allocationSize at *
  omega

theorem prepare_resources (caller : NState) (slot vb owner scope : Nat) (wb maximum : Bool)
    (buf : Proofs.CppVector.Buffer Value) (a : List Int)
    (ok : Proofs.MatMulPrepare.VOKG caller Proofs.IntSim.s64 slot vb owner scope wb maximum buf)
    (items : buf.items = a.map Value.integer) (limit : buf.limit = Proofs.CppVectorBindings.sizeLimit Proofs.IntSim.s64)
    (n : Nat) (positive : 1 ≤ n) (range : 4*n < 2147483648) (length : a.length = n) (values : Proofs.BeatsModel.InRange a) :
    ∃ callee fuel step bf heap,
      Proofs.CppNestedCall.prepare caller Proofs.BeatsInputPrepare.parameters [.vectorReference slot] = some callee ∧
      runFuel fuel (Proofs.BeatsInlineExec.stage 0 15) callee = .finished step ∧
      step.returned = none ∧ step.breaking = false ∧
      Proofs.BeatsRep.BRepS n (8*n+8) 256 a bf (Proofs.BeatsModel.buildBT a 0 n) heap ∧
      step.state.work ≤ caller.work+181824*n+1311 ∧
      step.state.scalars.peak ≤ stageScalar callee (Proofs.DoublingCall.callerP caller) n ∧
      step.state.frame.state.storage.peak ≤ stageStorage callee n ∧
      step.state.peak ≤ stageScalar callee (Proofs.DoublingCall.callerP caller) n+stageStorage callee n := by
  let callee := Proofs.BeatsInputPrepare.prepared caller owner scope
  have real := Proofs.BeatsInputPrepare.prepared_real caller slot vb owner scope wb maximum buf a ok items
  have input := Proofs.BeatsInputPrepare.prepared_input caller slot vb owner scope wb maximum buf a ok items
  have entry := Proofs.BeatsInputPrepare.prepared_entry caller owner scope maximum a
  have shape := Proofs.BeatsInputPrepare.layout caller owner scope
  have stored : callee.frame.state.storage.lookup owner = some buf := by rw [shape.1]; exact ok.vfound
  obtain ⟨fuel,step,bf,heap,ran,returned,breaking,rep,scalar,storage,sp,tp,peak,_⟩ :=
    stage_resources input entry n positive range length values callee real
      (Proofs.BeatsInputPrepare.prepared_strict caller owner scope ok.strict)
      (Proofs.BeatsInputPrepare.prepared_base caller owner scope ok.base) buf stored rfl limit
  have work := total_work callee step.state n scalar storage
  have preparedWork : callee.work = caller.work+3 := by
    change (Proofs.BeatsInputPrepare.prepared caller owner scope).scalars.work+
      (Proofs.BeatsInputPrepare.prepared caller owner scope).frame.state.storage.work = _
    rw [Proofs.BeatsInputPrepare.prepared_work,shape.1]
    unfold NState.work
    omega
  have memory : (Proofs.BeatsInputPrepare.logical caller owner scope maximum a).core.locals.memory =
      Proofs.DoublingCall.callerP caller := shape.2.2.2.2.2.2.1
  rw [memory] at sp peak
  refine ⟨callee,fuel,step,bf,heap,Proofs.BeatsInputPrepare.prepare_actual caller slot vb owner scope wb maximum buf ok,
    ran,returned,breaking,rep,?_,sp,tp,peak⟩
  rw [preparedWork] at work
  omega

end Proofs.BeatsAllocationResources
