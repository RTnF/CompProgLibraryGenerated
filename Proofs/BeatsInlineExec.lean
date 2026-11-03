import Proofs.BeatsInlineFrame

namespace Proofs.BeatsInlineExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorStore Proofs.CppVector
open Proofs.CppNestedHoare Proofs.MultiVec Proofs.MultiVecDynamic
open Proofs.CppLoop (Outcome liftChecked)
open Proofs.BeatsRep Proofs.BeatsExec Proofs.BeatsModel Proofs.BeatsPrepare
open Proofs.BeatsAllocationArgs Proofs.BeatsInlineFrame Proofs.QuotientFrame Proofs.GenState
open Proofs.IntSim Proofs.DoublingNested
open Proofs.BeatsAllocation

def scalarBound (s : NState) (P : List Proofs.CppState.Cell) : Nat :=
  s.peak+s.scalars.peak+P.length+100
def storageBound (s : NState) : Nat :=
  s.frame.state.storage.peak+s.frame.state.liveSpace+1

def stage : Nat → Nat → Command
  | _,0 => Proofs.CppSlotRename.command Proofs.BeatsSlotCycle.cycle (WideCtorCmd 16)
  | i,count+1 => .sequence (.primitive (fieldStmt i)) (stage (i+1) count)

private theorem field_control (i : Nat) (s : NState) (step : NStep)
    (ran : (fieldStmt i).run s = some step) : step.returned = none ∧ step.breaking = false := by
  simp only [fieldStmt,NStmt.run,Bind.bind,Option.bind_eq_some_iff] at ran
  obtain ⟨⟨t,n⟩,_,⟨u,x⟩,_,rest⟩ := ran
  dsimp only at rest
  split at rest
  · simp only [Option.bind_eq_some_iff] at rest
    obtain ⟨state,_,⟨frame,index⟩,_,same⟩ := rest
    cases same
    exact ⟨rfl,rfl⟩
  · simp at rest

theorem prefix_continue : ∀ count i (s out : NState) (fuel : Nat) (step : NStep),
    runFuel (count+1) (fillPrefix i count) s = .finished ⟨out,none,false⟩ →
    runFuel fuel (stage 0 0) out = .finished step →
    ∃ total, runFuel total (stage i count) s = .finished step := by
  intro count
  induction count with
  | zero =>
    intro i s out fuel step head tail
    have same : s = out := congrArg NStep.state (Outcome.finished.inj head)
    subst out
    exact ⟨fuel,tail⟩
  | succ count ih =>
    intro i s out fuel step head tail
    change (do
      let middle ← liftChecked ((fieldStmt i).run s)
      if middle.returned.isSome || middle.breaking then pure middle
      else runFuel (count+1) (fillPrefix (i+1) count) middle.state) = .finished ⟨out,none,false⟩ at head
    cases first : (fieldStmt i).run s with
    | none => simp only [first,liftChecked,Bind.bind,Outcome.bind] at head; contradiction
    | some middle =>
      have control := field_control i s middle first
      simp only [first,liftChecked,Bind.bind,Outcome.bind,control.1,control.2,
        Option.isSome_none,Bool.false_or,Bool.false_eq_true,ite_false] at head
      obtain ⟨total,rest⟩ := ih (i+1) middle.state out fuel step head tail
      have whole : RunsTo (stage i (count+1)) s (fun result => result = step) :=
        RunsTo.sequence (RunsTo.primitive first (Or.inr ⟨control.1,control.2,total,step,rest,rfl⟩))
      obtain ⟨total,result,ran,same⟩ := whole
      subst result
      exact ⟨total,ran⟩

-- These are symbolic bounds derived from the existing state, not execution
-- resource overrides or extra preconditions on a successful run.
theorem initial_resources (s : NState) (P : List Proofs.CppState.Cell) :
    Cq (scalarBound s P) (storageBound s) s.scalars.work (normalize s) := by
  constructor
  · exact Nat.le_refl _
  · change s.scalars.peak ≤ scalarBound s P
    unfold scalarBound
    omega
  · change s.frame.state.storage.peak ≤ storageBound s
    unfold storageBound
    omega
  · change s.peak ≤ scalarBound s P+storageBound s
    unfold scalarBound
    omega


-- Retain the concrete final frame and scalar layout for class-field export.
-- The older execution theorem below remains a projection with its original type.
def FinalLayout (initial out : NState) (V vsc : Nat → Nat) (m : Bool)
    (vv : Nat → List Int) (P : List Proofs.CppState.Cell) (n : Nat) : Prop :=
  ∃ (distinct : ∀ j k, j < 16 → k < 15 → j ≠ k → V j ≠ V k)
    (buffers : Nat → Buffer Value) (work : Nat),
    FWM (mvCtor initial V vsc m distinct) vv buffers work (normalize out).frame ∧
    QS (normalize out) [] initial.scalars.baseMemory initial.scope
      (gS P (CtCells INF n 0 (4*n))).mem (gS P (CtCells INF n 0 (4*n))).bs
      (slN 16 (gS P (CtCells INF n 0 (4*n))).bs.length)

theorem body_exec_full (s : NState) (sl vb V vsc : Nat → Nat) (m : Bool)
    (buf : Nat → Buffer Value) (a : List Int) (n : Nat) (P : List Proofs.CppState.Cell)
    (positive : 1 ≤ n) (range : 4*n < Proofs.BellmanFordExec.M31) (length : a.length = n) (values : InRange a)
    (hv : CVecs s sl vb V vsc m buf (VVA a (initial n)))
    (fw : FWM (mvCtor s V vsc m hv.dist) (VVA a (initial n)) buf 0 (normalize s).frame)
    (qs : QS (normalize s) [] s.scalars.baseMemory s.scope P [] (slN 16 0))
    (slots : 16 ≤ s.slots.length) (bindings : 16 ≤ s.frame.bindings.length) :
    ∃ fuel step bf heap,
      runFuel fuel (Proofs.CppSlotRename.command Proofs.BeatsSlotCycle.cycle (WideCtorCmd 16)) s = .finished step ∧
      step.returned = none ∧ step.breaking = false ∧
      BRepS n (8*n+8) 256 a bf (buildBT a 0 n) heap ∧
      step.state.scope = s.scope ∧
      step.state.scalars.work ≤ s.scalars.work+(4*n*45414+100) ∧
      step.state.frame.state.storage.work ≤ s.frame.state.storage.work+(4*n*18+10) ∧
      step.state.scalars.peak ≤ scalarBound s P ∧
      step.state.frame.state.storage.peak ≤ storageBound s ∧
      step.state.peak ≤ scalarBound s P+storageBound s ∧
      (∀ i, i < 16 → ∃ finalBuffer, step.state.frame.state.storage.lookup (V i) = some finalBuffer ∧
        finalBuffer.items = (VVA a bf i).map Value.integer) ∧
      FinalLayout s step.state V vsc m (VVA a bf) P n := by
  have fresh := initial_fresh n
  obtain ⟨bf,heap,F,r,exec,ret,mem,vectors,cost,need,work,rep⟩ :=
    ctor_rep_wide (S := 256) (mvCtor s V vsc m hv.dist) rfl
      (fun v bound => by show cty v = s64; simp [cty,bound])
      (fun v lower upper => by show cty v = i32; simp [cty]; omega)
      (by show cty 15 = s64; simp [cty]) P a n (8*n+8) positive (Nat.le_refl _) range length values
      (by decide) (initial n) fresh.valid fresh.lens fresh.lo fresh.hi fresh.mxv fresh.smx fresh.mxc
      fresh.mnv fresh.smn fresh.mnc fresh.len fresh.ladd fresh.lval fresh.lov fresh.hiv
  have memory : s.scalars.memory = P := qs.memory
  have base : s.scalars.baseMemory ≤ P.length := by
    rw [← memory]
    exact (hv.ok 0 (by decide)).base
  have initialQs : QS (normalize s) [] s.scalars.baseMemory s.scope (gS P []).mem (gS P []).bs
      (slN 16 (gS P []).bs.length) := by
    simpa only [gS,List.append_nil,List.length_nil,List.range_zero,List.map_nil] using qs
  have sim := soundM_owned (mvCtor s V vsc m hv.dist) cw
    (fun k h => ⟨h,by
      change (if k < 15 then true else m) = true
      exact ite_eq_left (of_decide_eq_true h)⟩) (WideCtorCmd 16) Proofs.BeatsWideCall.writable_body
    F (gS P []) (VVA a (initial n)) r exec (normalize s) initialQs fw (initial_resources s P)
    (by simpa only [gS_mem_len,List.length_nil,Nat.add_zero] using base)
    (by simp only [gS_mem_len,gS_bs_len,List.length_nil,Nat.add_zero]; unfold scalarBound; omega)
    (by unfold scalarBound; omega) (Nat.le_refl _)
    (by change s.frame.state.liveSpace+1 ≤ storageBound s; unfold storageBound; omega)
  obtain ⟨fuel,step,ran,returned,breaking,after,⟨finalBuffers,finalFrame⟩,resources⟩ := sim
  have equal := Proofs.BeatsWideCall.inline_body_view fuel s slots bindings
  change Proofs.BeatsBindingCycle.outcomeView (Proofs.BeatsSlotCycle.outcomeView
    (runFuel fuel (Proofs.CppSlotRename.command Proofs.BeatsSlotCycle.cycle (WideCtorCmd 16)) s)) =
      runFuel fuel (WideCtorCmd 16) (normalize s) at equal
  rw [ran] at equal
  cases actual : runFuel fuel (Proofs.CppSlotRename.command Proofs.BeatsSlotCycle.cycle (WideCtorCmd 16)) s with
  | exhausted => simp only [actual,Proofs.BeatsBindingCycle.outcomeView,Proofs.BeatsSlotCycle.outcomeView] at equal; contradiction
  | fault => simp only [actual,Proofs.BeatsBindingCycle.outcomeView,Proofs.BeatsSlotCycle.outcomeView] at equal; contradiction
  | finished actualStep =>
    simp only [actual,Proofs.BeatsBindingCycle.outcomeView,Proofs.BeatsSlotCycle.outcomeView] at equal
    have same := Outcome.finished.inj equal
    subst step
    rw [ret,Option.map_none] at returned
    rw [vectors] at finalFrame
    refine ⟨fuel,actualStep,bf,heap,actual,returned,breaking,rep,after.scope,?_,?_,
      resources.scalarPeak,resources.storagePeak,resources.outerPeak,?_,?_⟩
    · have bound := resources.work
      change actualStep.state.scalars.work ≤ s.scalars.work+r.cost at bound
      omega
    · have stored := finalFrame.work
      change actualStep.state.frame.state.storage.work = s.frame.state.storage.work+(0+r.wk) at stored
      omega
    · intro i bound
      exact ⟨finalBuffers i,finalFrame.vfound i bound,finalFrame.items i bound⟩
    · refine ⟨hv.dist,finalBuffers,0+r.wk,finalFrame,?_⟩
      rw [mem] at after
      exact after

theorem body_exec (s : NState) (sl vb V vsc : Nat → Nat) (m : Bool)
    (buf : Nat → Buffer Value) (a : List Int) (n : Nat) (P : List Proofs.CppState.Cell)
    (positive : 1 ≤ n) (range : 4*n < Proofs.BellmanFordExec.M31) (length : a.length = n) (values : InRange a)
    (hv : CVecs s sl vb V vsc m buf (VVA a (initial n)))
    (fw : FWM (mvCtor s V vsc m hv.dist) (VVA a (initial n)) buf 0 (normalize s).frame)
    (qs : QS (normalize s) [] s.scalars.baseMemory s.scope P [] (slN 16 0))
    (slots : 16 ≤ s.slots.length) (bindings : 16 ≤ s.frame.bindings.length) :
    ∃ fuel step bf heap,
      runFuel fuel (Proofs.CppSlotRename.command Proofs.BeatsSlotCycle.cycle (WideCtorCmd 16)) s = .finished step ∧
      step.returned = none ∧ step.breaking = false ∧
      BRepS n (8*n+8) 256 a bf (buildBT a 0 n) heap ∧
      step.state.scope = s.scope ∧
      step.state.scalars.work ≤ s.scalars.work+(4*n*45414+100) ∧
      step.state.frame.state.storage.work ≤ s.frame.state.storage.work+(4*n*18+10) ∧
      step.state.scalars.peak ≤ scalarBound s P ∧
      step.state.frame.state.storage.peak ≤ storageBound s ∧
      step.state.peak ≤ scalarBound s P+storageBound s ∧
      ∀ i, i < 16 → ∃ finalBuffer, step.state.frame.state.storage.lookup (V i) = some finalBuffer ∧
        finalBuffer.items = (VVA a bf i).map Value.integer := by
  obtain ⟨fuel,step,bf,heap,ran,returned,breaking,rep,scope,sw,tw,sp,tp,peak,buffers,_⟩ :=
    body_exec_full s sl vb V vsc m buf a n P positive range length values hv fw qs slots bindings
  exact ⟨fuel,step,bf,heap,ran,returned,breaking,rep,scope,sw,tw,sp,tp,peak,buffers⟩

theorem stage_exec_full {st : Proofs.DynamicOwnedState.State} {p : Proofs.MultiVecDynamic.Parameter} {a : List Int}
    (h : Input st p a) (entry : Entry st p) (n : Nat)
    (positive : 1 ≤ n) (range : 4*n < 2147483648) (length : a.length = n) (values : InRange a)
    (s : NState) (real : Proofs.DynamicOwnedState.Realizes st s)
    (strict : ∀ owner c, s.frame.state.forest.context owner = some c → c ≤ s.scope)
    (base : s.scalars.baseMemory ≤ s.scalars.memory.length)
    (buf : Buffer Value) (stored : s.frame.state.storage.lookup p.owner = some buf)
    (readonly : p.writable = false) (limit : buf.limit = Proofs.CppVectorBindings.sizeLimit s64) :
    ∃ out fuel step bf heap,
      runFuel 16 (fillPrefix 0 15) s = .finished ⟨out,none,false⟩ ∧
      runFuel fuel (stage 0 15) s = .finished step ∧ step.returned = none ∧ step.breaking = false ∧
      BRepS n (8*n+8) 256 a bf (buildBT a 0 n) heap ∧ step.state.scope = out.scope ∧
      step.state.scalars.work ≤ out.scalars.work+(4*n*45414+100) ∧
      step.state.frame.state.storage.work ≤ s.frame.state.storage.work+
        Proofs.BeatsAllocationLayout.storageWork n 0 15+(4*n*18+10) ∧
      step.state.scalars.peak ≤ scalarBound out st.core.locals.memory ∧
      step.state.frame.state.storage.peak ≤ storageBound out ∧
      step.state.peak ≤ scalarBound out st.core.locals.memory+storageBound out ∧
      (∀ i, i < 16 → ∃ finalBuffer, step.state.frame.state.storage.lookup (owner st p i) = some finalBuffer ∧
        finalBuffer.items = (VVA a bf i).map Value.integer) ∧
      FinalLayout out step.state (owner st p) (Proofs.BeatsAllocationArgs.scope st p)
        p.maximum (VVA a bf) st.core.locals.memory n := by
  obtain ⟨out,allocated,after,work,args,fw,qs⟩ := prefix_environment h entry n length range s real strict base buf stored readonly limit
  have slots : 16 ≤ out.slots.length := by rw [allocated_slots h entry n out after]; simp only [List.length_map,List.length_range,Nat.le_refl]
  have bindings : 16 ≤ out.frame.bindings.length := by rw [after.binding,states_binding,entry.binding]
  obtain ⟨fuel,step,bf,heap,ran,returned,breaking,rep,scope,scalarWork,storageWork,scalarPeak,storagePeak,peak,vector,layout⟩ :=
    body_exec_full out _ _ _ _ p.maximum (buffer st n buf) a n st.core.locals.memory positive range length values args fw qs slots bindings
  obtain ⟨total,whole⟩ := prefix_continue 15 0 s out fuel step allocated ran
  refine ⟨out,total,step,bf,heap,allocated,whole,returned,breaking,rep,scope,scalarWork,?_,scalarPeak,storagePeak,peak,vector,layout⟩
  rw [work] at storageWork
  exact storageWork

theorem stage_exec {st : Proofs.DynamicOwnedState.State} {p : Proofs.MultiVecDynamic.Parameter} {a : List Int}
    (h : Input st p a) (entry : Entry st p) (n : Nat)
    (positive : 1 ≤ n) (range : 4*n < 2147483648) (length : a.length = n) (values : InRange a)
    (s : NState) (real : Proofs.DynamicOwnedState.Realizes st s)
    (strict : ∀ owner c, s.frame.state.forest.context owner = some c → c ≤ s.scope)
    (base : s.scalars.baseMemory ≤ s.scalars.memory.length)
    (buf : Buffer Value) (stored : s.frame.state.storage.lookup p.owner = some buf)
    (readonly : p.writable = false) (limit : buf.limit = Proofs.CppVectorBindings.sizeLimit s64) :
    ∃ out fuel step bf heap,
      runFuel 16 (fillPrefix 0 15) s = .finished ⟨out,none,false⟩ ∧
      runFuel fuel (stage 0 15) s = .finished step ∧ step.returned = none ∧ step.breaking = false ∧
      BRepS n (8*n+8) 256 a bf (buildBT a 0 n) heap ∧ step.state.scope = out.scope ∧
      step.state.scalars.work ≤ out.scalars.work+(4*n*45414+100) ∧
      step.state.frame.state.storage.work ≤ s.frame.state.storage.work+
        Proofs.BeatsAllocationLayout.storageWork n 0 15+(4*n*18+10) ∧
      step.state.scalars.peak ≤ scalarBound out st.core.locals.memory ∧
      step.state.frame.state.storage.peak ≤ storageBound out ∧
      step.state.peak ≤ scalarBound out st.core.locals.memory+storageBound out ∧
      ∀ i, i < 16 → ∃ finalBuffer, step.state.frame.state.storage.lookup (owner st p i) = some finalBuffer ∧
        finalBuffer.items = (VVA a bf i).map Value.integer := by
  obtain ⟨out,fuel,step,bf,heap,allocated,ran,returned,breaking,rep,scope,sw,tw,sp,tp,peak,buffers,_⟩ :=
    stage_exec_full h entry n positive range length values s real strict base buf stored readonly limit
  exact ⟨out,fuel,step,bf,heap,allocated,ran,returned,breaking,rep,scope,sw,tw,sp,tp,peak,buffers⟩

end Proofs.BeatsInlineExec
