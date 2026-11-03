import Proofs.BeatsAllocationArgs
import Proofs.BeatsWideCtorExec
import Proofs.BeatsBindingRun

namespace Proofs.BeatsWideCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.CppNestedVectorStore Proofs.CppVector Proofs.CppState
open Proofs.BeatsRep Proofs.BeatsExec Proofs.BeatsModel Proofs.BeatsSeparate
open Proofs.BeatsPrepare Proofs.MultiVecCallB Proofs.MultiVec
open Proofs.GenState Proofs.ScalarCall Proofs.IntSim Proofs.DoublingNested
open Proofs.DoublingCall

-- This is the candidate's normalized constructor body, after allocation.
-- Its call boundary is explicit: the actual inlined construction stage still
-- needs a state/view correspondence with this prepared body.
def program : NProgram := ⟨vparams cty cw 0 16,.unit,WideCtorCmd 16⟩

theorem body_view (fuel : Nat) (s : NState) (long : 16 ≤ s.frame.bindings.length) :
    Proofs.BeatsBindingCycle.outcomeView (runFuel fuel program.body s) =
      runFuel fuel program.body (Proofs.BeatsBindingCycle.view s) :=
  Proofs.BeatsBindingCycle.run_view fuel _ s wide_ctor_core long

theorem inline_body_view (fuel : Nat) (s : NState)
    (slots : 16 ≤ s.slots.length) (bindings : 16 ≤ s.frame.bindings.length) :
    Proofs.BeatsBindingCycle.outcomeView (Proofs.BeatsSlotCycle.outcomeView
      (runFuel fuel (Proofs.CppSlotRename.command Proofs.BeatsSlotCycle.cycle program.body) s)) =
      runFuel fuel program.body (Proofs.BeatsBindingCycle.view (Proofs.BeatsSlotCycle.permute s)) := by
  simp only [program]
  rw [wide_ctor_cycle_runFuel fuel s slots]
  exact body_view fuel (Proofs.BeatsSlotCycle.permute s) bindings

theorem writable_body : WrM cw program.body = true := by decide

theorem prepare_frame (caller : NState) (sl vb V vsc : Nat → Nat) (m15 : Bool)
    (vbuf : Nat → Buffer Value) (vv : Nat → List Int)
    (hv : CVecs caller sl vb V vsc m15 vbuf vv) :
    ∃ prepared, prepare caller program.parameters (vargs sl 0 16) = some prepared ∧
      prepared.frame = ⟨caller.frame.state,caller.frame.rootWritable,bl cty V vsc cw 0 16⟩ ∧
      prepared.slots = slN 16 0 ∧ prepared.scope = caller.scope+1 ∧
      FWM (mvCtor caller V vsc m15 hv.dist) vv vbuf 0 prepared.frame := by
  obtain ⟨last,_,prepared,prep,slots,_,_,_,scope,frame,_,_,_⟩ :=
    prepare_gen caller 16 (by decide) cty cw sl vb V vsc
      (fun i => if i < 15 then true else m15) vbuf hv.ok [] program rfl (by simp)
  have fw := fw_init caller 16 (by decide) cty cw sl vb V vsc
    (fun i => if i < 15 then true else m15) vbuf hv.ok
    (fun k h => by simp [cw] at h; simp [h])
    (fun j k hj hk different writable => hv.dist j k hj (by simpa [cw] using writable) different)
    vv hv.items hv.valid hv.limit hv.owner hv.small
  rw [← frame] at fw
  exact ⟨prepared,prep,frame,slots,scope,fw⟩

private theorem call_extra_bound {cost bound : Nat} (h : cost ≤ bound) :
    cost + 2*16 + 0 + 2 ≤ bound + 34 := by omega

theorem call (caller : NState) (sl vb V vsc : Nat → Nat) (m15 : Bool)
    (vbuf : Nat → Buffer Value) (a : List Int) {b0 : BS}
    (hv : CVecs caller sl vb V vsc m15 vbuf (VVA a b0)) {n L S : Nat}
    (positive : 1 ≤ n) (capacity : 8*n+8 ≤ L) (range : 4*n < Proofs.BellmanFordExec.M31)
    (length : a.length = n) (values : InRange a) (stack : 34 ≤ S) (fresh : BFreshS L S b0) :
    ∃ (prepared : NState) (fuel : Nat) (res : NState),
      prepare caller program.parameters (vargs sl 0 16) = some prepared ∧
      program.callFuel fuel caller (vargs sl 0 16) = .finished (res,Ret.unit) ∧
      ∃ (bf : BS) (heap : Heap), BRepS n L S a bf (buildBT a 0 n) heap ∧
        ScalarPostMB 100 (mvCtor caller V vsc m15 hv.dist) caller prepared res 0
          (4*n*45414+100+34) caller.scalars.memory (4*n*18+10) (VVA a bf) := by
  obtain ⟨bf,heap,F,r,exec,ret,mem,vectors,cost,need,work,rep⟩ :=
    ctor_rep_wide (S := S) (mvCtor caller V vsc m15 hv.dist) rfl
      (fun v bound => by show cty v = s64; simp [cty,bound])
      (fun v lower upper => by show cty v = i32; simp [cty]; omega)
      (by show cty 15 = s64; simp [cty]) (callerP caller) a n L positive capacity range length values stack
      b0 fresh.valid fresh.lens fresh.lo fresh.hi fresh.mxv fresh.smx fresh.mxc fresh.mnv fresh.smn
      fresh.mnc fresh.len fresh.ladd fresh.lval fresh.lov fresh.hiv
  obtain ⟨prepared,fuel,res,prep,ran,post⟩ := beats_call_unit 100 caller 16 (by decide) cty cw sl vb V vsc
    (fun i => if i < 15 then true else m15) vbuf hv.ok
    (fun k h => by simp [cw] at h; simp [h])
    (fun j k hj hk different writable => hv.dist j k hj (by simpa [cw] using writable) different)
    cw (fun k h => ⟨h,by simp [cw] at h; simp [h]⟩)
    [] program rfl (by intro y member; simp at member)
    (VVA a b0) hv.items hv.valid hv.limit hv.owner hv.small writable_body rfl F r exec ret
    (by omega) (by simp) (4*n*45414+100+34) (call_extra_bound cost)
  refine ⟨prepared,fuel,res,prep,ran,bf,heap,rep,?_⟩
  have kept : r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [mem]
    simp only [gS_mem,callerP,List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [kept,vectors] at post
  exact post.relax (by simp) (Nat.le_refl _) work

-- Composition through the explicit normalized call. This is not yet the
-- runFuel theorem for the candidate's inlined allocation-and-body stage.
theorem allocated_call {st : Proofs.DynamicOwnedState.State} {p : Proofs.MultiVecDynamic.Parameter}
    {a : List Int} (input : Proofs.BeatsAllocation.Input st p a) (n : Nat)
    (positive : 1 ≤ n) (length : a.length = n) (range : 4*n < 2147483648) (values : InRange a)
    (s : NState) (real : Proofs.DynamicOwnedState.Realizes st s)
    (strict : ∀ owner c, s.frame.state.forest.context owner = some c → c ≤ s.scope)
    (base : s.scalars.baseMemory ≤ s.scalars.memory.length)
    (buf : Buffer Value) (stored : s.frame.state.storage.lookup p.owner = some buf)
    (readonly : p.writable = false) (limit : buf.limit = Proofs.CppVectorBindings.sizeLimit s64) :
    ∃ allocated prepared fuel res bf heap,
      runFuel 16 (Proofs.BeatsAllocation.fillPrefix 0 15) s = .finished ⟨allocated,none,false⟩ ∧
      prepare allocated program.parameters (vargs (Proofs.BeatsAllocationArgs.slot st) 0 16) = some prepared ∧
      program.callFuel fuel allocated (vargs (Proofs.BeatsAllocationArgs.slot st) 0 16) = .finished (res,Ret.unit) ∧
      BRepS n (8*n+8) 256 a bf (buildBT a 0 n) heap ∧
      res.scalars.memory = allocated.scalars.memory ∧ res.frame.bindings = allocated.frame.bindings ∧
      res.slots = allocated.slots ∧ res.scope = allocated.scope ∧
      res.frame.state.storage.work ≤ s.frame.state.storage.work+
        Proofs.BeatsAllocationLayout.storageWork n 0 15+(4*n*18+10) ∧
      res.scalars.work ≤ allocated.scalars.work+(4*n*45414+100+34) ∧
      ∀ i, i < 16 → ∃ finalBuffer, res.frame.state.storage.lookup (Proofs.BeatsAllocationArgs.owner st p i) = some finalBuffer ∧
        finalBuffer.items = (VVA a bf i).map Value.integer := by
  obtain ⟨allocated,prefixRun,_,work,args⟩ := Proofs.BeatsAllocationArgs.prefix_cvecs input n length range s real strict base
    buf stored readonly limit
  obtain ⟨prepared,fuel,res,prep,ran,bf,heap,rep,post⟩ := call allocated _ _ _ _ p.maximum
    (Proofs.BeatsAllocationArgs.buffer st n buf) a args positive (Nat.le_refl _) range length values
    (by decide) (Proofs.BeatsAllocationArgs.initial_fresh n)
  refine ⟨allocated,prepared,fuel,res,bf,heap,prefixRun,prep,ran,rep,post.scalarMemory,post.bindings,
    post.slots,post.scope,?_,?_,post.vector⟩
  · have bound := post.storageWork
    rw [work] at bound
    exact bound
  · simpa only [Nat.add_zero] using post.scalarWork

end Proofs.BeatsWideCall
