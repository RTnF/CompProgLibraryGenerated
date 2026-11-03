import Proofs.BeatsReceiverCalls
import Proofs.CppCallUnitFrame

namespace Proofs.BeatsReceiverRestore
open Proofs.CppNestedEval
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppNestedVectorBindings
open Proofs.CppNestedVectorStore Proofs.CppVector Proofs.CppBufferHeaders Proofs.CppCallFrame
open Proofs.BeatsModel Proofs.BeatsRep Proofs.BeatsExec Proofs.BeatsPrepare
open Proofs.BeatsReceiverCalls Proofs.BeatsInstance Proofs.BeatsConstructReceiver
open Proofs.IntSim Proofs.DoublingNested Proofs.MultiVecCallB
open Proofs.BellmanFordExec (M31)

theorem scalar_cell_eq {before after : NState} (effects : CallEffects before after)
    (memory : after.scalars.memory = before.scalars.memory) (slot : Nat) (ty : Ty) :
    after.scalarCell slot ty = before.scalarCell slot ty := by
  simp only [NState.scalarCell,NState.scalarSlot,effects.slots,effects.scalarBindings,memory]

theorem scalars_kept {before after : NState} {base n : Nat} (fields : Scalars before base n)
    (effects : CallEffects before after) (memory : after.scalars.memory = before.scalars.memory) :
    Scalars after base n := by
  obtain ⟨infBinding,inf⟩ := fields.inf
  obtain ⟨sizeBinding,size⟩ := fields.size
  exact ⟨⟨infBinding,(scalar_cell_eq effects memory _ _).trans inf⟩,
    ⟨sizeBinding,(scalar_cell_eq effects memory _ _).trans size⟩⟩

-- Values change, but headers and grants stay fixed. Recover every operation
-- precondition from those facts and the actual new payloads, without assuming
-- an already represented next receiver.
theorem restore_bvecs {before after : NState} {sl vb V vsc : Nat → Nat} {oldBuffers : Nat → Buffer Value}
    {oldValues newValues : Nat → List Int}
    (vectors : BVecs before sl vb V vsc oldBuffers oldValues) (effects : CallEffects before after)
    (valid : after.frame.state.wellFormed = true)
    (payloads : ∀ i, i < 15 → ∃ buffer, after.frame.state.storage.lookup (V i) = some buffer ∧
      buffer.items = (newValues i).map Value.integer) :
    BVecs after sl vb V vsc (fieldBuffer after V) newValues := by
  have facts (i : Nat) (bound : i < 15) :
      after.frame.state.storage.lookup (V i) = some (fieldBuffer after V i) ∧
      (fieldBuffer after V i).items = (newValues i).map Value.integer ∧
      (fieldBuffer after V i).Valid (accepts (.integer (bty i))) ∧
      (fieldBuffer after V i).limit = Proofs.CppVectorBindings.sizeLimit (bty i) ∧
      (fieldBuffer after V i).owner = V i ∧ (newValues i).length < 18446744073709551616 := by
    obtain ⟨buffer,found,items⟩ := payloads i bound
    have chosen : fieldBuffer after V i = buffer := by simp only [fieldBuffer,found,Option.getD_some]
    rw [chosen]
    have tag : after.frame.state.forest.lookup (V i) = some ⟨.integer (bty i),none,some (vsc i),[]⟩ := by
      rw [effects.headers.forest]
      exact (vectors.ok i bound).vtag
    obtain ⟨stored,again,owner,payload⟩ := Proofs.CppNestedFacts.wellFormed_pair after.frame.state (V i) _ valid tag
    have same : stored = buffer := Option.some.inj (again.symm.trans found)
    subst stored
    have header := effects.headers.buffers (V i)
    rw [found,(vectors.ok i bound).vfound] at header
    have signatureEq := Option.some.inj header
    have limitEq := congrArg Signature.limit signatureEq
    have sizeEq := congrArg Signature.size signatureEq
    refine ⟨found,items,payload.1,limitEq.trans (vectors.limit i bound),owner,?_⟩
    have oldSmall := vectors.small i bound
    change buffer.items.length = (oldBuffers i).items.length at sizeEq
    rw [items,vectors.items i bound,List.length_map,List.length_map] at sizeEq
    omega
  refine ⟨?_,vectors.dist,?_,?_,?_,?_,?_⟩
  · intro i bound
    have old := vectors.ok i bound
    refine ⟨valid,?_,?_,?_,(facts i bound).1,?_,?_,old.perm,?_,?_⟩
    · simpa only [NState.vectorSlot,effects.slots] using old.slot
    · rw [effects.vectorBindings]; exact old.binding
    · rw [effects.headers.forest]; exact old.vtag
    · rw [effects.flags,effects.headers.forest]; exact old.lengths
    · rw [effects.flags]; exact old.flag
    · exact effects.contexts old.strict
    · rw [effects.base,effects.memoryLength]; exact old.base
  · intro i bound; exact (facts i bound).2.1
  · intro i bound; exact (facts i bound).2.2.1
  · intro i bound; exact (facts i bound).2.2.2.1
  · intro i bound; exact (facts i bound).2.2.2.2.1
  · intro i bound; exact (facts i bound).2.2.2.2.2

private theorem sim_allowed {d : Nat} {a b : Command} (same : Sim d a b) :
    Proofs.CppNoResizeScope.Allowed a = Proofs.CppNoResizeScope.Allowed b := by
  induction same with
  | prim => rfl
  | dec => rfl
  | seq _ _ ih1 ih2 => simp only [Proofs.CppNoResizeScope.Allowed,ih1,ih2]
  | scope _ ih => exact ih
  | branch _ _ ih1 ih2 => simp only [Proofs.CppNoResizeScope.Allowed,ih1,ih2]
  | whileLoop _ ih => exact ih
  | breakLoop => rfl

private theorem allowed_w6 (op : Nat) (rest : Command) :
    Proofs.CppNoResizeScope.Allowed (W6 op rest) = Proofs.CppNoResizeScope.Allowed rest := by
  simp only [Proofs.CppNoResizeScope.Allowed,Proofs.CppNoResizeStmt.Allowed,
    Proofs.CppScalarFrame.Scalar,Bool.true_and]

private theorem allowed_init (o : Nat) (rest : Command) :
    Proofs.CppNoResizeScope.Allowed (ApInitc0 o rest) = Proofs.CppNoResizeScope.Allowed rest := by rfl

private theorem allowed_chunk0 (o : Nat) (rest : Command) :
    Proofs.CppNoResizeScope.Allowed (ApplyLoopc0 o rest) = Proofs.CppNoResizeScope.Allowed rest := by rfl

private theorem allowed_chunk1 (o : Nat) (rest : Command) :
    Proofs.CppNoResizeScope.Allowed (ApplyLoopc1 o rest) = Proofs.CppNoResizeScope.Allowed rest := by rfl

private theorem allowed_chunk2 (o : Nat) (rest : Command) :
    Proofs.CppNoResizeScope.Allowed (ApplyLoopc2 o rest) = Proofs.CppNoResizeScope.Allowed rest := by rfl

private theorem allowed_chunk3 (o : Nat) (rest : Command) :
    Proofs.CppNoResizeScope.Allowed (ApplyLoopc3 o rest) = Proofs.CppNoResizeScope.Allowed rest := by rfl

private theorem allowed_chunk4 (o : Nat) (rest : Command) :
    Proofs.CppNoResizeScope.Allowed (ApplyLoopc4 o rest) = Proofs.CppNoResizeScope.Allowed rest := by rfl

private theorem allowed_chunk5 (o : Nat) (rest : Command) :
    Proofs.CppNoResizeScope.Allowed (ApplyLoopc5 o rest) = Proofs.CppNoResizeScope.Allowed rest := by rfl

private theorem allowed_chunk6 (o : Nat) (rest : Command) :
    Proofs.CppNoResizeScope.Allowed (ApplyLoopc6 o rest) = Proofs.CppNoResizeScope.Allowed rest := by rfl

private theorem allowed_chunk7 (o : Nat) (rest : Command) :
    Proofs.CppNoResizeScope.Allowed (ApplyLoopc7 o rest) = Proofs.CppNoResizeScope.Allowed rest := by rfl

private theorem allowed_chunk8 (o : Nat) (rest : Command) :
    Proofs.CppNoResizeScope.Allowed (ApplyLoopc8 o rest) = Proofs.CppNoResizeScope.Allowed rest := by rfl

private theorem allowed_chunk9 (o : Nat) (rest : Command) :
    Proofs.CppNoResizeScope.Allowed (ApplyLoopc9 o rest) = Proofs.CppNoResizeScope.Allowed rest := by rfl

private theorem allowed_chunk10 (o : Nat) (rest : Command) :
    Proofs.CppNoResizeScope.Allowed (ApplyLoopc10 o rest) = Proofs.CppNoResizeScope.Allowed rest := by rfl

private theorem allowed_chunk11 (o : Nat) (rest : Command) :
    Proofs.CppNoResizeScope.Allowed (ApplyLoopc11 o rest) = Proofs.CppNoResizeScope.Allowed rest := by rfl

private theorem allowed_chunk12 (o : Nat) (rest : Command) :
    Proofs.CppNoResizeScope.Allowed (ApplyLoopc12 o rest) = Proofs.CppNoResizeScope.Allowed rest := by rfl

private theorem allowed_chunk13 (o : Nat) (rest : Command) :
    Proofs.CppNoResizeScope.Allowed (ApplyLoopc13 o rest) = Proofs.CppNoResizeScope.Allowed rest := by rfl

private theorem allowed_loop_body (o : Nat) : Proofs.CppNoResizeScope.Allowed (ApplyLoopBody o) = true := by
  unfold ApplyLoopBody
  rw [allowed_chunk0,allowed_chunk1,allowed_chunk2,allowed_chunk3,allowed_chunk4,allowed_chunk5,allowed_chunk6,allowed_chunk7,allowed_chunk8,allowed_chunk9,allowed_chunk10,allowed_chunk11,allowed_chunk12,allowed_chunk13]
  rfl

private theorem allowed_a_loop (o : Nat) : Proofs.CppNoResizeScope.Allowed (ALoop o) = true := by
  change (Proofs.CppNoResizeScope.Allowed (ApplyLoopBody o) && true) = true
  rw [allowed_loop_body]
  rfl
private theorem allowed_u_loop (o : Nat) : Proofs.CppNoResizeScope.Allowed (ULoop o) = true := by rfl

private theorem allowed_apply (o : Nat) : Proofs.CppNoResizeScope.Allowed (ApplyOpCmd o) = true := by
  change Proofs.CppNoResizeScope.Allowed (ApInitc0 o (.sequence (ALoop o) (.sequence (ULoop o) (.primitive .skip)))) = true
  rw [allowed_init]
  change (Proofs.CppNoResizeScope.Allowed (ALoop o) && (Proofs.CppNoResizeScope.Allowed (ULoop o) && true)) = true
  rw [allowed_a_loop,allowed_u_loop]
  rfl

theorem allowed_chmin : Proofs.CppNoResizeScope.Allowed SegmentTreeBeats_chmin.body = true := by
  obtain ⟨tail,body,same⟩ := tail_chmin
  rw [body,allowed_w6,← sim_allowed same]
  exact allowed_apply 20

theorem allowed_chmax : Proofs.CppNoResizeScope.Allowed SegmentTreeBeats_chmax.body = true := by
  obtain ⟨tail,body,same⟩ := tail_chmax
  rw [body,allowed_w6,← sim_allowed same]
  exact allowed_apply 20

theorem allowed_add_val : Proofs.CppNoResizeScope.Allowed SegmentTreeBeats_add_val.body = true := by
  obtain ⟨tail,body,same⟩ := tail_add_val
  rw [body,allowed_w6,← sim_allowed same]
  exact allowed_apply 20

theorem allowed_update_val : Proofs.CppNoResizeScope.Allowed SegmentTreeBeats_update_val.body = true := by
  obtain ⟨tail,body,same⟩ := tail_update_val
  rw [body,allowed_w6,← sim_allowed same]
  exact allowed_apply 20

theorem allowed_calc_max : Proofs.CppNoResizeScope.Allowed SegmentTreeBeats_calc_max.body = true := by decide

theorem allowed_calc_min : Proofs.CppNoResizeScope.Allowed SegmentTreeBeats_calc_min.body = true := by decide

variable {SC : Nat}

theorem chmin (receiver : NState) (base : Nat) (sl vb V vsc : Nat → Nat) (vbuf : Nat → Buffer Value) {b : BS}
    (hv : BVecs receiver sl vb V vsc vbuf (VVB b)) {n L : Nat} {ys : List Int} {t : BT} {H : Heap} (R : BRepS n L SC ys b t H)
    (fields : Scalars receiver base n) (range : 4*n < 2147483648)
    (qa qb : Nat) (x : Int) (hqa : qa < M31) (hqb : qb < M31) (hx : -INF < x ∧ x < INF) (hSM : SC < M31)
    (safe : chminSafe qa qb x t 0 n) (qaExpr qbExpr valueExpr : NExpr)
      (qaScalar : qaExpr.scalarOnly = true) (qbScalar : qbExpr.scalarOnly = true) (valueScalar : valueExpr.scalarOnly = true)
      (qaType : qaExpr.resultType = i32) (qbType : qbExpr.resultType = i32) (valueType : valueExpr.resultType = s64)
    (qaValue : qaExpr.denote (envOf receiver) = some (qa : Int)) (qbValue : qbExpr.denote (envOf receiver) = some (qb : Int)) (inputValue : valueExpr.denote (envOf receiver) = some x) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare receiver SegmentTreeBeats_chmin.parameters (vargs sl 0 15 ++ [.value (infExpr base), .value (sizeExpr base), .value qaExpr, .value qbExpr, .value valueExpr]) = some Sinit ∧
      SegmentTreeBeats_chmin.callFuel fuel receiver (vargs sl 0 15 ++ [.value (infExpr base), .value (sizeExpr base), .value qaExpr, .value qbExpr, .value valueExpr]) = .finished (res, Ret.unit) ∧
      ∃ (bf : BS) (Hf : Heap), BRepS n (methodCapacity L) SC (rangeMin 0 qa qb x ys) bf (chminBT qa qb x t 0 n) Hf ∧
        ScalarPostMB 333 (mvBeats receiver V vsc hv.dist) receiver Sinit res ((infExpr base).nodes + ((sizeExpr base).nodes + (qaExpr.nodes + (qbExpr.nodes + valueExpr.nodes))))
          (nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12 + 37) receiver.scalars.memory (nodesOf t * 47 + innerOf t * 6 + 3) (VVB bf) ∧
        CallEffects receiver res ∧ Scalars res base n ∧
        BVecs res sl vb V vsc (fieldBuffer res V) (VVB bf) := by
  obtain ⟨Sinit,fuel,res,prepared,ran,bf,Hf,rep,post⟩ := Proofs.BeatsReceiverCalls.chmin receiver base sl vb V vsc vbuf hv R fields range
    qa qb x hqa hqb hx hSM safe qaExpr qbExpr valueExpr
      qaScalar qbScalar valueScalar qaType qbType valueType qaValue qbValue inputValue
  have effects := Proofs.CppCallUnitFrame.call_headers SegmentTreeBeats_chmin fuel receiver res _ .unit
    rfl allowed_chmin (hv.ok 0 (by decide)).strict ran
  have fieldsAfter := scalars_kept fields effects post.scalarMemory
  have vectors : BVecs res sl vb V vsc (fieldBuffer res V) (VVB bf) :=
    restore_bvecs hv effects post.valid (fun i bound => post.vector i (by show i < 15; exact bound))
  exact ⟨Sinit,fuel,res,prepared,ran,bf,Hf,rep,post,effects,fieldsAfter,vectors⟩

theorem chmax (receiver : NState) (base : Nat) (sl vb V vsc : Nat → Nat) (vbuf : Nat → Buffer Value) {b : BS}
    (hv : BVecs receiver sl vb V vsc vbuf (VVB b)) {n L : Nat} {ys : List Int} {t : BT} {H : Heap} (R : BRepS n L SC ys b t H)
    (fields : Scalars receiver base n) (range : 4*n < 2147483648)
    (qa qb : Nat) (x : Int) (hqa : qa < M31) (hqb : qb < M31) (hx : -INF < x ∧ x < INF) (hSM : SC < M31)
    (safe : chmaxSafe qa qb x t 0 n) (qaExpr qbExpr valueExpr : NExpr)
      (qaScalar : qaExpr.scalarOnly = true) (qbScalar : qbExpr.scalarOnly = true) (valueScalar : valueExpr.scalarOnly = true)
      (qaType : qaExpr.resultType = i32) (qbType : qbExpr.resultType = i32) (valueType : valueExpr.resultType = s64)
    (qaValue : qaExpr.denote (envOf receiver) = some (qa : Int)) (qbValue : qbExpr.denote (envOf receiver) = some (qb : Int)) (inputValue : valueExpr.denote (envOf receiver) = some x) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare receiver SegmentTreeBeats_chmax.parameters (vargs sl 0 15 ++ [.value (infExpr base), .value (sizeExpr base), .value qaExpr, .value qbExpr, .value valueExpr]) = some Sinit ∧
      SegmentTreeBeats_chmax.callFuel fuel receiver (vargs sl 0 15 ++ [.value (infExpr base), .value (sizeExpr base), .value qaExpr, .value qbExpr, .value valueExpr]) = .finished (res, Ret.unit) ∧
      ∃ (bf : BS) (Hf : Heap), BRepS n (methodCapacity L) SC (rangeMap (fun v => max v x) 0 qa qb ys) bf (chmaxBT qa qb x t 0 n) Hf ∧
        ScalarPostMB 333 (mvBeats receiver V vsc hv.dist) receiver Sinit res ((infExpr base).nodes + ((sizeExpr base).nodes + (qaExpr.nodes + (qbExpr.nodes + valueExpr.nodes))))
          (nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12 + 37) receiver.scalars.memory (nodesOf t * 47 + innerOf t * 6 + 3) (VVB bf) ∧
        CallEffects receiver res ∧ Scalars res base n ∧
        BVecs res sl vb V vsc (fieldBuffer res V) (VVB bf) := by
  obtain ⟨Sinit,fuel,res,prepared,ran,bf,Hf,rep,post⟩ := Proofs.BeatsReceiverCalls.chmax receiver base sl vb V vsc vbuf hv R fields range
    qa qb x hqa hqb hx hSM safe qaExpr qbExpr valueExpr
      qaScalar qbScalar valueScalar qaType qbType valueType qaValue qbValue inputValue
  have effects := Proofs.CppCallUnitFrame.call_headers SegmentTreeBeats_chmax fuel receiver res _ .unit
    rfl allowed_chmax (hv.ok 0 (by decide)).strict ran
  have fieldsAfter := scalars_kept fields effects post.scalarMemory
  have vectors : BVecs res sl vb V vsc (fieldBuffer res V) (VVB bf) :=
    restore_bvecs hv effects post.valid (fun i bound => post.vector i (by show i < 15; exact bound))
  exact ⟨Sinit,fuel,res,prepared,ran,bf,Hf,rep,post,effects,fieldsAfter,vectors⟩

theorem add_val (receiver : NState) (base : Nat) (sl vb V vsc : Nat → Nat) (vbuf : Nat → Buffer Value) {b : BS}
    (hv : BVecs receiver sl vb V vsc vbuf (VVB b)) {n L : Nat} {ys : List Int} {t : BT} {H : Heap} (R : BRepS n L SC ys b t H)
    (fields : Scalars receiver base n) (range : 4*n < 2147483648)
    (qa qb : Nat) (x : Int) (hqa : qa < M31) (hqb : qb < M31) (hx : -INF < x ∧ x < INF) (hSM : SC < M31)
    (safe : addSafeRec qa qb x t 0 n) (qaExpr qbExpr valueExpr : NExpr)
      (qaScalar : qaExpr.scalarOnly = true) (qbScalar : qbExpr.scalarOnly = true) (valueScalar : valueExpr.scalarOnly = true)
      (qaType : qaExpr.resultType = i32) (qbType : qbExpr.resultType = i32) (valueType : valueExpr.resultType = s64)
    (qaValue : qaExpr.denote (envOf receiver) = some (qa : Int)) (qbValue : qbExpr.denote (envOf receiver) = some (qb : Int)) (inputValue : valueExpr.denote (envOf receiver) = some x) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare receiver SegmentTreeBeats_add_val.parameters (vargs sl 0 15 ++ [.value (infExpr base), .value (sizeExpr base), .value qaExpr, .value qbExpr, .value valueExpr]) = some Sinit ∧
      SegmentTreeBeats_add_val.callFuel fuel receiver (vargs sl 0 15 ++ [.value (infExpr base), .value (sizeExpr base), .value qaExpr, .value qbExpr, .value valueExpr]) = .finished (res, Ret.unit) ∧
      ∃ (bf : BS) (Hf : Heap), BRepS n (methodCapacity L) SC (rangeMap (fun v => v + x) 0 qa qb ys) bf (addRec qa qb x t 0 n) Hf ∧
        ScalarPostMB 333 (mvBeats receiver V vsc hv.dist) receiver Sinit res ((infExpr base).nodes + ((sizeExpr base).nodes + (qaExpr.nodes + (qbExpr.nodes + valueExpr.nodes))))
          (nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12 + 37) receiver.scalars.memory (nodesOf t * 47 + innerOf t * 6 + 3) (VVB bf) ∧
        CallEffects receiver res ∧ Scalars res base n ∧
        BVecs res sl vb V vsc (fieldBuffer res V) (VVB bf) := by
  obtain ⟨Sinit,fuel,res,prepared,ran,bf,Hf,rep,post⟩ := Proofs.BeatsReceiverCalls.add_val receiver base sl vb V vsc vbuf hv R fields range
    qa qb x hqa hqb hx hSM safe qaExpr qbExpr valueExpr
      qaScalar qbScalar valueScalar qaType qbType valueType qaValue qbValue inputValue
  have effects := Proofs.CppCallUnitFrame.call_headers SegmentTreeBeats_add_val fuel receiver res _ .unit
    rfl allowed_add_val (hv.ok 0 (by decide)).strict ran
  have fieldsAfter := scalars_kept fields effects post.scalarMemory
  have vectors : BVecs res sl vb V vsc (fieldBuffer res V) (VVB bf) :=
    restore_bvecs hv effects post.valid (fun i bound => post.vector i (by show i < 15; exact bound))
  exact ⟨Sinit,fuel,res,prepared,ran,bf,Hf,rep,post,effects,fieldsAfter,vectors⟩

theorem update_val (receiver : NState) (base : Nat) (sl vb V vsc : Nat → Nat) (vbuf : Nat → Buffer Value) {b : BS}
    (hv : BVecs receiver sl vb V vsc vbuf (VVB b)) {n L : Nat} {ys : List Int} {t : BT} {H : Heap} (R : BRepS n L SC ys b t H)
    (fields : Scalars receiver base n) (range : 4*n < 2147483648)
    (qa qb : Nat) (x : Int) (hqa : qa < M31) (hqb : qb < M31) (hx : -INF < x ∧ x < INF) (hSM : SC < M31)
    (safe : setSafeRec qa qb x t 0 n) (qaExpr qbExpr valueExpr : NExpr)
      (qaScalar : qaExpr.scalarOnly = true) (qbScalar : qbExpr.scalarOnly = true) (valueScalar : valueExpr.scalarOnly = true)
      (qaType : qaExpr.resultType = i32) (qbType : qbExpr.resultType = i32) (valueType : valueExpr.resultType = s64)
    (qaValue : qaExpr.denote (envOf receiver) = some (qa : Int)) (qbValue : qbExpr.denote (envOf receiver) = some (qb : Int)) (inputValue : valueExpr.denote (envOf receiver) = some x) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare receiver SegmentTreeBeats_update_val.parameters (vargs sl 0 15 ++ [.value (infExpr base), .value (sizeExpr base), .value qaExpr, .value qbExpr, .value valueExpr]) = some Sinit ∧
      SegmentTreeBeats_update_val.callFuel fuel receiver (vargs sl 0 15 ++ [.value (infExpr base), .value (sizeExpr base), .value qaExpr, .value qbExpr, .value valueExpr]) = .finished (res, Ret.unit) ∧
      ∃ (bf : BS) (Hf : Heap), BRepS n (methodCapacity L) SC (rangeMap (fun _ => x) 0 qa qb ys) bf (setRec qa qb x t 0 n) Hf ∧
        ScalarPostMB 333 (mvBeats receiver V vsc hv.dist) receiver Sinit res ((infExpr base).nodes + ((sizeExpr base).nodes + (qaExpr.nodes + (qbExpr.nodes + valueExpr.nodes))))
          (nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12 + 37) receiver.scalars.memory (nodesOf t * 47 + innerOf t * 6 + 3) (VVB bf) ∧
        CallEffects receiver res ∧ Scalars res base n ∧
        BVecs res sl vb V vsc (fieldBuffer res V) (VVB bf) := by
  obtain ⟨Sinit,fuel,res,prepared,ran,bf,Hf,rep,post⟩ := Proofs.BeatsReceiverCalls.update_val receiver base sl vb V vsc vbuf hv R fields range
    qa qb x hqa hqb hx hSM safe qaExpr qbExpr valueExpr
      qaScalar qbScalar valueScalar qaType qbType valueType qaValue qbValue inputValue
  have effects := Proofs.CppCallUnitFrame.call_headers SegmentTreeBeats_update_val fuel receiver res _ .unit
    rfl allowed_update_val (hv.ok 0 (by decide)).strict ran
  have fieldsAfter := scalars_kept fields effects post.scalarMemory
  have vectors : BVecs res sl vb V vsc (fieldBuffer res V) (VVB bf) :=
    restore_bvecs hv effects post.valid (fun i bound => post.vector i (by show i < 15; exact bound))
  exact ⟨Sinit,fuel,res,prepared,ran,bf,Hf,rep,post,effects,fieldsAfter,vectors⟩

theorem calc_max (receiver : NState) (base : Nat) (sl vb V vsc : Nat → Nat) (vbuf : Nat → Buffer Value) {b : BS}
    (hv : BVecs receiver sl vb V vsc vbuf (VVB b)) {n L : Nat} {ys : List Int} {t : BT} {H : Heap} (R : BRepS n L SC ys b t H)
    (fields : Scalars receiver base n) (range : 4*n < 2147483648)
    (qa qb : Nat) (hqa : qa < M31) (hqb : qb < M31) (hSM : SC < M31)
    (safe : calcSafe qa qb t 0 n) (qaExpr qbExpr : NExpr)
      (qaScalar : qaExpr.scalarOnly = true) (qbScalar : qbExpr.scalarOnly = true)
      (qaType : qaExpr.resultType = i32) (qbType : qbExpr.resultType = i32)
    (qaValue : qaExpr.denote (envOf receiver) = some (qa : Int)) (qbValue : qbExpr.denote (envOf receiver) = some (qb : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState) (xf : Int),
      prepare receiver SegmentTreeBeats_calc_max.parameters (vargs sl 0 15 ++ [.value (infExpr base), .value (sizeExpr base), .value qaExpr, .value qbExpr]) = some Sinit ∧
      SegmentTreeBeats_calc_max.callFuel fuel receiver (vargs sl 0 15 ++ [.value (infExpr base), .value (sizeExpr base), .value qaExpr, .value qbExpr]) = .finished (res, Ret.scalar xf) ∧
      xf = max (-INF) (rangeMaxOf 0 qa qb ys) ∧
      ∃ (bf : BS) (Hf : Heap), BRepS n (methodCapacity L) SC ys bf (calcMaxBT qa qb t 0 n).1 Hf ∧
        ScalarPostMB 400 (mvBeats receiver V vsc hv.dist) receiver Sinit res ((infExpr base).nodes + ((sizeExpr base).nodes + (qaExpr.nodes + qbExpr.nodes)))
          (nodesOf t * 72254 + 4 + 5000 + 16 + 10 + 36) receiver.scalars.memory (nodesOf t * 24 + 3) (VVB bf) ∧
        CallEffects receiver res ∧ Scalars res base n ∧
        BVecs res sl vb V vsc (fieldBuffer res V) (VVB bf) := by
  obtain ⟨Sinit,fuel,res,xf,prepared,ran,value,bf,Hf,rep,post⟩ := Proofs.BeatsReceiverCalls.calc_max receiver base sl vb V vsc vbuf hv R fields range
    qa qb hqa hqb hSM safe qaExpr qbExpr
      qaScalar qbScalar qaType qbType qaValue qbValue
  have effects := Proofs.CppCallFrame.call_headers SegmentTreeBeats_calc_max fuel receiver res _ (.scalar xf) s64
    rfl allowed_calc_max (hv.ok 0 (by decide)).strict ran
  have fieldsAfter := scalars_kept fields effects post.scalarMemory
  have vectors : BVecs res sl vb V vsc (fieldBuffer res V) (VVB bf) :=
    restore_bvecs hv effects post.valid (fun i bound => post.vector i (by show i < 15; exact bound))
  exact ⟨Sinit,fuel,res,xf,prepared,ran,value,bf,Hf,rep,post,effects,fieldsAfter,vectors⟩

theorem calc_min (receiver : NState) (base : Nat) (sl vb V vsc : Nat → Nat) (vbuf : Nat → Buffer Value) {b : BS}
    (hv : BVecs receiver sl vb V vsc vbuf (VVB b)) {n L : Nat} {ys : List Int} {t : BT} {H : Heap} (R : BRepS n L SC ys b t H)
    (fields : Scalars receiver base n) (range : 4*n < 2147483648)
    (qa qb : Nat) (hqa : qa < M31) (hqb : qb < M31) (hSM : SC < M31)
    (safe : calcSafe qa qb t 0 n) (qaExpr qbExpr : NExpr)
      (qaScalar : qaExpr.scalarOnly = true) (qbScalar : qbExpr.scalarOnly = true)
      (qaType : qaExpr.resultType = i32) (qbType : qbExpr.resultType = i32)
    (qaValue : qaExpr.denote (envOf receiver) = some (qa : Int)) (qbValue : qbExpr.denote (envOf receiver) = some (qb : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState) (xf : Int),
      prepare receiver SegmentTreeBeats_calc_min.parameters (vargs sl 0 15 ++ [.value (infExpr base), .value (sizeExpr base), .value qaExpr, .value qbExpr]) = some Sinit ∧
      SegmentTreeBeats_calc_min.callFuel fuel receiver (vargs sl 0 15 ++ [.value (infExpr base), .value (sizeExpr base), .value qaExpr, .value qbExpr]) = .finished (res, Ret.scalar xf) ∧
      xf = min INF (rangeMinOf 0 qa qb ys) ∧
      ∃ (bf : BS) (Hf : Heap), BRepS n (methodCapacity L) SC ys bf (calcMinBT qa qb t 0 n).1 Hf ∧
        ScalarPostMB 400 (mvBeats receiver V vsc hv.dist) receiver Sinit res ((infExpr base).nodes + ((sizeExpr base).nodes + (qaExpr.nodes + qbExpr.nodes)))
          (nodesOf t * 72254 + 4 + 5000 + 16 + 10 + 36) receiver.scalars.memory (nodesOf t * 24 + 3) (VVB bf) ∧
        CallEffects receiver res ∧ Scalars res base n ∧
        BVecs res sl vb V vsc (fieldBuffer res V) (VVB bf) := by
  obtain ⟨Sinit,fuel,res,xf,prepared,ran,value,bf,Hf,rep,post⟩ := Proofs.BeatsReceiverCalls.calc_min receiver base sl vb V vsc vbuf hv R fields range
    qa qb hqa hqb hSM safe qaExpr qbExpr
      qaScalar qbScalar qaType qbType qaValue qbValue
  have effects := Proofs.CppCallFrame.call_headers SegmentTreeBeats_calc_min fuel receiver res _ (.scalar xf) s64
    rfl allowed_calc_min (hv.ok 0 (by decide)).strict ran
  have fieldsAfter := scalars_kept fields effects post.scalarMemory
  have vectors : BVecs res sl vb V vsc (fieldBuffer res V) (VVB bf) :=
    restore_bvecs hv effects post.valid (fun i bound => post.vector i (by show i < 15; exact bound))
  exact ⟨Sinit,fuel,res,xf,prepared,ran,value,bf,Hf,rep,post,effects,fieldsAfter,vectors⟩

end Proofs.BeatsReceiverRestore
