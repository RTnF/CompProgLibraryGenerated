import Proofs.BeatsConstructReceiver

namespace Proofs.BeatsReceiverCalls
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppNestedEval
open Proofs.CppNestedVectorStore Proofs.CppVector
open Proofs.BeatsModel Proofs.BeatsRep Proofs.BeatsExec Proofs.BeatsPrepare
open Proofs.IntSim Proofs.DoublingNested Proofs.MultiVecCallB Proofs.BeatsInstance
open Proofs.BellmanFordExec (M31)

-- These expressions read the two actual fields returned with the fifteen
-- vector slots. Their values are never substituted by ghost constants.
def infExpr (base : Nat) : NExpr := .variable s64 (base+15)
def sizeExpr (base : Nat) : NExpr := .variable i32 (base+16)

structure Scalars (state : NState) (base n : Nat) : Prop where
  inf : ∃ binding, state.scalarCell (base+15) s64 = some (binding,⟨s64,INF⟩)
  size : ∃ binding, state.scalarCell (base+16) i32 = some (binding,⟨i32,n⟩)

theorem scalars_of_layout {caller result : NState} {V : Nat → Nat} {n : Nat}
    {prefixCells : List Proofs.CppState.Cell}
    (layout : Proofs.BeatsConstructorFields.ExportLayout caller result V n prefixCells) :
    Scalars result caller.slots.length n :=
  ⟨⟨_,layout.infCell⟩,⟨_,layout.nCell⟩⟩

theorem inf_denote {state : NState} {base n : Nat} (fields : Scalars state base n) :
    (infExpr base).denote (envOf state) = some INF := by
  obtain ⟨binding,found⟩ := fields.inf
  simp only [infExpr,NExpr.denote,envOf,found,Option.map_some]

theorem size_denote {state : NState} {base n : Nat} (fields : Scalars state base n) :
    (sizeExpr base).denote (envOf state) = some (n : Int) := by
  obtain ⟨binding,found⟩ := fields.size
  simp only [sizeExpr,NExpr.denote,envOf,found,Option.map_some]

def methodCapacity (physical : Nat) : Nat := min physical 2147483647

theorem method_capacity_bound (physical : Nat) : methodCapacity physical < Proofs.BellmanFordExec.M31 := by
  have bound := Nat.min_le_right physical 2147483647
  change min physical 2147483647 < 2147483648
  omega

private theorem n_bound (n : Nat) (range : 4*n < 2147483648) : n < Proofs.BellmanFordExec.M31 := by
  change n < 2147483648
  omega

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
          (nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12 + 37) receiver.scalars.memory (nodesOf t * 47 + innerOf t * 6 + 3) (VVB bf) := by
  have hn := n_bound n range
  have hL := method_capacity_bound L
  have shrunk := R.cap_indices range
  exact Proofs.BeatsSeparate.segment_tree_beats_chmin receiver sl vb V vsc vbuf hv shrunk
    qa qb x hqa hqb hx hL hSM hn safe (infExpr base) (sizeExpr base) qaExpr qbExpr valueExpr
    rfl rfl qaScalar qbScalar valueScalar rfl rfl qaType qbType valueType (inf_denote fields) (size_denote fields) qaValue qbValue inputValue

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
          (nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12 + 37) receiver.scalars.memory (nodesOf t * 47 + innerOf t * 6 + 3) (VVB bf) := by
  have hn := n_bound n range
  have hL := method_capacity_bound L
  have shrunk := R.cap_indices range
  exact Proofs.BeatsSeparate.segment_tree_beats_chmax receiver sl vb V vsc vbuf hv shrunk
    qa qb x hqa hqb hx hL hSM hn safe (infExpr base) (sizeExpr base) qaExpr qbExpr valueExpr
    rfl rfl qaScalar qbScalar valueScalar rfl rfl qaType qbType valueType (inf_denote fields) (size_denote fields) qaValue qbValue inputValue

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
          (nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12 + 37) receiver.scalars.memory (nodesOf t * 47 + innerOf t * 6 + 3) (VVB bf) := by
  have hn := n_bound n range
  have hL := method_capacity_bound L
  have shrunk := R.cap_indices range
  exact Proofs.BeatsSeparate.segment_tree_beats_add_val receiver sl vb V vsc vbuf hv shrunk
    qa qb x hqa hqb hx hL hSM hn safe (infExpr base) (sizeExpr base) qaExpr qbExpr valueExpr
    rfl rfl qaScalar qbScalar valueScalar rfl rfl qaType qbType valueType (inf_denote fields) (size_denote fields) qaValue qbValue inputValue

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
          (nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12 + 37) receiver.scalars.memory (nodesOf t * 47 + innerOf t * 6 + 3) (VVB bf) := by
  have hn := n_bound n range
  have hL := method_capacity_bound L
  have shrunk := R.cap_indices range
  exact Proofs.BeatsSeparate.segment_tree_beats_update_val receiver sl vb V vsc vbuf hv shrunk
    qa qb x hqa hqb hx hL hSM hn safe (infExpr base) (sizeExpr base) qaExpr qbExpr valueExpr
    rfl rfl qaScalar qbScalar valueScalar rfl rfl qaType qbType valueType (inf_denote fields) (size_denote fields) qaValue qbValue inputValue

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
          (nodesOf t * 72254 + 4 + 5000 + 16 + 10 + 36) receiver.scalars.memory (nodesOf t * 24 + 3) (VVB bf) := by
  have hn := n_bound n range
  have hL := method_capacity_bound L
  have shrunk := R.cap_indices range
  exact Proofs.BeatsSeparate.segment_tree_beats_calc_max receiver sl vb V vsc vbuf hv shrunk
    qa qb hqa hqb hL hSM hn safe (infExpr base) (sizeExpr base) qaExpr qbExpr
    rfl rfl qaScalar qbScalar rfl rfl qaType qbType (inf_denote fields) (size_denote fields) qaValue qbValue

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
          (nodesOf t * 72254 + 4 + 5000 + 16 + 10 + 36) receiver.scalars.memory (nodesOf t * 24 + 3) (VVB bf) := by
  have hn := n_bound n range
  have hL := method_capacity_bound L
  have shrunk := R.cap_indices range
  exact Proofs.BeatsSeparate.segment_tree_beats_calc_min receiver sl vb V vsc vbuf hv shrunk
    qa qb hqa hqb hL hSM hn safe (infExpr base) (sizeExpr base) qaExpr qbExpr
    rfl rfl qaScalar qbScalar rfl rfl qaType qbType (inf_denote fields) (size_denote fields) qaValue qbValue


-- Construction derives both the vector family and the real scalar-field
-- reads required by the six wrappers above, from the original caller.
theorem construct_arguments (caller : NState) (slot vb inputOwner inputScope : Nat) (wb maximum : Bool)
    (buf : Buffer Value) (a : List Int)
    (ok : Proofs.MatMulPrepare.VOKG caller s64 slot vb inputOwner inputScope wb maximum buf)
    (items : buf.items = a.map Value.integer)
    (limit : buf.limit = Proofs.CppVectorBindings.sizeLimit s64) (n : Nat)
    (positive : 1 ≤ n) (range : 4*n < 2147483648) (length : a.length = n) (values : InRange a) :
    ∃ fuel result bf heap,
      Proofs.BeatsConstructCall.program.constructMembersFuel fuel caller [.vectorReference slot]
        Proofs.BeatsConstructorFields.vectorFields Proofs.BeatsConstructorFields.scalarFields =
        .finished (result,Proofs.CppConstructorMultiFinish.reference caller 15 2) ∧
      BRepS n (8*n+8) 256 a bf (buildBT a 0 n) heap ∧
      Scalars result caller.slots.length n ∧
      BVecs result (fun i => caller.slots.length+i) (fun i => caller.frame.bindings.length+i)
        (fun i => caller.frame.state.storage.objects.length+i) (fun _ => caller.scope)
        (Proofs.BeatsConstructReceiver.fieldBuffer result (fun i => caller.frame.state.storage.objects.length+i)) (VVB bf) := by
  obtain ⟨fuel,result,bf,heap,ran,rep,_,layout,vectors⟩ :=
    Proofs.BeatsConstructReceiver.construct_ready caller slot vb inputOwner inputScope wb maximum
      buf a ok items limit n positive range length values
  exact ⟨fuel,result,bf,heap,ran,rep,scalars_of_layout layout,vectors⟩

end Proofs.BeatsReceiverCalls
