namespace BeatsReceiverRestoreExamples
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppNestedEval
open Proofs.CppVector Proofs.CppNestedVectorStore Proofs.BeatsModel Proofs.BeatsRep Proofs.BeatsExec
open Proofs.BeatsInstance Proofs.BeatsPrepare Proofs.BeatsReceiverCalls Proofs.BeatsReceiverRestore
open Proofs.BeatsConstructReceiver Proofs.IntSim Proofs.DoublingNested
open Proofs.BellmanFordExec (M31)

-- No successful next receiver is assumed: the first operation derives its
-- complete vector/scalar preconditions, which the second operation consumes.
example (state : NState) (base : Nat) (sl vb V vsc : Nat → Nat) (buffers : Nat → Buffer Value)
    (b : BS) (n L SC : Nat) (ys : List Int) (t : BT) (H : Heap)
    (vectors : BVecs state sl vb V vsc buffers (VVB b)) (fields : Scalars state base n)
    (rep : BRepS n L SC ys b t H) (range : 4*n < 2147483648)
    (qa qb : Nat) (qaBound : qa < M31) (qbBound : qb < M31) (x : Int)
    (valueBound : -INF < x ∧ x < INF) (stackBound : SC < M31)
    (updateSafe : chminSafe qa qb x t 0 n)
    (querySafe : calcSafe qa qb (chminBT qa qb x t 0 n) 0 n) :
    ∃ firstFuel middle secondFuel result value,
      SegmentTreeBeats_chmin.callFuel firstFuel state
        (vargs sl 0 15 ++ [.value (infExpr base),.value (sizeExpr base),
          .value (.literal i32 qa),.value (.literal i32 qb),.value (.literal s64 x)]) = .finished (middle,.unit) ∧
      SegmentTreeBeats_calc_max.callFuel secondFuel middle
        (vargs sl 0 15 ++ [.value (infExpr base),.value (sizeExpr base),
          .value (.literal i32 qa),.value (.literal i32 qb)]) = .finished (result,.scalar value) ∧
      value = max (-INF) (rangeMaxOf 0 qa qb (rangeMin 0 qa qb x ys)) ∧
      Scalars result base n ∧ ∃ bf, BVecs result sl vb V vsc (fieldBuffer result V) (VVB bf) := by
  have qaValid := Proofs.BellmanFordExec.i32_valid_nat qa qaBound
  have qbValid := Proofs.BellmanFordExec.i32_valid_nat qb qbBound
  have xValid : s64.valid x = true := s64_valid_of_bounds x
    (by have := valueBound.1; unfold INF at this; omega) (by have := valueBound.2; unfold INF at this; omega)
  have literal (s : NState) (ty : Ty) (x : Int) (valid : ty.valid x = true) :
      (NExpr.literal ty x).denote (envOf s) = some x := by simp only [NExpr.denote,valid,ite_true]
  obtain ⟨_,firstFuel,middle,_,ran1,b1,H1,rep1,_,_,fields1,vectors1⟩ :=
    Proofs.BeatsReceiverRestore.chmin state base sl vb V vsc buffers vectors rep fields range
      qa qb x qaBound qbBound valueBound stackBound updateSafe (.literal i32 qa) (.literal i32 qb) (.literal s64 x)
      rfl rfl rfl rfl rfl rfl (literal state _ _ qaValid) (literal state _ _ qbValid) (literal state _ _ xValid)
  obtain ⟨_,secondFuel,result,value,_,ran2,meaning,b2,_,_,_,_,fields2,vectors2⟩ :=
    Proofs.BeatsReceiverRestore.calc_max middle base sl vb V vsc (fieldBuffer middle V) vectors1 rep1 fields1 range
      qa qb qaBound qbBound stackBound querySafe (.literal i32 qa) (.literal i32 qb)
      rfl rfl rfl rfl (literal middle _ _ qaValid) (literal middle _ _ qbValid)
  exact ⟨firstFuel,middle,secondFuel,result,value,ran1,ran2,meaning,fields2,b2,vectors2⟩

end BeatsReceiverRestoreExamples
