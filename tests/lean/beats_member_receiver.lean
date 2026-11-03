namespace GeneratedBeatsMemberReceiverExamples
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppNestedEval
open Proofs.CppVector Proofs.CppNestedVectorStore Proofs.BeatsModel Proofs.BeatsRep Proofs.BeatsExec
open Proofs.BeatsInstance Proofs.BeatsPrepare Proofs.BeatsReceiverCalls Proofs.BeatsReceiverRestore
open Proofs.BeatsConstructReceiver Proofs.IntSim Proofs.DoublingNested
open Proofs.BellmanFordExec (M31)

-- Use the actual generated receiver adapter for both calls. The first call
-- derives the updated scalar/vector conditions consumed by the second call.
theorem generated_update_query (state : NState) (base : Nat) (sl vb V vsc : Nat → Nat) (buffers : Nat → Buffer Value)
    (b : BS) (n L SC : Nat) (ys : List Int) (t : BT) (H : Heap)
    (vectors : BVecs state sl vb V vsc buffers (VVB b)) (fields : Scalars state base n)
    (rep : BRepS n L SC ys b t H) (range : 4*n < 2147483648)
    (qa qb : Nat) (qaBound : qa < M31) (qbBound : qb < M31) (x : Int)
    (valueBound : -INF < x ∧ x < INF) (stackBound : SC < M31)
    (updateSafe : chminSafe qa qb x t 0 n)
    (querySafe : calcSafe qa qb (chminBT qa qb x t 0 n) 0 n) :
    ∃ firstFuel middle secondFuel result value,
      BeatsMemberBundle.Calls.SegmentTreeBeats_chmin_callFuel firstFuel state
        (sourceReceiver sl base) false
        [.value (.literal i32 qa),.value (.literal i32 qb),.value (.literal s64 x)] = .finished (middle,.unit) ∧
      BeatsMemberBundle.Calls.SegmentTreeBeats_calc_max_callFuel secondFuel middle
        (sourceReceiver sl base) false
        [.value (.literal i32 qa),.value (.literal i32 qb)] = .finished (result,.scalar value) ∧
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
  have sourceRan1 := (generated_chmin_call firstFuel state sl base
    (.literal i32 qa) (.literal i32 qb) (.literal s64 x)).trans ran1
  have sourceRan2 := (generated_calc_max_call secondFuel middle sl base
    (.literal i32 qa) (.literal i32 qb)).trans ran2
  exact ⟨firstFuel,middle,secondFuel,result,value,sourceRan1,sourceRan2,meaning,fields2,b2,vectors2⟩

-- Start from the original caller's actual input grant. Construction success,
-- field reads, and the updated receiver needed for the query are all derived.
theorem generated_construct_update_query (caller : NState)
    (slot vb inputOwner inputScope : Nat) (wb maximum : Bool) (buf : Buffer Value) (a : List Int)
    (ok : Proofs.MatMulPrepare.VOKG caller s64 slot vb inputOwner inputScope wb maximum buf)
    (items : buf.items = a.map Value.integer)
    (limit : buf.limit = Proofs.CppVectorBindings.sizeLimit s64) (n : Nat)
    (positive : 1 ≤ n) (range : 4*n < 2147483648) (length : a.length = n) (values : InRange a)
    (qa qb : Nat) (qaBound : qa < M31) (qbBound : qb < M31) (x : Int)
    (valueBound : -INF < x ∧ x < INF)
    (updateSafe : chminSafe qa qb x (buildBT a 0 n) 0 n)
    (querySafe : calcSafe qa qb (chminBT qa qb x (buildBT a 0 n) 0 n) 0 n) :
    ∃ constructorFuel initial firstFuel middle secondFuel result value,
      BeatsMemberBundle.Construction.SegmentTreeBeats_construct0_exportFuel constructorFuel caller
        [.vectorReference slot] = .finished (initial,Proofs.CppConstructorMultiFinish.reference caller 15 2) ∧
      BeatsMemberBundle.Calls.SegmentTreeBeats_chmin_callFuel firstFuel initial
        (Proofs.CppConstructorMultiFinish.reference caller 15 2) false
        [.value (.literal i32 qa),.value (.literal i32 qb),.value (.literal s64 x)] = .finished (middle,.unit) ∧
      BeatsMemberBundle.Calls.SegmentTreeBeats_calc_max_callFuel secondFuel middle
        (Proofs.CppConstructorMultiFinish.reference caller 15 2) false
        [.value (.literal i32 qa),.value (.literal i32 qb)] = .finished (result,.scalar value) ∧
      value = max (-INF) (rangeMaxOf 0 qa qb (rangeMin 0 qa qb x a)) ∧
      Scalars result caller.slots.length n ∧ ∃ bf,
        BVecs result (fun i => caller.slots.length+i) (fun i => caller.frame.bindings.length+i)
          (fun i => caller.frame.state.storage.objects.length+i) (fun _ => caller.scope)
          (fieldBuffer result (fun i => caller.frame.state.storage.objects.length+i)) (VVB bf) := by
  obtain ⟨constructorFuel,initial,b,heap,constructed,rep,fields,vectors⟩ :=
    Proofs.BeatsReceiverCalls.construct_arguments caller slot vb inputOwner inputScope wb maximum
      buf a ok items limit n positive range length values
  have sourceConstructed := (generated_constructor_call constructorFuel caller [.vectorReference slot]).trans constructed
  obtain ⟨firstFuel,middle,secondFuel,result,value,ran1,ran2,meaning,fields2,b2,vectors2⟩ :=
    generated_update_query initial caller.slots.length
      (fun i => caller.slots.length+i) (fun i => caller.frame.bindings.length+i)
      (fun i => caller.frame.state.storage.objects.length+i) (fun _ => caller.scope)
      (fieldBuffer initial (fun i => caller.frame.state.storage.objects.length+i))
      b n (8*n+8) 256 a (buildBT a 0 n) heap vectors fields rep range
      qa qb qaBound qbBound x valueBound (by decide) updateSafe querySafe
  have actualReference : Proofs.CppConstructorMultiFinish.reference caller 15 2 =
      sourceReceiver (fun i => caller.slots.length+i) caller.slots.length := rfl
  rw [← actualReference] at ran1 ran2
  exact ⟨constructorFuel,initial,firstFuel,middle,secondFuel,result,value,
    sourceConstructed,ran1,ran2,meaning,fields2,b2,vectors2⟩

end GeneratedBeatsMemberReceiverExamples
