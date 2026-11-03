import Proofs.NestedReadOnly
import Proofs.FillWriteStmt

/-! `g[i][j] = x;` on a writable nested root `g` (scalar-only index and value expressions). -/

namespace Proofs.NestedWrite
open Proofs.CppScalar Proofs.CppMixedInvoke Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedSim Proofs.CppNestedEval
open Proofs.CppVector Proofs.CppNestedFacts Proofs.CppNestedConstruct Proofs.CppNestedRows Proofs.CppNestedStmt
open Proofs.NestedReadOnly Proofs.FlatVectorStmt Proofs.FillWriteStmt Proofs.DoublingPrologue

theorem write_row_stmt (s : NState) (slot rb : Nat) (idx iE vE : NExpr) (k j R w sc : Nat) (ty : Ty) (x : Int)
    (prev : Buffer Value)
    (idxScalar : idx.scalarOnly = true) (idxValue : idx.denote (envOf s) = some (k : Int))
    (iScalar : iE.scalarOnly = true) (iValue : iE.denote (envOf s) = some (j : Int))
    (vScalar : vE.scalarOnly = true) (vValue : vE.denote (envOf s) = some x)
    (hslot : s.vectorSlot slot = some rb)
    (binding : s.frame.bindings[rb]? = some ⟨R,.vector (.integer ty),true,.root sc⟩)
    (g : RootGraph s.frame.state R ty w sc)
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (flag : s.frame.rootWritable[R]? = some true) (inside : k < w)
    (found : s.frame.state.storage.lookup (R+1+k) = some prev)
    (accepted : ty.valid x = true) (hj : j < prev.items.length) :
    ∃ t, (NStmt.write (.row (.local slot) (.integer ty) idx) ty iE vE).run s = some ⟨t,none,false⟩ ∧
      t.frame = s.frame.updated (R+1+k) prev ⟨{prev with items := prev.items.set j (Value.integer x)},(),1,prev.capacity+2⟩ ∧
      t.slots = s.slots ∧ t.scope = s.scope ∧ t.scalars.memory = s.scalars.memory ∧
      t.scalars.bindings = s.scalars.bindings ∧ t.scalars.baseMemory = s.scalars.baseMemory ∧
      s.scalars.work ≤ t.scalars.work ∧ t.scalars.work ≤ s.scalars.work+vE.nodes+idx.nodes+iE.nodes+6 ∧
      s.scalars.peak ≤ t.scalars.peak ∧
      t.scalars.peak ≤ max s.scalars.peak (liveS s+idx.nodes+iE.nodes+vE.nodes+10) ∧
      s.peak ≤ t.peak ∧ t.peak ≤ max s.peak (t.scalars.peak+t.frame.state.storage.peak) := by
  have nodes := container_nodes slot ty idx
  obtain ⟨t1,hexp,good1⟩ := scalar_eval vE (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+iE.nodes+vE.nodes+3))
    x vScalar (by rw [envOf_core (core_charge _ _ _)]; exact vValue)
  have core1 : Core s t1 := (core_charge s 0 _).trans good1.1
  have frame1 : t1.frame = s.frame := core1.1
  have env1 : envOf t1 = envOf s := envOf_core core1
  obtain ⟨t2,hrow,goodr,bindr⟩ := eval_row_g t1 slot rb idx k R w sc ty true true idxScalar (by rw [env1]; exact idxValue)
    (by simpa [NState.vectorSlot, core1.2.1] using hslot) (by rw [frame1]; exact binding) (by rw [frame1]; exact g)
    (by rw [frame1]; exact lengths) (by rw [frame1]; exact flag) (fun _ => rfl) inside
  have env2 : envOf t2 = envOf s := (envOf_goodF goodr).trans env1
  obtain ⟨t3,hidx,good3⟩ := scalar_eval iE t2 j iScalar (by rw [env2]; exact iValue)
  have frame3 : t3.frame = t2.frame := good3.1.1
  have stateEq : t3.frame.state = s.frame.state := by rw [frame3, goodr.1, frame1]
  have rwEq : t3.frame.rootWritable = s.frame.rootWritable := by rw [frame3, goodr.2.1, frame1]
  have bindEq : t3.frame.bindings = s.frame.bindings ++ [rowBindingW R ty k true] := by
    rw [frame3, bindr, frame1]
  have g3 : RootGraph t3.frame.state R ty w sc := by rw [stateEq]; exact g
  have lengths3 : t3.frame.rootWritable.length = t3.frame.state.forest.objects.length := by
    rw [rwEq, stateEq]; exact lengths
  have flag3 : t3.frame.rootWritable[R]? = some true := by rw [rwEq]; exact flag
  have hb : t3.frame.bindings[s.frame.bindings.length]? = some (rowBindingW R ty k true) := by simp [bindEq]
  obtain ⟨buffer,resolved,foundBuffer⟩ := resolve_row_g t3.frame s.frame.bindings.length R ty w sc k g3 true true hb
    lengths3 flag3 (fun _ => rfl) inside
  have sameBuffer : buffer = prev := by
    rw [stateEq, found] at foundBuffer
    exact (Option.some.inj foundBuffer).symm
  subst sameBuffer
  obtain ⟨objectBuffer,object,foundAgain⟩ := row_object t3.frame R ty w sc k g3 inside
  have sameObject : objectBuffer = buffer := by
    rw [foundBuffer] at foundAgain
    exact (Option.some.inj foundAgain).symm
  subst sameObject
  obtain ⟨ref,hrefs,hwrite⟩ := write_ok t3.frame s.frame.bindings.length ty j x (rowBindingW R ty k true) objectBuffer
    ⟨.integer ty,some R,none,[]⟩ true hb rfl resolved object (maximum_row_g t3.frame R ty w sc k g3 lengths3 true flag3 inside)
    rfl rfl accepted hj
  have hwrite' : t3.frame.write ref x = some (t3.frame.updated (R+1+k) objectBuffer
      ⟨{objectBuffer with items := objectBuffer.items.set j (Value.integer x)},(),1,objectBuffer.capacity+2⟩) := by
    simpa [rowBindingW] using hwrite
  have gAll := (GoodF.charge s 0 ((Container.row (.local slot) (.integer ty) idx).nodes+iE.nodes+vE.nodes+3)).trans
    (good1.toF.trans (goodr.trans good3.toF))
  obtain ⟨_,_,sl,sc',m,b,k',gl,gu,gpl,gpu,gql,gqu⟩ := gAll
  have live : liveS t3 = liveS s := liveS_of_memory m b k'
  have hrunEval : (Container.row (.local slot) (.integer ty) idx).eval t1 = some (t2, s.frame.bindings.length) := by
    have := hrow
    rw [frame1] at this
    exact this
  have frameEq : ((withFrame t3 (t3.frame.updated (R+1+k) objectBuffer
      ⟨{objectBuffer with items := objectBuffer.items.set j (Value.integer x)},(),1,objectBuffer.capacity+2⟩)).release s).frame =
      s.frame.updated (R+1+k) objectBuffer
        ⟨{objectBuffer with items := objectBuffer.items.set j (Value.integer x)},(),1,objectBuffer.capacity+2⟩ := by
    apply Proofs.DoublingPrologue.Frame.eq_of
    · simp [NState.release, Frame.updated, stateEq]
    · simp [NState.release, Frame.updated, rwEq]
    · simp [NState.release, Frame.updated, bindEq]
  refine ⟨((withFrame t3 (t3.frame.updated (R+1+k) objectBuffer
      ⟨{objectBuffer with items := objectBuffer.items.set j (Value.integer x)},(),1,objectBuffer.capacity+2⟩)).release s).charge 1 0,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [NStmt.run, hexp, hrunEval, hidx, hrefs, hwrite', withFrame]
  · simpa using frameEq
  · simpa using sl
  · simpa using sc'
  · simpa using m
  · simpa using b
  · simpa using k'
  · simp [charge_work]; omega
  · simp [charge_work]; simp [Container.nodes] at gu; omega
  · simp [charge_scalar_peak, liveS]; omega
  · simp [charge_scalar_peak, m, b, k']
    simp [Container.nodes] at gpu
    unfold liveS at gpu live ⊢
    omega
  · exact (peak_after t3 (withFrame t3 (t3.frame.updated (R+1+k) objectBuffer ⟨{objectBuffer with items := objectBuffer.items.set j (Value.integer x)},(),1,objectBuffer.capacity+2⟩)) s 1 0 rfl rfl (by simp [Frame.updated, stateEq] <;> omega) gql
      (by rw [stateEq] at gqu ⊢; exact gqu)).1
  · exact (peak_after t3 (withFrame t3 (t3.frame.updated (R+1+k) objectBuffer ⟨{objectBuffer with items := objectBuffer.items.set j (Value.integer x)},(),1,objectBuffer.capacity+2⟩)) s 1 0 rfl rfl (by simp [Frame.updated, stateEq] <;> omega) gql
      (by rw [stateEq] at gqu ⊢; exact gqu)).2

end Proofs.NestedWrite
