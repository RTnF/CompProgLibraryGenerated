import Proofs.UfReadCursor
import Proofs.UfInlineRoot

namespace Proofs.UfReadInline
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecWrite
open Proofs.VecKitW Proofs.DoublingNested Proofs.UfRootCall Proofs.UfReadCursor
open Proofs.VecCapture Proofs.UfInlineRoot Proofs.VectorFillCall
open Proofs.CppState (Cell Binding)
open Proofs.PowModStep

-- Only the length is used in the command; these are never runtime bindings.
abbrev shape (k : Nat) : List Binding := List.replicate (k+1) ⟨0,false⟩
abbrev returning (k nSlot aSlot : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (.variable i32 nSlot)))
    (.sequence (.primitive (.declare i32 true (.variable i32 aSlot))) (body (shape k)))
abbrev inlined (k nSlot aSlot : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (.variable i32 nSlot)))
    (.sequence (.primitive (.declare i32 true (.variable i32 aSlot)))
      (.sequence (loop (shape k))
        (.sequence (.primitive (.declare i32 true (.variable i32 (k+2)))) Sk)))

theorem terminal_shape (k nSlot aSlot : Nat) : Terminal i32 i32 (.variable i32 (k+2))
    (returning k nSlot aSlot) (inlined k nSlot aSlot) := by
  simp only [returning,inlined,body,shape,List.length_replicate]
  exact .seq _ _ _ (declare_silent i32 i32 true (.variable i32 nSlot))
    (.seq _ _ _ (declare_silent i32 i32 true (.variable i32 aSlot))
      (.seq _ _ _ (while_silent i32 (UfReadCursor.condition (shape k)) (iteration (shape k))) .done))

def inlineState (state : PS) (n r : Int) : PS :=
  ⟨state.mem++[⟨i32,n⟩,⟨i32,r⟩,⟨i32,r⟩],
    state.bs++[⟨state.mem.length,true⟩,⟨state.mem.length+1,true⟩,⟨state.mem.length+2,true⟩]⟩

theorem returning_correct (state : PS) (vec : List Int) (rank : Nat → Nat)
    (forest : Forest vec rank) (length : vec.length < 2147483648) (nSlot aSlot : Nat)
    (n : Int) (nvalid : i32.valid n = true) (a : Nat)
    (nv : penv1 state nSlot i32 = some n) (av : penv1 state aSlot i32 = some (a : Int))
    (inside : a < vec.length) (fuel : Nat) (enough : rank a+2 ≤ fuel) :
    ∃ (out : PRW) (r : Nat), pexecW i32 fuel (returning state.bs.length nSlot aSlot) state vec = some out ∧
      out.ret = some (r : Int) ∧ appended i32 (r : Int) out.ps = inlineState state n r ∧
      Reach vec a r ∧ r < vec.length ∧ (∃ w, vec[r]? = some w ∧ w < 0) ∧ out.vec = vec ∧
      out.cost ≤ 16 * rank a+22 ∧ out.need ≤ state.mem.length+state.bs.length+24 ∧ out.wk = 0 := by
  let ns := appended i32 n state
  let args := appended i32 (a : Int) ns
  let P := state.mem++[(⟨i32,n⟩ : Cell)]
  let B : List Binding := state.bs++[⟨state.mem.length,true⟩]
  have avalid := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by omega)
  have nvalue : vdenL i32 vec (penv1 state) (.variable i32 nSlot) = some n := by
    rw [vdenL_scalar _ _ _ _ rfl]; exact nv
  have avalue : vdenL i32 vec (penv1 ns) (.variable i32 aSlot) = some (a : Int) := by
    rw [vdenL_scalar _ _ _ _ rfl]
    exact env_old state i32 i32 a n aSlot av
  have nd := pstmtW_declare_ok i32 state vec i32 true (.variable i32 nSlot) n nvalue n
    (Proofs.VectorSumCall.conv_signed i32 rfl rfl _ nvalid)
  have ad := pstmtW_declare_ok i32 ns vec i32 true (.variable i32 aSlot) a avalue a
    (Proofs.VectorSumCall.conv_signed i32 rfl rfl _ avalid)
  have np := (pexecW_prim i32 fuel (.declare i32 true (.variable i32 nSlot)) _ _).trans nd
  have ap := (pexecW_prim i32 fuel (.declare i32 true (.variable i32 aSlot)) _ _).trans ad
  obtain ⟨old,r,run,ret,oldState,unchanged,reach,rl,root,cost,need,work⟩ :=
    body_run P B vec rank forest length a inside fuel enough
  have argState : args = cursor P B a := by
    simp [args,ns,appended,cursor,P,B,List.append_assoc]
  have bodyEq : body B = body (shape state.bs.length) := by
    simp only [body,loop,UfReadCursor.condition,readCursor,iteration,assignCursor,B,shape,
      List.length_append,List.length_cons,List.length_nil,List.length_replicate]
  rw [←argState,bodyEq] at run
  have aRun := seqW_some ap rfl run
  have nRun := seqW_some np rfl aRun
  refine ⟨_,r,nRun,ret,?_,reach,rl,root,unchanged,?_,?_,?_⟩
  · change appended i32 (r : Int) old.ps = inlineState state n r
    rw [oldState]
    simp [appended,cursor,inlineState,P,B,List.append_assoc]
  · have ng : vwp (.variable i32 nSlot) = (1,1) := rfl
    have ag : vwp (.variable i32 aSlot) = (1,1) := rfl
    change (vwp (.variable i32 nSlot)).1+1+((vwp (.variable i32 aSlot)).1+1+old.cost) ≤ _
    rw [ng,ag]; dsimp; omega
  · change max (state.mem.length+state.bs.length+(vwp (.variable i32 nSlot)).2+4)
      (max (ns.mem.length+ns.bs.length+(vwp (.variable i32 aSlot)).2+4) old.need) ≤ _
    have ng : vwp (.variable i32 nSlot) = (1,1) := rfl
    have ag : vwp (.variable i32 aSlot) = (1,1) := rfl
    simp only [P,B,List.length_append,List.length_cons,List.length_nil] at need
    simp [ns,appended,ng,ag]; omega
  · simpa only [Nat.zero_add] using work

theorem inlined_correct (state : PS) (vec : List Int) (rank : Nat → Nat)
    (forest : Forest vec rank) (length : vec.length < 2147483648) (nSlot aSlot : Nat)
    (n : Int) (nvalid : i32.valid n = true) (a : Nat)
    (nv : penv1 state nSlot i32 = some n) (av : penv1 state aSlot i32 = some (a : Int))
    (inside : a < vec.length) (fuel : Nat) (enough : rank a+2 ≤ fuel) :
    ∃ (out : PRW) (r : Nat), pexecW i32 fuel (inlined state.bs.length nSlot aSlot) state vec = some out ∧
      out.ret = none ∧ out.ps = inlineState state n r ∧ Reach vec a r ∧ r < vec.length ∧
      (∃ w, vec[r]? = some w ∧ w < 0) ∧ out.vec = vec ∧
      out.cost ≤ 16 * rank a+22 ∧ out.need ≤ state.mem.length+state.bs.length+26 ∧ out.wk = 0 ∧
      (∀ tail next, pexecW i32 fuel tail out.ps out.vec = some next →
        pexecW i32 fuel (plug (inlined state.bs.length nSlot aSlot) tail) state vec = some (followed out next)) := by
  obtain ⟨old,r,run,ret,afterState,reach,rl,root,unchanged,cost,need,work⟩ :=
    returning_correct state vec rank forest length nSlot aSlot n nvalid a nv av inside fuel enough
  have valid := Proofs.VectorSumCall.i32_valid (r : Int) (by omega) (by omega)
  have convert := Proofs.VectorSumCall.conv_signed i32 rfl rfl (r : Int) valid
  have shape := terminal_shape state.bs.length nSlot aSlot
  obtain ⟨executed,space⟩ := execution shape fuel state vec old r run ret convert
  exact ⟨_,r,executed,rfl,afterState,reach,rl,root,unchanged,cost,by omega,work,
    fun tail next tailRun => continuation shape fuel state vec old r tail next run ret convert tailRun⟩

theorem inline_appended (state : PS) (n r : Int) : inlineState state n r =
    appended i32 r (appended i32 r (appended i32 n state)) := by
  simp [inlineState,appended,List.append_assoc]

theorem inline_env_old (state : PS) (n r v : Int) (slot : Nat)
    (value : penv1 state slot i32 = some v) : penv1 (inlineState state n r) slot i32 = some v := by
  rw [inline_appended]
  exact env_old _ i32 i32 v r slot (env_old _ i32 i32 v r slot (env_old _ i32 i32 v n slot value))

theorem inline_env_result (state : PS) (n r : Int) (valid : i32.valid r = true) :
    penv1 (inlineState state n r) (state.bs.length+3) i32 = some r := by
  rw [inline_appended]
  simpa [appended] using env_new (appended i32 r (appended i32 n state)) i32 r valid

end Proofs.UfReadInline
