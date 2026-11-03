import Proofs.VecCapture

namespace Proofs.UfInlineRoot
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecWrite
open Proofs.VecKitW Proofs.PowModStep Proofs.DoublingNested Proofs.PrefixSumsCall
open Proofs.UfRootCall Proofs.UfSameCall Proofs.UfFindCall Proofs.UfCompression Proofs.VecCapture
open Proofs.CppState (Cell)
open Proofs.VectorFillCall Proofs.QuotientSearch

abbrev capturedF : Command :=
  .sequence (.primitive (.declare i32 true (.variable i32 1))) (.sequence (loopCK 1)
    (.sequence loop2 (.sequence (.primitive (.declare i32 true (.variable i32 2))) Sk)))

theorem terminal_shape : Terminal i32 i32 (.variable i32 2) bodyF capturedF :=
  .seq _ _ _ (declare_silent i32 i32 true (.variable i32 1))
    (.seq _ _ _ (while_silent i32 (condK 1) (loopBodyK 1))
      (.seq _ _ _ (while_silent i32 cond2 loopBody2) .done))

def coreState (P : List Cell) (r : Int) : PS :=
  ⟨P++[⟨i32,r⟩,⟨i32,r⟩,⟨i32,r⟩],[⟨P.length,true⟩,⟨P.length+1,true⟩,⟨P.length+2,true⟩]⟩

theorem state_eq (P : List Cell) (a r : Int) :
    appended i32 r (setP (setP (appI (stI P a) a) (P.length+1) r) P.length r) = coreState P r := by
  simp [appended,setP,appI,stI,coreState,List.append_assoc,List.set_append_right]

theorem core_correct (P : List Cell) (ps : List Int) (rank : Nat → Nat)
    (forest : Forest ps rank) (length : ps.length < 2147483648) (a : Nat) (inside : a < ps.length)
    (fuel : Nat) (enough : rank a+2 ≤ fuel) :
    ∃ (out : PRW) (r : Nat), pexecW i32 fuel capturedF (stI P a) ps = some out ∧
      out.ret = none ∧ out.ps = coreState P r ∧ Compressed ps out.vec a r ∧ Forest out.vec rank ∧
      out.cost ≤ 90 * rank a+60 ∧ out.need ≤ P.length+62 ∧ out.wk ≤ rank a ∧
      (∀ tail next, pexecW i32 fuel tail out.ps out.vec = some next →
        pexecW i32 fuel (plug capturedF tail) (stI P a) ps = some (followed out next)) := by
  obtain ⟨old,r,run,ret,reach,rl,root,inv,cost,need,work,saved,state⟩ :=
    body_exec_find_state P ps rank forest length a inside fuel enough
  have valid := Proofs.VectorSumCall.i32_valid (r : Int) (by omega) (by omega)
  have convert := Proofs.VectorSumCall.conv_signed i32 rfl rfl (r : Int) valid
  obtain ⟨capturing,space⟩ := execution terminal_shape fuel (stI P a) ps old r run ret convert
  obtain ⟨sameLength,entries⟩ := inv2_final ps old.vec a r root inv
  have compressed : Compressed ps old.vec a r := ⟨sameLength,reach,root,entries⟩
  have newForest := find_forest ps old.vec rank forest a r reach rl root sameLength entries valid
  refine ⟨_,r,capturing,rfl,?_,compressed,newForest,cost,?_,work,?_⟩
  · change appended i32 (r : Int) old.ps = coreState P r
    rw [state,state_eq]
  · omega
  · intro tail next executed
    exact continuation terminal_shape fuel (stI P a) ps old r tail next run ret convert executed

theorem env_new (ps : PS) (ty : Ty) (v : Int) (valid : ty.valid v = true) :
    penv1 (appended ty v ps) (ps.bs.length+1) ty = some v := by
  simp [appended,penv1,penv,valid]

theorem env_old (ps : PS) (ty extraTy : Ty) (v x : Int) (slot : Nat)
    (value : penv1 ps slot ty = some v) : penv1 (appended extraTy x ps) slot ty = some v := by
  cases slot with
  | zero => simp [penv1] at value
  | succ k =>
    simp only [penv1,penv] at value ⊢
    cases binding : ps.bs[k]? with
    | none => simp [binding] at value
    | some b =>
      have blt : k < ps.bs.length := (List.getElem?_eq_some_iff.mp binding).1
      cases cell : ps.mem[b.address]? with
      | none => simp [binding,cell] at value
      | some c =>
        have mlt : b.address < ps.mem.length := (List.getElem?_eq_some_iff.mp cell).1
        simpa [appended,List.getElem?_append_left blt,List.getElem?_append_left mlt,binding,cell] using value

abbrev condition (nSlot aSlot : Nat) : NExpr := .logical true
  (.binary Proofs.PrefixSumsCall.bT .le (.literal i32 0) (.variable i32 aSlot))
  (.binary Proofs.PrefixSumsCall.bT .lt (.variable i32 aSlot) (.variable i32 nSlot))

theorem condition_value (ps : PS) (vec : List Int) (nSlot aSlot : Nat) (n a : Int)
    (nv : penv1 ps nSlot i32 = some n) (av : penv1 ps aSlot i32 = some a)
    (nonneg : 0 ≤ a) (less : a < n) : vdenL i32 vec (penv1 ps) (condition nSlot aSlot) = some 1 := by
  have low : (NExpr.binary Proofs.PrefixSumsCall.bT .le (.literal i32 0) (.variable i32 aSlot)).denote (penv1 ps) = some 1 := by
    simp only [NExpr.denote,show i32.valid 0 = true from rfl,ite_true,av,Option.bind_some]
    change Proofs.PrefixSumsCall.bT.convert (if 0 ≤ a then 1 else 0) = some 1
    rw [ite_eq_left nonneg]; rfl
  have high : (NExpr.binary Proofs.PrefixSumsCall.bT .lt (.variable i32 aSlot) (.variable i32 nSlot)).denote (penv1 ps) = some 1 := by
    simp only [NExpr.denote,av,nv,Option.bind_some]
    change Proofs.PrefixSumsCall.bT.convert (if a < n then 1 else 0) = some 1
    rw [ite_eq_left less]; rfl
  rw [vdenL_scalar _ _ _ _ rfl]
  change (NExpr.logical true _ _).denote _ = some 1
  rw [NExpr.denote,low]
  simp [high]

abbrev returning (k nSlot aSlot : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (.variable i32 nSlot)))
    (.sequence (.primitive (.declare i32 true (.variable i32 aSlot)))
      (.sequence (.primitive (.check (condition (k+1) (k+2)))) (VecShift.command (k+1) bodyF)))

abbrev inlined (k nSlot aSlot : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (.variable i32 nSlot)))
    (.sequence (.primitive (.declare i32 true (.variable i32 aSlot)))
      (.sequence (.primitive (.check (condition (k+1) (k+2)))) (VecShift.command (k+1) capturedF)))

theorem shifted_shape (n : Nat) : Terminal i32 i32 (VecShift.expr n (.variable i32 2))
    (VecShift.command n bodyF) (VecShift.command n capturedF) :=
  .seq _ _ _ (declare_silent i32 i32 true (VecShift.expr n (.variable i32 1)))
    (.seq _ _ _ (while_silent i32 (VecShift.expr n (condK 1)) (VecShift.command n (loopBodyK 1)))
      (.seq _ _ _ (while_silent i32 (VecShift.expr n cond2) (VecShift.command n loopBody2)) .done))

theorem inline_shape (k nSlot aSlot : Nat) : Terminal i32 i32 (VecShift.expr (k+1) (.variable i32 2))
    (returning k nSlot aSlot) (inlined k nSlot aSlot) :=
  .seq _ _ _ (declare_silent i32 i32 true (.variable i32 nSlot))
    (.seq _ _ _ (declare_silent i32 i32 true (.variable i32 aSlot))
      (.seq _ _ _ (check_silent i32 (condition (k+1) (k+2))) (shifted_shape (k+1))))

def inlineState (ps : PS) (n r : Int) : PS :=
  ⟨ps.mem++[⟨i32,n⟩,⟨i32,r⟩,⟨i32,r⟩,⟨i32,r⟩],
    ps.bs++[⟨ps.mem.length,true⟩,⟨ps.mem.length+1,true⟩,⟨ps.mem.length+2,true⟩,⟨ps.mem.length+3,true⟩]⟩

theorem returning_correct (state : PS) (vec : List Int) (rank : Nat → Nat)
    (forest : Forest vec rank) (length : vec.length < 2147483648) (nSlot aSlot : Nat) (a : Nat)
    (nv : penv1 state nSlot i32 = some (vec.length : Int)) (av : penv1 state aSlot i32 = some (a : Int))
    (inside : a < vec.length) (fuel : Nat) (enough : rank a+2 ≤ fuel) :
    ∃ (out : PRW) (r : Nat), pexecW i32 fuel (returning state.bs.length nSlot aSlot) state vec = some out ∧
      out.ret = some (r : Int) ∧ appended i32 (r : Int) out.ps = inlineState state vec.length r ∧
      Compressed vec out.vec a r ∧ Forest out.vec rank ∧
      out.cost ≤ 90 * rank a+72 ∧ out.need ≤ state.mem.length+state.bs.length+62 ∧ out.wk ≤ rank a := by
  let n := (vec.length : Int)
  let ns := appended i32 n state
  let args := appended i32 (a : Int) ns
  let P := state.mem++[(⟨i32,n⟩ : Cell)]
  let B : List CppState.Binding := state.bs++[⟨state.mem.length,true⟩]
  have nvalid := Proofs.VectorSumCall.i32_valid n (by dsimp [n]; omega) (by dsimp [n]; omega)
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
  have newN : penv1 args (state.bs.length+1) i32 = some n :=
    env_old ns i32 i32 n a (state.bs.length+1) (env_new state i32 n nvalid)
  have newA : penv1 args (state.bs.length+2) i32 = some (a : Int) := by
    simpa [args,ns,appended] using env_new ns i32 (a : Int) avalid
  have guard := condition_value args vec (state.bs.length+1) (state.bs.length+2) n a newN newA (by omega)
    (by dsimp [n]; omega)
  have check := pstmtW_check_ok i32 args vec (condition (state.bs.length+1) (state.bs.length+2)) 1 guard (by decide)
  have cp := (pexecW_prim i32 fuel (.check (condition (state.bs.length+1) (state.bs.length+2))) _ _).trans check
  obtain ⟨old,r,run,ret,reach,rl,root,inv,cost,need,work,saved,oldState⟩ :=
    body_exec_find_state P vec rank forest length a inside fuel enough
  have shifted := VecShift.execution i32 fuel bodyF (stI P a) vec B
  rw [run] at shifted
  simp only [Option.map_some] at shifted
  have argState : args = VecShift.pad B (stI P a) := by
    simp [args,ns,appended,VecShift.pad,stI,P,B,List.append_assoc]
  have blen : B.length = state.bs.length+1 := by simp [B]
  rw [← argState,blen] at shifted
  have guarded := seqW_some cp rfl shifted
  have aRun := seqW_some ap rfl guarded
  have nRun := seqW_some np rfl aRun
  obtain ⟨sameLength,entries⟩ := inv2_final vec old.vec a r root inv
  have compressed : Compressed vec old.vec a r := ⟨sameLength,reach,root,entries⟩
  have newForest := find_forest vec old.vec rank forest a r reach rl root sameLength entries
    (Proofs.VectorSumCall.i32_valid _ (by omega) (by omega))
  refine ⟨_,r,nRun,ret,?_,compressed,newForest,?_,?_,?_⟩
  · change appended i32 (r : Int) (VecShift.pad B old.ps) = inlineState state n r
    have commute : appended i32 (r : Int) (VecShift.pad B old.ps) = VecShift.pad B (appended i32 (r : Int) old.ps) := by
      simp [appended,VecShift.pad,List.append_assoc]
    rw [commute,oldState,state_eq]
    simp [VecShift.pad,coreState,inlineState,P,B,List.append_assoc]
  · have ng : vwp (.variable i32 nSlot) = (1,1) := rfl
    have ag : vwp (.variable i32 aSlot) = (1,1) := rfl
    have gg : vwp (condition (state.bs.length+1) (state.bs.length+2)) = (7,7) := rfl
    change (vwp (.variable i32 nSlot)).1+1+((vwp (.variable i32 aSlot)).1+1+
      ((vwp (condition (state.bs.length+1) (state.bs.length+2))).1+1+old.cost)) ≤ _
    rw [ng,ag,gg]; dsimp; omega
  · change max (state.mem.length+state.bs.length+(vwp (.variable i32 nSlot)).2+4)
      (max (ns.mem.length+ns.bs.length+(vwp (.variable i32 aSlot)).2+4)
        (max (args.mem.length+args.bs.length+(vwp (condition (state.bs.length+1) (state.bs.length+2))).2+2)
          (old.need+B.length))) ≤ _
    have ng : vwp (.variable i32 nSlot) = (1,1) := rfl
    have ag : vwp (.variable i32 aSlot) = (1,1) := rfl
    have gg : vwp (condition (state.bs.length+1) (state.bs.length+2)) = (7,7) := rfl
    simp only [P,List.length_append,List.length_cons,List.length_nil] at need
    simp [ns,args,appended,B,ng,ag,gg]; omega
  · simpa only [VecShift.result,Nat.zero_add] using work

theorem inlined_correct (state : PS) (vec : List Int) (rank : Nat → Nat)
    (forest : Forest vec rank) (length : vec.length < 2147483648) (nSlot aSlot : Nat) (a : Nat)
    (nv : penv1 state nSlot i32 = some (vec.length : Int)) (av : penv1 state aSlot i32 = some (a : Int))
    (inside : a < vec.length) (fuel : Nat) (enough : rank a+2 ≤ fuel) :
    ∃ (out : PRW) (r : Nat), pexecW i32 fuel (inlined state.bs.length nSlot aSlot) state vec = some out ∧
      out.ret = none ∧ out.ps = inlineState state vec.length r ∧ Compressed vec out.vec a r ∧ Forest out.vec rank ∧
      out.cost ≤ 90 * rank a+72 ∧ out.need ≤ state.mem.length+state.bs.length+64 ∧ out.wk ≤ rank a ∧
      (∀ tail next, pexecW i32 fuel tail out.ps out.vec = some next →
        pexecW i32 fuel (plug (inlined state.bs.length nSlot aSlot) tail) state vec = some (followed out next)) := by
  obtain ⟨old,r,run,ret,stateAfter,compressed,newForest,cost,need,work⟩ :=
    returning_correct state vec rank forest length nSlot aSlot a nv av inside fuel enough
  have insideRoot : r < vec.length := by
    obtain ⟨w,found,_⟩ := compressed.root
    exact (List.getElem?_eq_some_iff.mp found).1
  have valid := Proofs.VectorSumCall.i32_valid (r : Int) (by omega) (by omega)
  have convert := Proofs.VectorSumCall.conv_signed i32 rfl rfl (r : Int) valid
  have shape := inline_shape state.bs.length nSlot aSlot
  obtain ⟨executed,space⟩ := execution shape fuel state vec old r run ret convert
  exact ⟨_,r,executed,rfl,stateAfter,compressed,newForest,cost,by omega,work,
    fun tail next tailRun => continuation shape fuel state vec old r tail next run ret convert tailRun⟩

theorem inline_appended (state : PS) (n r : Int) : inlineState state n r =
    appended i32 r (appended i32 r (appended i32 r (appended i32 n state))) := by
  simp [inlineState,appended,List.append_assoc]

theorem inline_env_old (state : PS) (n r v : Int) (slot : Nat)
    (value : penv1 state slot i32 = some v) : penv1 (inlineState state n r) slot i32 = some v := by
  rw [inline_appended]
  exact env_old _ i32 i32 v r slot (env_old _ i32 i32 v r slot
    (env_old _ i32 i32 v r slot (env_old _ i32 i32 v n slot value)))

theorem inline_env_result (state : PS) (n r : Int) (valid : i32.valid r = true) :
    penv1 (inlineState state n r) (state.bs.length+4) i32 = some r := by
  rw [inline_appended]
  simpa [appended] using env_new (appended i32 r (appended i32 r (appended i32 n state))) i32 r valid

end Proofs.UfInlineRoot
