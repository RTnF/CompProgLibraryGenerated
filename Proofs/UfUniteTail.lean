import Proofs.UfMergeInvariant

namespace Proofs.UfUniteTail
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.StraightLine Proofs.Mod61Body Proofs.VecExpr Proofs.VecStraight Proofs.VecCall Proofs.VecKit
open Proofs.CppNestedFacts Proofs.IntSim Proofs.ScalarCall Proofs.VecWrite Proofs.VecWriteCall Proofs.VecKitW
open Proofs.QuotientSearch Proofs.VectorFillCall Proofs.PrefixSumsCall Proofs.UfRootCall Proofs.UfSameCall
open Proofs.VectorSumCall (conv_signed i32_valid)
open Proofs.CppState (Cell)
open Proofs.PowModStep (Sk)
open Proofs.UfFindCall (reach_det reach_trans reach_rank root_reach)


abbrev swapBlock : Command :=
  .sequence (.scope (.sequence (.primitive (.declare i32 true (.variable i32 9)))
    (.sequence (.primitive (.assign 9 i32 (.variable i32 14)))
      (.sequence (.primitive (.assign 14 i32 (.variable i32 15))) Sk)))) Sk

theorem scope_swap_restore (ps0 : PS) (adX adY : Nat) (x y : Int)
    (insideX : adX < ps0.mem.length) (insideY : adY < ps0.mem.length) :
    (⟨(setP (setP (appI ps0 x) adX y) adY x).mem.take ps0.mem.length,
      (setP (setP (appI ps0 x) adX y) adY x).bs.take ps0.bs.length⟩ : PS) = setP (setP ps0 adX y) adY x := by
  obtain ⟨mem,bs⟩ := ps0
  simp only [setP, appI] at *
  simp only [PS.mk.injEq]
  constructor
  · apply List.ext_getElem?
    intro i
    simp only [List.getElem?_take, List.getElem?_set, List.length_set, List.length_append, List.getElem?_append]
    by_cases h1 : adX = i <;> by_cases h2 : adY = i <;> by_cases h3 : i < mem.length <;> simp_all <;> omega
  · simp [List.take_append_of_le_length]

theorem swap_exec (ps0 : PS) (vec : List Int) (adX adY x y : Nat) (lx : Loc ps0 8 adX x) (ly : Loc ps0 13 adY y)
    (hne : adX ≠ adY) (hbs : ps0.bs.length = 14) (hx : i32.valid (x : Int) = true) (hy : i32.valid (y : Int) = true)
    (fu : Nat) :
    ∃ r, pexecW i32 fu swapBlock ps0 vec = some r ∧ r.ps = setP (setP ps0 adX (y : Int)) adY (x : Int) ∧
      r.vec = vec ∧ r.ret = none ∧ r.cost ≤ 20 ∧ r.need ≤ ps0.mem.length + ps0.bs.length + 20 ∧ r.wk = 0 := by
  have insideX : adX < ps0.mem.length := (List.getElem?_eq_some_iff.mp lx.2).1
  have d := decl_step ps0 vec 8 adX (x : Int) lx hx
  have d' := (pexecW_prim i32 fu (.declare i32 true (.variable i32 9)) _ _).trans d
  have temp : Loc (appI ps0 (x : Int)) 14 ps0.mem.length x := by
    have := loc_app_new ps0 (x : Int)
    rw [hbs] at this
    exact this
  have oldY := loc_app_old ps0 13 adY (y : Int) (x : Int) ly
  have oldX := loc_app_old ps0 8 adX (x : Int) (x : Int) lx
  obtain ⟨hb4, hm4⟩ := oldX
  have s1 := pstmtW_assign_ok i32 (appI ps0 (x : Int)) vec 8 i32 (.variable i32 14) (y : Int)
    (by rw [vdenL_scalar _ _ _ _ rfl, den_variable]; exact env_loc _ 13 adY y oldY hy) ⟨adX,true⟩ ⟨i32,(x : Int)⟩ hb4 hm4
    rfl hx rfl (y : Int) (conv_signed i32 rfl rfl _ hy)
  have a1 := (pexecW_prim i32 fu (.assign 9 i32 (.variable i32 14)) _ _).trans s1
  have temp' : Loc (setP (appI ps0 (x : Int)) adX (y : Int)) 14 ps0.mem.length x :=
    loc_set_other _ _ _ _ _ _ temp (by omega)
  have oldY' : Loc (setP (appI ps0 (x : Int)) adX (y : Int)) 13 adY y := loc_set_other _ _ _ _ _ _ oldY hne
  obtain ⟨hb7, hm7⟩ := oldY'
  have s2 := pstmtW_assign_ok i32 (setP (appI ps0 (x : Int)) adX (y : Int)) vec 13 i32 (.variable i32 15) (x : Int)
    (by rw [vdenL_scalar _ _ _ _ rfl, den_variable]; exact env_loc _ 14 _ x temp' hx) ⟨adY,true⟩ ⟨i32,(y : Int)⟩ hb7 hm7
    rfl hy rfl (x : Int) (conv_signed i32 rfl rfl _ hx)
  have a2 := (pexecW_prim i32 fu (.assign 14 i32 (.variable i32 15)) _ _).trans s2
  have c3 := seqW_some a2 rfl (pexecW_skip i32 fu (setP (setP (appI ps0 (x : Int)) adX (y : Int)) adY (x : Int)) vec)
  have c2 := seqW_some a1 rfl c3
  have c1 := seqW_some d' rfl c2
  have sc := pexecW_scope i32 fu _ _ _ _ c1
  have insideY : adY < ps0.mem.length := (List.getElem?_eq_some_iff.mp ly.2).1
  have tk := scope_swap_restore ps0 adX adY (x : Int) (y : Int) insideX insideY
  simp only [tk] at sc
  have c4 := seqW_some sc rfl (pexecW_skip i32 fu (setP (setP ps0 adX (y : Int)) adY (x : Int)) vec)
  refine ⟨_, c4, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes]
  · simp [vwp, NExpr.nodes, hbs]
  · simp



abbrev W1 : Command := .primitive (.write (.local 0) i32 (.cast u64 (.variable i32 9))
  (.binary i32 .add (rdK 8) (rdK 13)))
abbrev W2 : Command := .primitive (.write (.local 0) i32 (.cast u64 (.variable i32 14)) (.variable i32 9))
abbrev decrement : NExpr := .binary i32 .sub (.variable i32 1) (.literal i32 1)
abbrev C1 : Command := .primitive (.assign 1 i32 decrement)
abbrev retX : Command := .sequence (.primitive (.ret (.variable i32 9))) Sk
abbrev writes : Command := .sequence W1 (.sequence W2 (.sequence C1 retX))

theorem writes_exec (state : PS) (vec : List Int) (adX adY adC X Y : Nat) (vx vy groups : Int)
    (lx : Loc state 8 adX X) (ly : Loc state 13 adY Y) (lc : Loc state 0 adC groups)
    (separate : adC ≠ adX) (length : vec.length < 2147483648) (ix : X < vec.length) (iy : Y < vec.length)
    (fx : vec[X]? = some vx) (fy : vec[Y]? = some vy) (xvalid : i32.valid vx = true) (yvalid : i32.valid vy = true)
    (countValid : i32.valid groups = true) (sumValid : i32.valid (vx+vy) = true)
    (decrementValid : i32.valid (groups-1) = true) (fuel : Nat) :
    ∃ out, pexecW i32 fuel writes state vec = some out ∧ out.ret = some (X : Int) ∧
      out.vec = Proofs.UfMergeInvariant.linked vec X Y (vx+vy) ∧ out.ps = setP state adC (groups-1) ∧
      out.wk = 2 ∧ out.cost ≤ 120 ∧ out.need ≤ state.mem.length+state.bs.length+50 := by
  have rootValid := i32_valid (X : Int) (by omega) (by omega)
  have iX : vdenL i32 vec (penv1 state) (.cast u64 (.variable i32 9)) = some (X : Int) := by
    rw [vdenL_scalar _ _ _ _ rfl]
    exact idxK state 8 adX X lx (by omega)
  have sum : vdenL i32 vec (penv1 state) (.binary i32 .add (rdK 8) (rdK 13)) = some (vx+vy) := by
    rw [vdenL_binary _ _ _ _ _ _ _ rfl,rdK_val vec state 8 adX X lx length ix vx fx xvalid,
      rdK_val vec state 13 adY Y ly length iy vy fy yvalid,Option.bind_some,Option.bind_some]
    exact conv_signed i32 rfl rfl _ sumValid
  have w1 := pstmtW_write_ok i32 state vec (.cast u64 (.variable i32 9))
    (.binary i32 .add (rdK 8) (rdK 13)) (vx+vy) X sum iX ix sumValid
  have iY : vdenL i32 (vec.set X (vx+vy)) (penv1 state) (.cast u64 (.variable i32 14)) = some (Y : Int) := by
    rw [vdenL_scalar _ _ _ _ rfl]
    exact idxK state 13 adY Y ly (by omega)
  have xValue : vdenL i32 (vec.set X (vx+vy)) (penv1 state) (.variable i32 9) = some (X : Int) := by
    rw [vdenL_scalar _ _ _ _ rfl,den_variable]
    exact env_loc state 8 adX X lx rootValid
  have w2 := pstmtW_write_ok i32 state (vec.set X (vx+vy)) (.cast u64 (.variable i32 14))
    (.variable i32 9) (X : Int) Y xValue iY (by simpa using iy) rootValid
  let nextVec := (vec.set X (vx+vy)).set Y (X : Int)
  have countValue : vdenL i32 nextVec (penv1 state) decrement = some (groups-1) := by
    rw [vdenL_scalar _ _ _ _ rfl]
    simp only [decrement,NExpr.denote,env_loc state 0 adC groups lc countValid,
      show i32.valid 1 = true from rfl,ite_true,Option.bind_some]
    exact conv_signed i32 rfl rfl _ decrementValid
  have c1 := pstmtW_assign_ok i32 state nextVec 0 i32 decrement (groups-1) countValue
    ⟨adC,true⟩ ⟨i32,groups⟩ lc.1 lc.2 rfl countValid rfl (groups-1)
    (conv_signed i32 rfl rfl _ decrementValid)
  have afterX : Loc (setP state adC (groups-1)) 8 adX X := loc_set_other _ _ _ _ _ _ lx separate
  have returned := pstmtW_ret_ok i32 (setP state adC (groups-1)) nextVec (.variable i32 9) (X : Int)
    (by rw [vdenL_scalar _ _ _ _ rfl,den_variable]; exact env_loc _ 8 adX X afterX rootValid)
  have last := seqW_ret (b := Sk) ((pexecW_prim i32 fuel _ _ _).trans returned) rfl
  have third := seqW_some ((pexecW_prim i32 fuel _ _ _).trans c1) rfl last
  have second := seqW_some ((pexecW_prim i32 fuel _ _ _).trans w2) rfl third
  have first := seqW_some ((pexecW_prim i32 fuel _ _ _).trans w1) rfl second
  refine ⟨_,first,rfl,rfl,rfl,rfl,?_,?_⟩
  · simp [vwp,NExpr.nodes,Container.nodes,rdK]
  · simp [vwp,NExpr.nodes,Container.nodes,rdK,setP]

abbrev eqE : NExpr := .binary bT .eq (.variable i32 9) (.variable i32 14)
abbrev negX : NExpr := .unary i32 .neg (rdK 8)
abbrev negY : NExpr := .unary i32 .neg (rdK 13)
abbrev comparison : NExpr := .binary bT .lt negX negY
abbrev B1 : Command := .branch eqE (.sequence (.scope retX) Sk) Sk
abbrev B2 : Command := .branch comparison swapBlock Sk
abbrev tail : Command := .sequence B1 (.sequence B2 writes)
abbrev before_tail (next : Command) : Command :=
  .sequence (.primitive (.check (UfInlineRoot.condition 2 3)))
    (.sequence (.primitive (.check (UfInlineRoot.condition 2 4)))
      (VecCapture.plug (UfInlineRoot.inlined 4 2 3)
        (.sequence (.primitive (.declare i32 true (.variable i32 8)))
          (VecCapture.plug (UfInlineRoot.inlined 9 2 4)
            (.sequence (.primitive (.declare i32 true (.variable i32 13))) next)))))

theorem body_eq : Proofs.UnionFindCandidateInstance.UnionFind_unite.body = before_tail tail := rfl

theorem eq_value (state : PS) (vec : List Int) (adX adY X Y : Nat)
    (lx : Loc state 8 adX X) (ly : Loc state 13 adY Y)
    (xv : i32.valid (X : Int) = true) (yv : i32.valid (Y : Int) = true) :
    vdenL i32 vec (penv1 state) eqE = some (if X=Y then 1 else 0) := by
  rw [vdenL_scalar _ _ _ _ rfl,den_binary,den_variable,den_variable,
    env_loc state 8 adX X lx xv,env_loc state 13 adY Y ly yv]
  simp only [Option.bind_some]
  by_cases same : X=Y <;> simp [binaryValue,same,bT,Ty.convert]

theorem neg_value (state : PS) (vec : List Int) (j ad r : Nat) (v : Int)
    (loc : Loc state j ad r) (length : vec.length < 2147483648) (inside : r < vec.length)
    (found : vec[r]? = some v) (valid : i32.valid v = true) (negativeValid : i32.valid (-v) = true) :
    vdenL i32 vec (penv1 state) (.unary i32 .neg (rdK j)) = some (-v) := by
  change (vdenL i32 vec (penv1 state) (rdK j)).bind (fun x => i32.convert (unaryValue .neg x)) = some (-v)
  rw [rdK_val vec state j ad r loc length inside v found valid,Option.bind_some]
  exact conv_signed i32 rfl rfl _ negativeValid

theorem comparison_value (state : PS) (vec : List Int) (adX adY X Y : Nat) (vx vy : Int)
    (lx : Loc state 8 adX X) (ly : Loc state 13 adY Y) (length : vec.length < 2147483648)
    (ix : X < vec.length) (iy : Y < vec.length) (fx : vec[X]? = some vx) (fy : vec[Y]? = some vy)
    (xv : i32.valid vx = true) (yv : i32.valid vy = true)
    (nxv : i32.valid (-vx) = true) (nyv : i32.valid (-vy) = true) :
    vdenL i32 vec (penv1 state) comparison = some (if -vx < -vy then 1 else 0) := by
  rw [vdenL_binary _ _ _ _ _ _ _ rfl,neg_value state vec 8 adX X vx lx length ix fx xv nxv,
    neg_value state vec 13 adY Y vy ly length iy fy yv nyv,Option.bind_some,Option.bind_some]
  by_cases less : -vx < -vy <;> simp [binaryValue,less,bT,Ty.convert]

theorem same_exec (state : PS) (vec : List Int) (adX adY X : Nat)
    (lx : Loc state 8 adX X) (ly : Loc state 13 adY X) (valid : i32.valid (X : Int) = true) (fuel : Nat) :
    ∃ out, pexecW i32 fuel tail state vec = some out ∧ out.ps = state ∧ out.vec = vec ∧
      out.ret = some (X : Int) ∧ out.cost ≤ 40 ∧ out.need ≤ state.mem.length+state.bs.length+40 ∧ out.wk = 0 := by
  have equal := eq_value state vec adX adY X X lx ly valid valid
  rw [if_pos rfl] at equal
  have value : vdenL i32 vec (penv1 state) (.variable i32 9) = some (X : Int) := by
    rw [vdenL_scalar _ _ _ _ rfl,den_variable]
    exact env_loc state 8 adX X lx valid
  have returned := seqW_ret (b := Sk) ((pexecW_prim i32 fuel _ _ _).trans
    (pstmtW_ret_ok i32 state vec (.variable i32 9) X value)) rfl
  have scopedReturn := pexecW_scope i32 fuel _ _ _ _ returned
  have branchBody := seqW_ret (b := Sk) scopedReturn rfl
  have branch := Proofs.UfUniteCall.pexecW_branch_true i32 fuel eqE (.sequence (.scope retX) Sk) Sk state vec
    1 equal (by decide) _ branchBody
  have all := seqW_ret (b := .sequence B2 writes) branch rfl
  refine ⟨_,all,?_,rfl,rfl,?_,?_,rfl⟩
  · simp
  · simp [vwp,NExpr.nodes]
  · simp [vwp,NExpr.nodes]

def orderedState (state : PS) (adX adY X Y : Nat) (vx vy : Int) : PS :=
  if -vx < -vy then setP (setP state adX (Y : Int)) adY (X : Int) else state

theorem different_exec (state : PS) (vec : List Int) (groups : Int) (rank : Nat → Nat)
    (valid : Proofs.UfClassInvariant.Valid vec groups rank) (adX adY adC X Y : Nat) (vx vy : Int)
    (lx : Loc state 8 adX X) (ly : Loc state 13 adY Y) (lc : Loc state 0 adC groups)
    (separate : adX ≠ adY) (cx : adC ≠ adX) (cy : adC ≠ adY) (bindings : state.bs.length = 14)
    (fx : vec[X]? = some vx) (fy : vec[Y]? = some vy) (nx : vx < 0) (ny : vy < 0)
    (different : X ≠ Y) (fuel : Nat) :
    ∃ out, pexecW i32 fuel tail state vec = some out ∧
      out.ret = some ((if -vx < -vy then Y else X : Nat) : Int) ∧
      out.vec = Proofs.UfMergeInvariant.linked vec (if -vx < -vy then Y else X)
        (if -vx < -vy then X else Y) (vx+vy) ∧
      out.ps = setP (orderedState state adX adY X Y vx vy) adC (groups-1) ∧
      out.wk = 2 ∧ out.cost ≤ 160 ∧ out.need ≤ state.mem.length+state.bs.length+70 := by
  have ix := (List.getElem?_eq_some_iff.mp fx).1
  have iy := (List.getElem?_eq_some_iff.mp fy).1
  have length := valid.length
  have xv := i32_valid (X : Int) (by omega) (by omega)
  have yv := i32_valid (Y : Int) (by omega) (by omega)
  have xvalid := valid.forest.valid vx (List.mem_of_getElem? fx)
  have yvalid := valid.forest.valid vy (List.mem_of_getElem? fy)
  have wx := valid.weights X vx fx nx
  have wy := valid.weights Y vy fy ny
  have nxv := i32_valid (-vx) (by omega) (by omega)
  have nyv := i32_valid (-vy) (by omega) (by omega)
  have countValid := valid.count_range.2.2
  have sumValid := (valid.sum_valid X Y vx vy fx fy nx ny different).2.2
  have decrementValid := (valid.decrement_valid X Y ⟨vx,fx,nx⟩ ⟨vy,fy,ny⟩ different).2
  have equal := eq_value state vec adX adY X Y lx ly xv yv
  rw [if_neg different] at equal
  have first := Proofs.UfUniteCall.pexecW_branch_false i32 fuel eqE (.sequence (.scope retX) Sk) Sk state vec
    equal _ (pexecW_skip i32 fuel state vec)
  have compare := comparison_value state vec adX adY X Y vx vy lx ly length ix iy fx fy xvalid yvalid nxv nyv
  by_cases swap : -vx < -vy
  · rw [if_pos swap] at compare
    obtain ⟨rs,ran,ps,vs,ret,cost,need,work⟩ := swap_exec state vec adX adY X Y lx ly separate bindings xv yv fuel
    have second := Proofs.UfUniteCall.pexecW_branch_true i32 fuel comparison swapBlock Sk state vec
      1 compare (by decide) _ ran
    let swapped := setP (setP state adX (Y : Int)) adY (X : Int)
    have sx : Loc swapped 8 adX Y := loc_set_other _ _ _ _ _ _ (loc_set _ _ _ _ _ lx) (Ne.symm separate)
    have sy : Loc swapped 13 adY X := loc_set _ _ _ _ _ (loc_set_other _ _ _ _ _ _ ly separate)
    have sc : Loc swapped 0 adC groups := loc_set_other _ _ _ _ _ _
      (loc_set_other _ _ _ _ _ _ lc (Ne.symm cx)) (Ne.symm cy)
    have reversed : i32.valid (vy+vx) = true := by rw [Int.add_comm]; exact sumValid
    obtain ⟨rw_,wrun,wret,wvec,wps,wwork,wcost,wneed⟩ := writes_exec swapped vec adX adY adC Y X vy vx groups
      sx sy sc cx length iy ix fy fx yvalid xvalid countValid reversed decrementValid fuel
    have after := seqW_some second ret (by rw [ps,vs]; exact wrun)
    have all := seqW_some first rfl after
    refine ⟨_,all,?_,?_,?_,?_,?_,?_⟩
    · simpa [swap] using wret
    · simpa [swap,Int.add_comm] using wvec
    · simpa [orderedState,swap,swapped] using wps
    · simp [wwork,work]
    · simp [vwp,NExpr.nodes,Container.nodes,rdK] at *
      omega
    · simp [vwp,NExpr.nodes,Container.nodes,rdK,swapped,setP] at *
      omega
  · rw [if_neg swap] at compare
    have second := Proofs.UfUniteCall.pexecW_branch_false i32 fuel comparison swapBlock Sk state vec
      compare _ (pexecW_skip i32 fuel state vec)
    obtain ⟨rw_,wrun,wret,wvec,wps,wwork,wcost,wneed⟩ := writes_exec state vec adX adY adC X Y vx vy groups
      lx ly lc cx length ix iy fx fy xvalid yvalid countValid sumValid decrementValid fuel
    have after := seqW_some second rfl wrun
    have all := seqW_some first rfl after
    refine ⟨_,all,?_,?_,?_,?_,?_,?_⟩
    · simpa [swap] using wret
    · simpa [swap] using wvec
    · simpa [orderedState,swap] using wps
    · simp [wwork]
    · simp [vwp,NExpr.nodes,Container.nodes,rdK] at *
      omega
    · simp [vwp,NExpr.nodes,Container.nodes,rdK] at *
      omega

def finalState (state : PS) (vec : List Int) (adX adY adC X Y : Nat) (groups : Int) : PS :=
  if X=Y then state else setP (orderedState state adX adY X Y (vec.getD X 0) (vec.getD Y 0)) adC (groups-1)

theorem tail_correct (state : PS) (vec : List Int) (groups : Int) (rank : Nat → Nat)
    (valid : Proofs.UfClassInvariant.Valid vec groups rank) (adX adY adC X Y : Nat)
    (lx : Loc state 8 adX X) (ly : Loc state 13 adY Y) (lc : Loc state 0 adC groups)
    (separate : adX ≠ adY) (cx : adC ≠ adX) (cy : adC ≠ adY) (bindings : state.bs.length = 14)
    (rootX : ∃ w, vec[X]? = some w ∧ w < 0) (rootY : ∃ w, vec[Y]? = some w ∧ w < 0) (fuel : Nat) :
    ∃ out, pexecW i32 fuel tail state vec = some out ∧
      out.ret = some (Proofs.UfUniteCall.uniteX vec X Y : Int) ∧
      out.vec = Proofs.UfUniteCall.uniteVec vec X Y ∧ out.ps = finalState state vec adX adY adC X Y groups ∧
      out.wk = (if X=Y then 0 else 2) ∧ out.cost ≤ 160 ∧ out.need ≤ state.mem.length+state.bs.length+70 ∧
      ∃ rank', Proofs.UfClassInvariant.Valid out.vec (if X=Y then groups else groups-1) rank' := by
  obtain ⟨newRank,newValid⟩ := valid.unite_vec X Y rootX rootY
  by_cases same : X=Y
  · subst Y
    obtain ⟨vx,fx,nx⟩ := rootX
    have inside := (List.getElem?_eq_some_iff.mp fx).1
    have length := valid.length
    have rootValid := i32_valid (X : Int) (by omega) (by omega)
    obtain ⟨out,run,stateEq,vecEq,ret,cost,need,work⟩ := same_exec state vec adX adY X lx ly rootValid fuel
    refine ⟨out,run,?_,?_,?_,?_,by omega,by omega,newRank,?_⟩
    · simpa [Proofs.UfUniteCall.uniteX] using ret
    · simpa [Proofs.UfUniteCall.uniteVec] using vecEq
    · simpa [finalState] using stateEq
    · simpa using work
    · simpa [vecEq,Proofs.UfUniteCall.uniteVec] using newValid
  · obtain ⟨vx,fx,nx⟩ := rootX
    obtain ⟨vy,fy,ny⟩ := rootY
    obtain ⟨out,run,ret,vecEq,stateEq,work,cost,need⟩ := different_exec state vec groups rank valid
      adX adY adC X Y vx vy lx ly lc separate cx cy bindings fx fy nx ny same fuel
    have dx := Proofs.UfUniteCall.getD_of vec X vx fx
    have dy := Proofs.UfUniteCall.getD_of vec Y vy fy
    refine ⟨out,run,?_,?_,?_,?_,cost,need,newRank,?_⟩
    · simpa [Proofs.UfUniteCall.uniteX,dx,dy,fx,fy] using ret
    · simpa [Proofs.UfUniteCall.uniteVec,Proofs.UfUniteCall.uniteX,Proofs.UfUniteCall.uniteY,
        Proofs.UfMergeInvariant.linked,same,dx,dy,fx,fy] using vecEq
    · simpa [finalState,same,dx,dy,fx,fy] using stateEq
    · simpa [same] using work
    · have actual : out.vec = Proofs.UfUniteCall.uniteVec vec X Y := by
        simpa [Proofs.UfUniteCall.uniteVec,Proofs.UfUniteCall.uniteX,Proofs.UfUniteCall.uniteY,
          Proofs.UfMergeInvariant.linked,same,dx,dy,fx,fy] using vecEq
      rw [actual]
      exact newValid

end Proofs.UfUniteTail
