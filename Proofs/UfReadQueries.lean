import Proofs.UfReadInline
import Proofs.UfFieldsSize

namespace Proofs.UfReadQueries
open Proofs.UfReadInline Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecCapture
open Proofs.CppScalar Proofs.DoublingNested Proofs.PrefixSumsCall
open Proofs.PowModStep (Sk)

abbrev low (a : Nat) : NExpr := .binary bT .le (.literal i32 0) (.variable i32 a)
abbrev high (a : Nat) : NExpr := .binary bT .lt (.variable i32 a)
  (.cast i32 (.size (.integer i32) (.local 0)))
abbrev retSize : Command := .sequence (.primitive (.ret
  (.unary i32 .neg (.read i32 (.local 0) (.cast u64 (.variable i32 6)))))) Sk
abbrev sizeBody : Command := .sequence (.primitive (.check (low 3)))
  (.sequence (.primitive (.check (high 3))) (plug (inlined 3 2 3) retSize))
abbrev retSame : Command := .sequence (.primitive (.ret
  (.binary bT .eq (.variable i32 8) (.variable i32 12)))) Sk
abbrev sameBody : Command := .sequence (.primitive (.check (low 3)))
  (.sequence (.primitive (.check (high 3)))
    (.sequence (.primitive (.check (low 4)))
      (.sequence (.primitive (.check (high 4)))
        (plug (inlined 4 2 3) (.sequence (.primitive (.declare i32 true (.variable i32 7)))
          (plug (inlined 8 2 4) (.sequence (.primitive (.declare i32 true (.variable i32 11))) retSame)))))))


open Proofs.VecExpr Proofs.VecWrite Proofs.VecKitW Proofs.VectorFillCall Proofs.UfRootCall
open Proofs.UfInlineRoot (env_old env_new)
open Proofs.CppState (Cell Binding)

theorem low_value (state : PS) (vec : List Int) (slot : Nat) (a : Nat)
    (value : penv1 state slot i32 = some (a : Int)) :
    vdenL i32 vec (penv1 state) (low slot) = some 1 := by
  rw [vdenL_scalar _ _ _ _ rfl]
  simp only [NExpr.denote,show i32.valid 0 = true from rfl,ite_true,value,Option.bind_some]
  change bT.convert (if 0 ≤ (a : Int) then 1 else 0) = some 1
  rw [ite_eq_left (by omega)]; rfl

theorem high_value (state : PS) (vec : List Int) (slot : Nat) (a : Nat)
    (value : penv1 state slot i32 = some (a : Int))
    (length : vec.length < 2147483648) (inside : a < vec.length) :
    vdenL i32 vec (penv1 state) (high slot) = some 1 := by
  have nv := Proofs.VectorSumCall.i32_valid (vec.length : Int) (by omega) (by omega)
  have castsize : vdenL i32 vec (penv1 state) (.cast i32 (.size (.integer i32) (.local 0))) = some (vec.length : Int) := by
    have size : vdenL i32 vec (penv1 state) (.size (.integer i32) (.local 0)) = some (vec.length : Int) := by
      simp [vdenL,NExpr.scalarOnly]
    rw [vdenL_cast _ _ _ _ _ rfl,size,Option.bind_some]
    exact Proofs.VectorSumCall.conv_signed i32 rfl rfl _ nv
  have av : vdenL i32 vec (penv1 state) (.variable i32 slot) = some (a : Int) := by
    rw [vdenL_scalar _ _ _ _ rfl]; exact value
  change (vdenL i32 vec (penv1 state) (.variable i32 slot)).bind (fun x =>
    (vdenL i32 vec (penv1 state) (.cast i32 (.size (.integer i32) (.local 0)))).bind (fun y =>
      bT.convert (binaryValue .lt x y))) = some 1
  rw [av,Option.bind_some,castsize,Option.bind_some]
  change bT.convert (if (a : Int) < vec.length then 1 else 0) = some 1
  rw [ite_eq_left (by omega)]; rfl

abbrev sizeExpr (slot : Nat) : NExpr := .unary i32 .neg
  (.read i32 (.local 0) (.cast u64 (.variable i32 slot)))

theorem size_value (vec : List Int) (state : PS) (slot r : Nat) (w : Int)
    (bound : r < 18446744073709551616) (rv : penv1 state slot i32 = some (r : Int))
    (found : vec[r]? = some w) (valid : i32.valid w = true) (resultValid : i32.valid (-w) = true) :
    vdenL i32 vec (penv1 state) (sizeExpr slot) = some (-w) := by
  have index : (NExpr.cast u64 (.variable i32 slot)).denote (penv1 state) = some (r : Int) := by
    simp only [NExpr.denote,rv,Option.bind_some]
    apply Ty.convert_of_valid
    exact Proofs.Mod61Body.u64_lt r bound
  have read : vdenL i32 vec (penv1 state) (.read i32 (.local 0) (.cast u64 (.variable i32 slot))) = some w := by
    unfold vdenL
    simp [NExpr.scalarOnly,index,elemAtL,found,valid]
  change (vdenL i32 vec (penv1 state) (.read i32 (.local 0) (.cast u64 (.variable i32 slot)))).bind
    (fun x => i32.convert (unaryValue .neg x)) = some (-w)
  rw [read,Option.bind_some]
  exact Ty.convert_of_valid _ _ resultValid

theorem size_correct (state : PS) (slots : state.bs.length = 3) (vec : List Int)
    (rank : Nat → Nat) (forest : Forest vec rank) (length : vec.length < 2147483648)
    (weights : Proofs.UfFieldsSize.Weights vec) (n : Int) (nvalid : i32.valid n = true)
    (a : Nat) (inside : a < vec.length) (nv : penv1 state 2 i32 = some n)
    (av : penv1 state 3 i32 = some (a : Int)) (fuel : Nat) (enough : rank a+2 ≤ fuel) :
    ∃ (out : PRW) (r : Nat) (w : Int), pexecW i32 fuel sizeBody state vec = some out ∧
      out.ret = some (-w) ∧ Reach vec a r ∧ r < vec.length ∧ vec[r]? = some w ∧ w < 0 ∧
      i32.valid (-w) = true ∧ out.vec = vec ∧ out.ps = inlineState state n r ∧
      out.cost ≤ 16 * rank a+40 ∧ out.need ≤ state.mem.length+state.bs.length+30 ∧ out.wk = 0 := by
  have lowVal := low_value state vec 3 a av
  have highVal := high_value state vec 3 a av length inside
  have lc := (pexecW_prim i32 fuel (.check (low 3)) state vec).trans
    (pstmtW_check_ok i32 state vec (low 3) 1 lowVal (by decide))
  have hc := (pexecW_prim i32 fuel (.check (high 3)) state vec).trans
    (pstmtW_check_ok i32 state vec (high 3) 1 highVal (by decide))
  obtain ⟨one,r,run,ret,afterState,reach,rl,root,unchanged,cost,need,work,tail⟩ :=
    inlined_correct state vec rank forest length 2 3 n nvalid a nv av inside fuel enough
  obtain ⟨w,found,negative⟩ := root
  have lower := weights r w found negative
  have resultValid := Proofs.VectorSumCall.i32_valid (-w) (by omega) (by omega)
  have rvalid := Proofs.VectorSumCall.i32_valid (r : Int) (by omega) (by omega)
  have rv : penv1 one.ps 6 i32 = some (r : Int) := by
    rw [afterState]
    simpa only [slots] using inline_env_result state n r rvalid
  have value := size_value vec one.ps 6 r w (by omega) rv found
    (forest.valid w (List.mem_of_getElem? found)) resultValid
  rw [←unchanged] at value
  have returned := seqW_ret (b := Sk)
    ((pexecW_prim i32 fuel (.ret (sizeExpr 6)) one.ps one.vec).trans
      (pstmtW_ret_ok i32 one.ps one.vec (sizeExpr 6) (-w) value)) rfl
  have continued := tail retSize _ returned
  have all := seqW_some lc rfl (seqW_some hc rfl continued)
  rw [slots] at all
  refine ⟨_,r,w,all,rfl,reach,rl,found,negative,resultValid,unchanged,afterState,?_,?_,?_⟩
  · have lw : vwp (low 3) = (3,3) := rfl
    have hw : vwp (high 3) = (6,6) := rfl
    have rw : vwp (sizeExpr 6) = (6,6) := rfl
    change (vwp (low 3)).1+1+((vwp (high 3)).1+1+(one.cost+((vwp (sizeExpr 6)).1+1))) ≤ _
    rw [lw,hw,rw]; dsimp; omega
  · have lw : vwp (low 3) = (3,3) := rfl
    have hw : vwp (high 3) = (6,6) := rfl
    have rw : vwp (sizeExpr 6) = (6,6) := rfl
    change max (state.mem.length+3+(vwp (low 3)).2+2)
      (max (state.mem.length+3+(vwp (high 3)).2+2)
        (max one.need (one.ps.mem.length+one.ps.bs.length+(vwp (sizeExpr 6)).2+2))) ≤ _
    have mem : one.ps.mem.length = state.mem.length+3 := by rw [afterState]; simp [inlineState]
    have bs : one.ps.bs.length = state.bs.length+3 := by rw [afterState]; simp [inlineState]
    simp [lw,hw,rw,mem,bs]; omega
  · change 0+(0+(one.wk+0)) = 0
    omega


theorem declare_run (state : PS) (vec : List Int) (slot : Nat) (v : Int)
    (value : penv1 state slot i32 = some v) (valid : i32.valid v = true) (fuel : Nat) :
    pexecW i32 fuel (.primitive (.declare i32 true (.variable i32 slot))) state vec =
      some ⟨appended i32 v state,vec,none,2,state.mem.length+state.bs.length+5,0⟩ := by
  have den : vdenL i32 vec (penv1 state) (.variable i32 slot) = some v := by
    rw [vdenL_scalar _ _ _ _ rfl]; exact value
  exact (pexecW_prim i32 fuel _ _ _).trans (pstmtW_declare_ok i32 state vec i32 true
    (.variable i32 slot) v den v (Proofs.VectorSumCall.conv_signed i32 rfl rfl _ valid))

def sameState (state : PS) (n r1 r2 : Int) : PS :=
  appended i32 r2 (inlineState (appended i32 r1 (inlineState state n r1)) n r2)

theorem same_correct (state : PS) (slots : state.bs.length = 4) (vec : List Int)
    (rank : Nat → Nat) (forest : Forest vec rank) (length : vec.length < 2147483648)
    (n : Int) (nvalid : i32.valid n = true) (a b : Nat) (ha : a < vec.length) (hb : b < vec.length)
    (nv : penv1 state 2 i32 = some n) (av : penv1 state 3 i32 = some (a : Int))
    (bv : penv1 state 4 i32 = some (b : Int)) (fuel : Nat) (fa : rank a+2 ≤ fuel) (fb : rank b+2 ≤ fuel) :
    ∃ (out : PRW) (r1 r2 : Nat), pexecW i32 fuel sameBody state vec = some out ∧
      out.ret = some (if r1=r2 then 1 else 0) ∧ Reach vec a r1 ∧ Reach vec b r2 ∧
      r1 < vec.length ∧ r2 < vec.length ∧ (∃ w, vec[r1]? = some w ∧ w < 0) ∧
      (∃ w, vec[r2]? = some w ∧ w < 0) ∧ out.vec = vec ∧ out.ps = sameState state n r1 r2 ∧
      out.cost ≤ 16 * rank a+16 * rank b+74 ∧ out.need ≤ state.mem.length+state.bs.length+40 ∧ out.wk = 0 := by
  have la := low_value state vec 3 a av
  have ua := high_value state vec 3 a av length ha
  have lb := low_value state vec 4 b bv
  have ub := high_value state vec 4 b bv length hb
  obtain ⟨one,r1,run1,ret1,state1,reach1,rl1,root1,unchanged1,cost1,need1,work1,tail1⟩ :=
    inlined_correct state vec rank forest length 2 3 n nvalid a nv av ha fuel fa
  have r1valid := Proofs.VectorSumCall.i32_valid (r1 : Int) (by omega) (by omega)
  have firstResult : penv1 one.ps 7 i32 = some (r1 : Int) := by
    rw [state1]
    simpa only [slots] using inline_env_result state n r1 r1valid
  have len1 : one.ps.bs.length = 7 := by rw [state1]; simp [inlineState,slots]
  let withX := appended i32 (r1 : Int) one.ps
  have xRun := declare_run one.ps vec 7 r1 firstResult r1valid fuel
  have nextN : penv1 withX 2 i32 = some n := by
    apply env_old one.ps i32 i32 n r1 2
    rw [state1]; exact inline_env_old state n r1 n 2 nv
  have nextB : penv1 withX 4 i32 = some (b : Int) := by
    apply env_old one.ps i32 i32 b r1 4
    rw [state1]; exact inline_env_old state n r1 b 4 bv
  have lenX : withX.bs.length = 8 := by simp [withX,appended,len1]
  obtain ⟨two,r2,run2,ret2,state2,reach2,rl2,root2,unchanged2,cost2,need2,work2,tail2⟩ :=
    inlined_correct withX vec rank forest length 2 4 n nvalid b nextN nextB hb fuel fb
  have r2valid := Proofs.VectorSumCall.i32_valid (r2 : Int) (by omega) (by omega)
  have secondResult : penv1 two.ps 11 i32 = some (r2 : Int) := by
    rw [state2]
    simpa only [lenX] using inline_env_result withX n r2 r2valid
  have len2 : two.ps.bs.length = 11 := by rw [state2]; simp [inlineState,lenX]
  let withY := appended i32 (r2 : Int) two.ps
  have yRun := declare_run two.ps vec 11 r2 secondResult r2valid fuel
  have xValue : penv1 withX 8 i32 = some (r1 : Int) := by
    simpa only [len1] using env_new one.ps i32 r1 r1valid
  have firstFinal : penv1 withY 8 i32 = some (r1 : Int) := by
    apply env_old two.ps i32 i32 r1 r2 8
    rw [state2]; exact inline_env_old withX n r2 r1 8 xValue
  have secondFinal : penv1 withY 12 i32 = some (r2 : Int) := by
    simpa only [len2] using env_new two.ps i32 r2 r2valid
  have value : vdenL i32 vec (penv1 withY) (.binary bT .eq (.variable i32 8) (.variable i32 12)) =
      some (if r1=r2 then 1 else 0) := by
    rw [vdenL_scalar _ _ _ _ rfl]
    simp only [NExpr.denote,firstFinal,secondFinal,Option.bind_some]
    have comparison : binaryValue .eq (r1 : Int) (r2 : Int) = if r1=r2 then 1 else 0 := by
      by_cases equal : r1=r2
      · simp [binaryValue,equal]
      · have unequal : (r1 : Int) ≠ (r2 : Int) := by omega
        simp [binaryValue,equal,unequal]
    rw [comparison]
    by_cases equal : r1=r2 <;> simp [equal,Ty.convert]
  have returned := seqW_ret (b := Sk)
    ((pexecW_prim i32 fuel (.ret (.binary bT .eq (.variable i32 8) (.variable i32 12))) withY vec).trans
      (pstmtW_ret_ok i32 withY vec _ _ value)) rfl
  have yThen := seqW_some yRun rfl returned
  rw [unchanged2] at tail2
  have after2 := tail2 (.sequence (.primitive (.declare i32 true (.variable i32 11))) retSame) _ yThen
  rw [lenX] at after2
  have xThen := seqW_some xRun rfl after2
  rw [unchanged1] at tail1
  have after1 := tail1 (.sequence (.primitive (.declare i32 true (.variable i32 7)))
    (plug (inlined 8 2 4) (.sequence (.primitive (.declare i32 true (.variable i32 11))) retSame))) _ xThen
  rw [slots] at after1
  have all := Proofs.UfBounds.prepend la (Proofs.UfBounds.prepend ua
    (Proofs.UfBounds.prepend lb (Proofs.UfBounds.prepend ub after1)))
  refine ⟨_,r1,r2,all,rfl,reach1,reach2,rl1,rl2,root1,root2,rfl,?_,?_,?_,?_⟩
  · change withY = sameState state n r1 r2
    simp only [withY,withX,sameState,state1,state2]
  · have lw (slot : Nat) : vwp (low slot) = (3,3) := rfl
    have hw (slot : Nat) : vwp (high slot) = (6,6) := rfl
    have resultW : vwp (.binary bT .eq (.variable i32 8) (.variable i32 12)) = (3,3) := rfl
    change (vwp (low 3)).1+1+((vwp (high 3)).1+1+((vwp (low 4)).1+1+((vwp (high 4)).1+1+
      (one.cost+(2+(two.cost+(2+((vwp (.binary bT .eq (.variable i32 8) (.variable i32 12))).1+1)))))))) ≤ _
    rw [lw,hw,lw,hw,resultW]; dsimp; omega
  · have m1 : one.ps.mem.length = state.mem.length+3 := by rw [state1]; simp [inlineState]
    have mX : withX.mem.length = state.mem.length+4 := by simp [withX,appended,m1]
    have m2 : two.ps.mem.length = state.mem.length+7 := by rw [state2]; simp [inlineState,mX]
    have mY : withY.mem.length = state.mem.length+8 := by simp [withY,appended,m2]
    have lY : withY.bs.length = 12 := by simp [withY,appended,len2]
    have lw (slot : Nat) : vwp (low slot) = (3,3) := rfl
    have hw (slot : Nat) : vwp (high slot) = (6,6) := rfl
    have resultW : vwp (.binary bT .eq (.variable i32 8) (.variable i32 12)) = (3,3) := rfl
    change max (state.mem.length+state.bs.length+(vwp (low 3)).2+2)
      (max (state.mem.length+state.bs.length+(vwp (high 3)).2+2)
        (max (state.mem.length+state.bs.length+(vwp (low 4)).2+2)
          (max (state.mem.length+state.bs.length+(vwp (high 4)).2+2)
            (max one.need (max (one.ps.mem.length+one.ps.bs.length+5)
              (max two.need (max (two.ps.mem.length+two.ps.bs.length+5)
                (withY.mem.length+withY.bs.length+(vwp (.binary bT .eq (.variable i32 8) (.variable i32 12))).2+2)))))))) ≤ _
    rw [mX,lenX] at need2
    simp [lw,hw,resultW,m1,m2,mY,len1,len2,lY]; omega
  · change one.wk+(0+(two.wk+(0+0))) = 0
    omega

abbrev counterBody : Command := .sequence (.primitive (.ret (.variable i32 1))) Sk

theorem counter_correct (state : PS) (vec : List Int) (count : Int)
    (value : penv1 state 1 i32 = some count) (fuel : Nat) :
    pexecW i32 fuel counterBody state vec =
      some ⟨state,vec,some count,2,state.mem.length+state.bs.length+3,0⟩ := by
  have den : vdenL i32 vec (penv1 state) (.variable i32 1) = some count := by
    rw [vdenL_scalar _ _ _ _ rfl]; exact value
  exact seqW_ret ((pexecW_prim i32 fuel (.ret (.variable i32 1)) state vec).trans
    (pstmtW_ret_ok i32 state vec (.variable i32 1) count den)) rfl

end Proofs.UfReadQueries
