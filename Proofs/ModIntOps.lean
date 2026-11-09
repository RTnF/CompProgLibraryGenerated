import Proofs.ModIntCall
import Proofs.ModIntExec
import Proofs.Generated.ModInt
import Proofs.ScalarStraight
import Proofs.MultiVecCall
import Proofs.MultiKit
import Proofs.BellmanFordExec
import Proofs.LowerBoundIndexCall
import Proofs.VecWriteCall
import Proofs.VecCall
import Proofs.ScalarCall

namespace Proofs.ModIntOps
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCall
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested
open Proofs.PowModStep (Sk rem_value)
open Proofs.Mod61Body (u64_lt)
open Proofs.ModIntExec (convert32 lit32_value u32_valid_nat)
open Proofs.BellmanFordExec (pexecM_branch_true pexecM_branch_false)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.ScalarStraight
open Proofs.ExtremaCall (scalarCell_facts take_set_memory)
open Proofs.LowerBoundIndexCall (validN)

abbrev cu32 (x : Nat) : Cell := ⟨u32, (x : Int)⟩

/-- The machine for a function without vectors. -/
def mvOp (L0 T0 sc N : Nat) : MV where
  nv := 0
  ty := fun _ => u32
  wV := fun _ => false
  flag := fun _ => false
  R := fun _ => 0
  vsc := fun _ => 0
  perm := by intro k hk; simp at hk
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by intro j k hj hk; omega

/-- Reading variable `k` of a `u32` cell. -/
theorem var_val (mv : MV) (hnv : mv.nv = 0) (vv : Nat → List Int) (P cs : List Cell) (k x : Nat) (hk : cs[k]? = some (cu32 x))
    (hx : x < 4294967296) :
    vdenM mv vv (penvN mv.nv (gS P cs)) (.variable u32 k) = some (x : Int) := by
  rw [vdenM_scalar _ _ _ _ rfl, den_variable]
  have := gSM_env mv.nv P cs k (cu32 x) hk (u32_valid_nat x hx)
  rw [hnv, Nat.zero_add] at this
  rw [hnv]
  exact this

theorem lit_val (mv : MV) (vv : Nat → List Int) (ps : PS) (m : Nat) (hm : m < 4294967296) :
    vdenM mv vv (penvN mv.nv ps) (.literal u32 (m : Int)) = some (m : Int) := by
  rw [vdenM_scalar _ _ _ _ rfl]
  exact lit32_value _ m hm


theorem env_u32 (mv : MV) (hnv : mv.nv = 0) (P cs : List Cell) (k x : Nat) (hk : cs[k]? = some (cu32 x))
    (hx : x < 4294967296) : penvN mv.nv (gS P cs) k u32 = some (x : Int) := by
  have := gSM_env mv.nv P cs k (cu32 x) hk (u32_valid_nat x hx)
  rw [hnv, Nat.zero_add] at this
  rw [hnv]
  exact this

theorem ge_val (mv : MV) (hnv : mv.nv = 0) (vv : Nat → List Int) (P cs : List Cell) (k v m : Nat)
    (hk : cs[k]? = some (cu32 v)) (hv : v < 4294967296) (hm : m < 4294967296) :
    vdenM mv vv (penvN mv.nv (gS P cs)) (.binary bl .ge (.variable u32 k) (.literal u32 (m : Int))) =
      some (if m ≤ v then 1 else 0) := by
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, env_u32 mv hnv P cs k v hk hv, lit32_value _ m hm]
  simp only [Option.bind_some, binaryValue, convert_bl]
  by_cases c : m ≤ v
  · have : (v : Int) ≥ (m : Int) := by omega
    simp [this, c]
  · have : ¬ ((v : Int) ≥ (m : Int)) := by omega
    simp [this, c]

theorem lit_sub_val (mv : MV) (hnv : mv.nv = 0) (vv : Nat → List Int) (P cs : List Cell) (k v m : Nat)
    (hk : cs[k]? = some (cu32 v)) (hv : v < 4294967296) (hm : m < 4294967296) (hmv : m ≤ v) :
    vdenM mv vv (penvN mv.nv (gS P cs)) (.binary u32 .sub (.variable u32 k) (.literal u32 (m : Int))) =
      some ((v - m : Nat) : Int) := by
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, env_u32 mv hnv P cs k v hk hv, lit32_value _ m hm]
  simp only [Option.bind_some, binaryValue]
  have : (v : Int) - (m : Int) = ((v - m : Nat) : Int) := by omega
  rw [this]
  exact convert32 _ (by omega)

theorem add_val (mv : MV) (hnv : mv.nv = 0) (vv : Nat → List Int) (P cs : List Cell) (k1 k2 x y : Nat)
    (h1 : cs[k1]? = some (cu32 x)) (h2 : cs[k2]? = some (cu32 y)) (hx : x < 4294967296) (hy : y < 4294967296)
    (hs : x + y < 4294967296) :
    vdenM mv vv (penvN mv.nv (gS P cs)) (.binary u32 .add (.variable u32 k1) (.variable u32 k2)) =
      some ((x + y : Nat) : Int) := by
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, den_variable, env_u32 mv hnv P cs k1 x h1 hx,
    env_u32 mv hnv P cs k2 y h2 hy]
  simp only [Option.bind_some, binaryValue]
  have : (x : Int) + (y : Int) = ((x + y : Nat) : Int) := by omega
  rw [this]
  exact convert32 _ hs

abbrev copyReturn (k : Nat) : Command :=
  .sequence (.primitive (.declare u32 true (.variable u32 k)))
    (.sequence (.primitive (.ret (.variable u32 k))) Sk)

abbrev addBody (m : Nat) : Command :=
  .sequence (.primitive (.declare u32 true (.variable u32 0)))
    (.sequence (.primitive (.assign 2 u32 (.binary u32 .add (.variable u32 2) (.variable u32 1))))
      (.sequence (.branch (.binary bl .ge (.variable u32 2) (.literal u32 (m : Int)))
          (.sequence (.scope (.sequence (.primitive (.assign 2 u32
            (.binary u32 .sub (.variable u32 2) (.literal u32 (m : Int))))) Sk)) Sk) Sk)
        (copyReturn 2)))

theorem add_body_eq : (Proofs.ModIntInstance.operator_add_ModInt_998244353U).body = addBody 998244353 := rfl


theorem take_gS_same (P cs cs' : List Cell) (h : cs'.length = cs.length) :
    (gS P cs').mem.take (gS P cs).mem.length = (gS P cs').mem := by
  have := gS_mem_len P cs'
  rw [gS_mem_len P cs, ← h, ← this]
  exact List.take_length

theorem gS_scope_same (P cs cs' : List Cell) (h : cs'.length = cs.length) :
    (⟨(gS P cs').mem.take (gS P cs).mem.length, (gS P cs').bs.take (gS P cs).bs.length⟩ : PS) = gS P cs' := by
  have hm := take_gS_same P cs cs' h
  have hb : (gS P cs').bs.take (gS P cs).bs.length = (gS P cs').bs := by
    rw [gS_bs_len P cs, ← h, ← gS_bs_len P cs']
    exact List.take_length
  rw [hm, hb]

theorem ret_var (mv : MV) (hnv : mv.nv = 0) (fu : Nat) (P cs : List Cell) (vv : Nat → List Int) (k v : Nat)
    (hk : cs[k]? = some (cu32 v)) (hv : v < 4294967296) :
    pexecM mv fu (copyReturn k) (gS P cs) vv =
      some ⟨gS P (cs ++ [cu32 v]),vv,some (v : Int),4,
        (gS P cs).mem.length+(gS P cs).bs.length+5,0⟩ := by
  have q0 := (pexecM_prim mv fu _ _ _).trans
    (gSM_decl mv P cs vv u32 (.variable u32 k) (v : Int) (v : Int)
      (var_val mv hnv vv P cs k v hk hv) (convert32 v hv))
  have index : k < cs.length := (List.getElem?_eq_some_iff.mp hk).1
  have read : (cs ++ [cu32 v])[k]? = some (cu32 v) := by
    rw [List.getElem?_append_left index]; exact hk
  have q1 := seqM_ret (fu:=fu) (b:=Sk) (by
    rw [pexecM_prim,pstmtM_ret_ok mv _ vv _ _ (var_val mv hnv vv P (cs ++ [cu32 v]) k v read hv)]) rfl
  have q := seqM_some q0 rfl q1
  have need : max (P.length+2*cs.length+1+4)
      (P.length+(cs.length+1)+(cs.length+1)+1+2) = P.length+cs.length+cs.length+5 := by omega
  simpa [copyReturn,vwp,NExpr.scalarOnly,NExpr.nodes,gS_mem_len,gS_bs_len,need] using q

/-- The tail `if (r >= m) { r -= m; } return r;` common to `+` (after the sum) -/
theorem add_exec (mv : MV) (hnv : mv.nv = 0) (fu : Nat) (P : List Cell) (vv : Nat → List Int) (m x y : Nat)
    (hm : 2 ≤ m) (hm2 : m ≤ 2147483648) (hx : x < m) (hy : y < m) :
    ∃ r : PRM, pexecM mv fu (addBody m) (gS P [cu32 x, cu32 y]) vv = some r ∧
      r.ret = some (((x + y) % m : Nat) : Int) ∧ r.ps = gS P [cu32 x, cu32 y, cu32 ((x + y) % m), cu32 ((x + y) % m)] ∧ r.vv = vv ∧
      r.cost ≤ 60 ∧ r.need ≤ P.length + 30 ∧ r.wk = 0 := by
  have hx32 : x < 4294967296 := by omega
  have hy32 : y < 4294967296 := by omega
  have hm32 : m < 4294967296 := by omega
  have hs : x + y < 4294967296 := by omega
  have c0 : ([cu32 x, cu32 y] : List Cell)[0]? = some (cu32 x) := rfl
  have s1 := gSM_decl mv P [cu32 x, cu32 y] vv u32 (.variable u32 0) (x : Int) (x : Int)
    (var_val mv hnv vv P _ 0 x c0 hx32) (convert32 x hx32)
  have q1 := (pexecM_prim mv fu _ _ _).trans s1
  have c2 : ([cu32 x, cu32 y] ++ [(⟨u32, (x : Int)⟩ : Cell)] : List Cell)[2]? = some (cu32 x) := rfl
  have c1 : ([cu32 x, cu32 y] ++ [(⟨u32, (x : Int)⟩ : Cell)] : List Cell)[1]? = some (cu32 y) := rfl
  have d2 := add_val mv hnv vv P _ 2 1 x y c2 c1 hx32 hy32 hs
  have s2 := gSM_assign mv P ([cu32 x, cu32 y] ++ [(⟨u32, (x : Int)⟩ : Cell)]) vv 2 (by simp) u32
    (.binary u32 .add (.variable u32 2) (.variable u32 1)) ((x + y : Nat) : Int) ((x + y : Nat) : Int) d2
    (cu32 x) c2 rfl (u32_valid_nat x hx32) (convert32 _ hs)
  rw [hnv, Nat.zero_add] at s2
  have q2 := (pexecM_prim mv fu _ _ _).trans s2
  have e1 : ([cu32 x, cu32 y] ++ [(⟨u32, (x : Int)⟩ : Cell)]).set 2 (⟨u32, ((x + y : Nat) : Int)⟩ : Cell) =
      [cu32 x, cu32 y, cu32 (x + y)] := rfl
  rw [e1] at q2
  have k2 : ([cu32 x, cu32 y, cu32 (x + y)] : List Cell)[2]? = some (cu32 (x + y)) := rfl
  have hge := ge_val mv hnv vv P [cu32 x, cu32 y, cu32 (x + y)] 2 (x + y) m k2 hs hm32
  by_cases hc : m ≤ x + y
  · -- reduce once
    rw [if_pos hc] at hge
    have hlt : x + y - m < 4294967296 := by omega
    have dsub := lit_sub_val mv hnv vv P [cu32 x, cu32 y, cu32 (x + y)] 2 (x + y) m k2 hs hm32 hc
    have sA := gSM_assign mv P [cu32 x, cu32 y, cu32 (x + y)] vv 2 (by simp) u32
      (.binary u32 .sub (.variable u32 2) (.literal u32 (m : Int))) ((x + y - m : Nat) : Int) ((x + y - m : Nat) : Int)
      dsub (cu32 (x + y)) k2 rfl (u32_valid_nat _ hs) (convert32 _ hlt)
    rw [hnv, Nat.zero_add] at sA
    have e2 : ([cu32 x, cu32 y, cu32 (x + y)] : List Cell).set 2 (⟨u32, ((x + y - m : Nat) : Int)⟩ : Cell) =
        [cu32 x, cu32 y, cu32 (x + y - m)] := rfl
    rw [e2] at sA
    have qA := (pexecM_prim mv fu _ _ _).trans sA
    have qS := seqM_some qA rfl (pexecM_skip mv fu (gS P [cu32 x, cu32 y, cu32 (x + y - m)]) vv)
    have qSc := pexecM_scope mv fu _ _ vv _ qS
    dsimp only at qSc
    rw [gS_scope_same P [cu32 x, cu32 y, cu32 (x + y)] [cu32 x, cu32 y, cu32 (x + y - m)] rfl] at qSc
    have qY := seqM_some qSc rfl (pexecM_skip mv fu (gS P [cu32 x, cu32 y, cu32 (x + y - m)]) vv)
    have qB := pexecM_branch_true mv fu _ _ Sk _ vv 1 hge (by decide) _ qY
    have hmod : (x + y) % m = x + y - m := by
      have : x + y < 2 * m := by omega
      rw [Nat.mod_eq_sub_mod hc, Nat.mod_eq_of_lt (by omega)]
    have kr : ([cu32 x, cu32 y, cu32 (x + y - m)] : List Cell)[2]? = some (cu32 (x + y - m)) := rfl
    have qR := ret_var mv hnv fu P _ vv 2 (x + y - m) kr hlt
    have qT := seqM_some qB rfl qR
    have p0 := seqM_some q2 rfl qT
    have p1 := seqM_some q1 rfl p0
    refine ⟨_, p1, ?_⟩
    simp [hmod, vwp, NExpr.scalarOnly, NExpr.nodes, gS_mem_len, gS_bs_len]
  · rw [if_neg hc] at hge
    have hmod : (x + y) % m = x + y := Nat.mod_eq_of_lt (by omega)
    have qB := pexecM_branch_false mv fu _ (.sequence (.scope (.sequence (.primitive (.assign 2 u32
      (.binary u32 .sub (.variable u32 2) (.literal u32 (m : Int))))) Sk)) Sk) Sk
      (gS P [cu32 x, cu32 y, cu32 (x + y)]) vv hge _ (pexecM_skip mv fu (gS P [cu32 x, cu32 y, cu32 (x + y)]) vv)
    have qR := ret_var mv hnv fu P _ vv 2 (x + y) k2 hs
    have qT := seqM_some qB rfl qR
    have p0 := seqM_some q2 rfl qT
    have p1 := seqM_some q1 rfl p0
    refine ⟨_, p1, ?_⟩
    simp [hmod, vwp, NExpr.scalarOnly, NExpr.nodes, gS_mem_len, gS_bs_len]


theorem sub_val (mv : MV) (hnv : mv.nv = 0) (vv : Nat → List Int) (P cs : List Cell) (k1 k2 x y : Nat)
    (h1 : cs[k1]? = some (cu32 x)) (h2 : cs[k2]? = some (cu32 y)) (hx : x < 4294967296) (hy : y < 4294967296) :
    vdenM mv vv (penvN mv.nv (gS P cs)) (.binary u32 .sub (.variable u32 k1) (.variable u32 k2)) =
      some (((x + 4294967296 - y) % 4294967296 : Nat) : Int) := by
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, den_variable, env_u32 mv hnv P cs k1 x h1 hx,
    env_u32 mv hnv P cs k2 y h2 hy]
  simp only [Option.bind_some, binaryValue, convert_u32]
  have : ((x : Int) - (y : Int)) % 4294967296 = (((x + 4294967296 - y) % 4294967296 : Nat) : Int) := by omega
  rw [this]

theorem addlit_val (mv : MV) (hnv : mv.nv = 0) (vv : Nat → List Int) (P cs : List Cell) (k v m : Nat)
    (hk : cs[k]? = some (cu32 v)) (hv : v < 4294967296) (hm : m < 4294967296) :
    vdenM mv vv (penvN mv.nv (gS P cs)) (.binary u32 .add (.variable u32 k) (.literal u32 (m : Int))) =
      some (((v + m) % 4294967296 : Nat) : Int) := by
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, env_u32 mv hnv P cs k v hk hv, lit32_value _ m hm]
  simp only [Option.bind_some, binaryValue, convert_u32]
  have : ((v : Int) + (m : Int)) % 4294967296 = (((v + m) % 4294967296 : Nat) : Int) := by omega
  rw [this]

theorem mul_val (mv : MV) (hnv : mv.nv = 0) (vv : Nat → List Int) (P cs : List Cell) (k1 k2 m x y : Nat)
    (h1 : cs[k1]? = some (cu32 x)) (h2 : cs[k2]? = some (cu32 y)) (hm : 0 < m) (hm2 : m < 4294967296)
    (hx : x < m) (hy : y < m) :
    vdenM mv vv (penvN mv.nv (gS P cs)) (.cast u32 (.divrem u64 true (.binary u64 .mul (.cast u64 (.variable u32 k1))
      (.cast u64 (.variable u32 k2))) (.cast u64 (.literal u32 (m : Int))))) = some ((x * y % m : Nat) : Int) := by
  have hxy : x * y < 18446744073709551616 := by
    have : x * y < m * m := Nat.mul_lt_mul'' hx hy
    have : m * m ≤ 4294967296 * 4294967296 := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hxv : u64.valid (x : Int) = true := u64_lt x (by omega)
  have hyv : u64.valid (y : Int) = true := u64_lt y (by omega)
  have hmv : u64.valid (m : Int) = true := u64_lt m (by omega)
  have lit : u32.valid (m : Int) = true := u32_valid_nat m (by omega)
  have rem := rem_value (x * y) m hm hxy
  have e0 := env_u32 mv hnv P cs k1 x h1 (by omega)
  have e1 := env_u32 mv hnv P cs k2 y h2 (by omega)
  rw [vdenM_scalar _ _ _ _ rfl]
  simp only [NExpr.denote, e0, e1, lit, ite_true, Option.bind_some, binaryValue]
  rw [Ty.convert_of_valid _ _ hxv, Ty.convert_of_valid _ _ hyv, Ty.convert_of_valid _ _ hmv]
  simp only [Option.bind_some]
  have e2 : (x : Int) * (y : Int) = ((x * y : Nat) : Int) := by omega
  rw [e2, Ty.convert_of_valid _ _ (u64_lt _ hxy)]
  simp only [Option.bind_some]
  rw [rem]
  simp only [Option.bind_some]
  exact convert32 _ (by have := Nat.mod_lt (x * y) hm; omega)

abbrev subBody (m : Nat) : Command :=
  .sequence (.primitive (.declare u32 true (.variable u32 0)))
    (.sequence (.primitive (.assign 2 u32 (.binary u32 .sub (.variable u32 2) (.variable u32 1))))
      (.sequence (.branch (.binary bl .ge (.variable u32 2) (.literal u32 (m : Int)))
          (.sequence (.scope (.sequence (.primitive (.assign 2 u32
            (.binary u32 .add (.variable u32 2) (.literal u32 (m : Int))))) Sk)) Sk) Sk)
        (copyReturn 2)))

abbrev mulBody (m : Nat) : Command :=
  .sequence (.primitive (.declare u32 true (.variable u32 0)))
    (.sequence (.primitive (.assign 2 u32 (.cast u32 (.divrem u64 true (.binary u64 .mul (.cast u64 (.variable u32 2))
      (.cast u64 (.variable u32 1))) (.cast u64 (.literal u32 (m : Int)))))))
      (copyReturn 2))

theorem sub_body_eq : (Proofs.ModIntInstance.operator_sub_ModInt_998244353U).body = subBody 998244353 := rfl
theorem mul_body_eq : (Proofs.ModIntInstance.operator_mul_ModInt_998244353U).body = mulBody 998244353 := rfl


theorem mul_exec (mv : MV) (hnv : mv.nv = 0) (fu : Nat) (P : List Cell) (vv : Nat → List Int) (m x y : Nat)
    (hm : 2 ≤ m) (hm2 : m ≤ 2147483648) (hx : x < m) (hy : y < m) :
    ∃ r : PRM, pexecM mv fu (mulBody m) (gS P [cu32 x, cu32 y]) vv = some r ∧
      r.ret = some ((x * y % m : Nat) : Int) ∧ r.ps = gS P [cu32 x, cu32 y, cu32 (x * y % m), cu32 (x * y % m)] ∧ r.vv = vv ∧
      r.cost ≤ 60 ∧ r.need ≤ P.length + 30 ∧ r.wk = 0 := by
  have hx32 : x < 4294967296 := by omega
  have hy32 : y < 4294967296 := by omega
  have hm32 : m < 4294967296 := by omega
  have hr : x * y % m < 4294967296 := by have := Nat.mod_lt (x * y) (show 0 < m by omega); omega
  have c0 : ([cu32 x, cu32 y] : List Cell)[0]? = some (cu32 x) := rfl
  have s1 := gSM_decl mv P [cu32 x, cu32 y] vv u32 (.variable u32 0) (x : Int) (x : Int)
    (var_val mv hnv vv P _ 0 x c0 hx32) (convert32 x hx32)
  have q1 := (pexecM_prim mv fu _ _ _).trans s1
  have c2 : ([cu32 x, cu32 y] ++ [(⟨u32, (x : Int)⟩ : Cell)] : List Cell)[2]? = some (cu32 x) := rfl
  have c1 : ([cu32 x, cu32 y] ++ [(⟨u32, (x : Int)⟩ : Cell)] : List Cell)[1]? = some (cu32 y) := rfl
  have d2 := mul_val mv hnv vv P _ 2 1 m x y c2 c1 (by omega) hm32 hx hy
  have s2 := gSM_assign mv P ([cu32 x, cu32 y] ++ [(⟨u32, (x : Int)⟩ : Cell)]) vv 2 (by simp) u32
    (.cast u32 (.divrem u64 true (.binary u64 .mul (.cast u64 (.variable u32 2)) (.cast u64 (.variable u32 1)))
      (.cast u64 (.literal u32 (m : Int))))) ((x * y % m : Nat) : Int) ((x * y % m : Nat) : Int) d2
    (cu32 x) c2 rfl (u32_valid_nat x hx32) (convert32 _ hr)
  rw [hnv, Nat.zero_add] at s2
  have q2 := (pexecM_prim mv fu _ _ _).trans s2
  have e1 : ([cu32 x, cu32 y] ++ [(⟨u32, (x : Int)⟩ : Cell)]).set 2 (⟨u32, ((x * y % m : Nat) : Int)⟩ : Cell) =
      [cu32 x, cu32 y, cu32 (x * y % m)] := rfl
  rw [e1] at q2
  have k2 : ([cu32 x, cu32 y, cu32 (x * y % m)] : List Cell)[2]? = some (cu32 (x * y % m)) := rfl
  have qR := ret_var mv hnv fu P _ vv 2 (x * y % m) k2 hr
  have p0 := seqM_some q2 rfl qR
  have p1 := seqM_some q1 rfl p0
  refine ⟨_, p1, ?_⟩
  simp [vwp, NExpr.scalarOnly, NExpr.nodes, gS_mem_len, gS_bs_len]

theorem sub_exec (mv : MV) (hnv : mv.nv = 0) (fu : Nat) (P : List Cell) (vv : Nat → List Int) (m x y : Nat)
    (hm : 2 ≤ m) (hm2 : m ≤ 2147483648) (hx : x < m) (hy : y < m) :
    ∃ r : PRM, pexecM mv fu (subBody m) (gS P [cu32 x, cu32 y]) vv = some r ∧
      r.ret = some (((x + m - y) % m : Nat) : Int) ∧ r.ps = gS P [cu32 x, cu32 y, cu32 ((x + m - y) % m), cu32 ((x + m - y) % m)] ∧ r.vv = vv ∧
      r.cost ≤ 60 ∧ r.need ≤ P.length + 30 ∧ r.wk = 0 := by
  have hx32 : x < 4294967296 := by omega
  have hy32 : y < 4294967296 := by omega
  have hm32 : m < 4294967296 := by omega
  obtain ⟨w, hw⟩ : ∃ w, w = (x + 4294967296 - y) % 4294967296 := ⟨_, rfl⟩
  have hwlt : w < 4294967296 := by omega
  have c0 : ([cu32 x, cu32 y] : List Cell)[0]? = some (cu32 x) := rfl
  have s1 := gSM_decl mv P [cu32 x, cu32 y] vv u32 (.variable u32 0) (x : Int) (x : Int)
    (var_val mv hnv vv P _ 0 x c0 hx32) (convert32 x hx32)
  have q1 := (pexecM_prim mv fu _ _ _).trans s1
  have c2 : ([cu32 x, cu32 y] ++ [(⟨u32, (x : Int)⟩ : Cell)] : List Cell)[2]? = some (cu32 x) := rfl
  have c1 : ([cu32 x, cu32 y] ++ [(⟨u32, (x : Int)⟩ : Cell)] : List Cell)[1]? = some (cu32 y) := rfl
  have d2 := sub_val mv hnv vv P _ 2 1 x y c2 c1 hx32 hy32
  rw [← hw] at d2
  have s2 := gSM_assign mv P ([cu32 x, cu32 y] ++ [(⟨u32, (x : Int)⟩ : Cell)]) vv 2 (by simp) u32
    (.binary u32 .sub (.variable u32 2) (.variable u32 1)) (w : Int) (w : Int) d2
    (cu32 x) c2 rfl (u32_valid_nat x hx32) (convert32 _ hwlt)
  rw [hnv, Nat.zero_add] at s2
  have q2 := (pexecM_prim mv fu _ _ _).trans s2
  have e1 : ([cu32 x, cu32 y] ++ [(⟨u32, (x : Int)⟩ : Cell)]).set 2 (⟨u32, (w : Int)⟩ : Cell) =
      [cu32 x, cu32 y, cu32 w] := rfl
  rw [e1] at q2
  have k2 : ([cu32 x, cu32 y, cu32 w] : List Cell)[2]? = some (cu32 w) := rfl
  have hge := ge_val mv hnv vv P [cu32 x, cu32 y, cu32 w] 2 w m k2 hwlt hm32
  by_cases hc : m ≤ w
  · rw [if_pos hc] at hge
    have hadd := addlit_val mv hnv vv P [cu32 x, cu32 y, cu32 w] 2 w m k2 hwlt hm32
    obtain ⟨z, hz⟩ : ∃ z, z = (w + m) % 4294967296 := ⟨_, rfl⟩
    have hzlt : z < 4294967296 := by omega
    rw [← hz] at hadd
    have sA := gSM_assign mv P [cu32 x, cu32 y, cu32 w] vv 2 (by simp) u32
      (.binary u32 .add (.variable u32 2) (.literal u32 (m : Int))) (z : Int) (z : Int)
      hadd (cu32 w) k2 rfl (u32_valid_nat _ hwlt) (convert32 _ hzlt)
    rw [hnv, Nat.zero_add] at sA
    have e2 : ([cu32 x, cu32 y, cu32 w] : List Cell).set 2 (⟨u32, (z : Int)⟩ : Cell) = [cu32 x, cu32 y, cu32 z] := rfl
    rw [e2] at sA
    have qA := (pexecM_prim mv fu _ _ _).trans sA
    have qS := seqM_some qA rfl (pexecM_skip mv fu (gS P [cu32 x, cu32 y, cu32 z]) vv)
    have qSc := pexecM_scope mv fu _ _ vv _ qS
    dsimp only at qSc
    rw [gS_scope_same P [cu32 x, cu32 y, cu32 w] [cu32 x, cu32 y, cu32 z] rfl] at qSc
    have qY := seqM_some qSc rfl (pexecM_skip mv fu (gS P [cu32 x, cu32 y, cu32 z]) vv)
    have qB := pexecM_branch_true mv fu _ _ Sk _ vv 1 hge (by decide) _ qY
    have hxy : x < y := by omega
    have hzv : z = x + m - y := by omega
    have hmod : (x + m - y) % m = x + m - y := Nat.mod_eq_of_lt (by omega)
    have kr : ([cu32 x, cu32 y, cu32 z] : List Cell)[2]? = some (cu32 z) := rfl
    have qR := ret_var mv hnv fu P _ vv 2 z kr hzlt
    have qT := seqM_some qB rfl qR
    have p0 := seqM_some q2 rfl qT
    have p1 := seqM_some q1 rfl p0
    refine ⟨_, p1, ?_⟩
    simp [hmod, hzv, vwp, NExpr.scalarOnly, NExpr.nodes, gS_mem_len, gS_bs_len]
  · rw [if_neg hc] at hge
    have hxy : y ≤ x := by omega
    have hwv : w = x - y := by omega
    have hmod : (x + m - y) % m = x - y := by
      have : x + m - y = (x - y) + m := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have qB := pexecM_branch_false mv fu _ (.sequence (.scope (.sequence (.primitive (.assign 2 u32
      (.binary u32 .add (.variable u32 2) (.literal u32 (m : Int))))) Sk)) Sk) Sk
      (gS P [cu32 x, cu32 y, cu32 w]) vv hge _ (pexecM_skip mv fu (gS P [cu32 x, cu32 y, cu32 w]) vv)
    have qR := ret_var mv hnv fu P _ vv 2 w k2 hwlt
    have qT := seqM_some qB rfl qR
    have p0 := seqM_some q2 rfl qT
    have p1 := seqM_some q1 rfl p0
    refine ⟨_, p1, ?_⟩
    simp [hmod, hwv, vwp, NExpr.scalarOnly, NExpr.nodes, gS_mem_len, gS_bs_len]


theorem prepare_op2 (caller : NState) (params : List CppVectorBindings.Parameter)
    (hp : params = [.scalar u32 false true, .scalar u32 false true]) (e1 e2 : NExpr) (v1 v2 : Int)
    (h1 : e1.scalarOnly = true) (h2 : e2.scalarOnly = true) (t1ty : e1.resultType = u32) (t2ty : e2.resultType = u32)
    (d1 : e1.denote (envOf caller) = some v1) (d2 : e2.denote (envOf caller) = some v2)
    (valid : caller.frame.state.wellFormed = true) (n1 : u32.valid v1 = true) (n2 : u32.valid v2 = true) :
    ∃ t1 t2, Good caller t1 e1.nodes e1.nodes ∧ Good t1 t2 e2.nodes e2.nodes ∧
      ∃ Sinit, prepare caller params [.value e1,.value e2] = some Sinit ∧
        Sinit.slots = [.scalar 0,.scalar 1] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨u32,v1⟩,⟨u32,v2⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
        Sinit.scalars.work = t2.scalars.work+3 ∧ t2.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨t1,ran1,g1⟩ := scalar_eval e1 caller v1 h1 d1
  obtain ⟨t2,ran2,g2⟩ := scalar_eval e2 t1 v2 h2 (by rw [envOf_core g1.1]; exact d2)
  refine ⟨t1,t2,g1,g2,?_⟩
  have frameT : t2.frame = caller.frame := by rw [g2.1.1,g1.1.1]
  have fs : t2.frame.state = caller.frame.state := by rw [frameT]
  have fr : t2.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t2.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t2.scalars.memory = caller.scalars.memory := by
    have a := g2.1.2.2.2.1; have b := g1.1.2.2.2.1; rw [a,b]
  have hbind : t2.scalars.bindings = caller.scalars.bindings := by
    have a := g2.1.2.2.2.2.1; have b := g1.1.2.2.2.2.1; rw [a,b]
  have hbase : t2.scalars.baseMemory = caller.scalars.baseMemory := by
    have a := g2.1.2.2.2.2.2; have b := g1.1.2.2.2.2.2; rw [a,b]
  have res1 : resolve caller (.scalar u32 false true) (.value e1) = some (t1,.scalar u32 true v1) := by
    simp [resolve,t1ty,ran1]
  have res2 : resolve t1 (.scalar u32 false true) (.value e2) = some (t2,.scalar u32 true v2) := by
    simp [resolve,t2ty,ran2]
  rw [hp]
  simp [prepare,valid,resolveAll,res1,res2]
  simp [fs,fr,fb,hmem,hbind,hbase,bindAll,bindOne,CppState.bindArgument,n1,n2,callerP,
    NState.observe,CppState.State.observe]
  omega


def bbOp : Nat → Buffer Value := fun _ => ⟨0, [], 0, 0, 0⟩

theorem fwOp_init (caller : NState) (L0 T0 sc N : Nat) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (hL : L0 = caller.frame.state.liveSpace) (hT : T0 = caller.frame.state.storage.work)
    (hs : sc = caller.scope + 1) (hN : N = caller.frame.state.storage.objects.length) :
    FWM (mvOp L0 T0 sc N) (fun _ => []) bbOp 0
      (⟨caller.frame.state, caller.frame.rootWritable, []⟩ : Frame) := by
  subst hL hT hs hN
  refine ⟨valid, lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := strict owner k h
    show k < caller.scope + 1
    omega
  all_goals (intro k hk; exact absurd hk (by simp [mvOp]))

set_option maxHeartbeats 4000000 in
theorem op_call (prog : NProgram) (body : Command) (hbody : prog.body = body)
    (hpar : prog.parameters = [.scalar u32 false true, .scalar u32 false true])
    (hres : prog.result = ResultKind.scalar u32) (hwr : WrM (fun _ => false) body = true) (x y rv : Nat)
    (hrv : rv < 4294967296) (hx : x < 4294967296) (hy : y < 4294967296)
    (exec : ∀ (mv : MV) (_ : mv.nv = 0) (fu : Nat) (P : List Cell) (vv : Nat → List Int),
      ∃ r : PRM, pexecM mv fu body (gS P [cu32 x, cu32 y]) vv = some r ∧ r.ret = some (rv : Int) ∧
        r.ps = gS P [cu32 x, cu32 y, cu32 rv, cu32 rv] ∧ r.vv = vv ∧ r.cost ≤ 60 ∧ r.need ≤ P.length + 30 ∧ r.wk = 0)
    (caller : NState) (e1 e2 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ty1 : e1.resultType = u32) (ty2 : e2.resultType = u32)
    (d1 : e1.denote (envOf caller) = some (x : Int)) (d2 : e2.denote (envOf caller) = some (y : Int))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller prog.parameters [.value e1,.value e2] = some Sinit ∧
      prog.callFuel fuel caller [.value e1,.value e2] = .finished (res,.scalar (rv : Int)) ∧
      ScalarPostM (mvOp caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length) caller Sinit res (e1.nodes + e2.nodes) 80 caller.scalars.memory 0
        (fun _ => []) := by
  obtain ⟨t1,t2,g1,g2,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT⟩ :=
    prepare_op2 caller prog.parameters hpar e1 e2 (x : Int) (y : Int) hs1 hs2 ty1 ty2 d1 d2 valid
      (u32_valid_nat x hx) (u32_valid_nat y hy)
  have fwS := fwOp_init caller _ _ _ _ valid lengths strict rfl rfl rfl rfl
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrps,hrvv,hcost,hneed,hwk⟩ :=
    exec (mvOp caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
      caller.frame.state.storage.objects.length) rfl 1 (callerP caller) (fun _ => [])
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have gw1 := g1.2.2.1
  have gw2 := g2.2.2.1
  have spC : caller.scalars.peak ≤ Sinit.scalars.peak := by
    have a1 := g1.2.2.2.2.1; have a2 := g2.2.2.2.2.1
    omega
  have hmk : (⟨callerP caller ++ [(⟨u32,(x : Int)⟩ : Cell),⟨u32,(y : Int)⟩],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]⟩ : PS) = gS (callerP caller) [cu32 x, cu32 y] := by
    simp [gS, List.range_succ]
  have hpost := call_vecm (mvOp caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length) (fun _ => false)
    (by intro k hk; simp at hk)
    caller prog [.value e1,.value e2] Sinit
    (callerP caller ++ [(⟨u32,(x : Int)⟩ : Cell),⟨u32,(y : Int)⟩])
    [(⟨(callerP caller).length,true⟩ : CppState.Binding),⟨(callerP caller).length+1,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    spC (by simp [hlenP]; omega) (by simp [callerP, List.take_append_of_le_length]) base
    (by rw [hbody]; exact hwr) 1 rr (by rw [hmk, hbody]; exact hexec) (rv : Int) hret u32 hres
    (u32_valid_nat rv hrv) (by omega) (by simp [hlenP]) (e1.nodes + e2.nodes) 80 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv, hwk] at post
  exact post


theorem wr_add (m : Nat) : WrM (fun _ => false) (addBody m) = true := by simp [WrM]
theorem wr_sub (m : Nat) : WrM (fun _ => false) (subBody m) = true := by simp [WrM]
theorem wr_mul (m : Nat) : WrM (fun _ => false) (mulBody m) = true := by simp [WrM]

/-- `sum` of two `ModInt<m>` values (`2 <= m <= 2^31`, both operands in `[0, m)`) for any `prog` whose body is the
generated one: the result is the residue of the sum modulo `m`. -/
theorem operator_add_correct (prog : NProgram) (m : Nat) (hbody : prog.body = addBody m)
    (hpar : prog.parameters = [.scalar u32 false true, .scalar u32 false true])
    (hres : prog.result = ResultKind.scalar u32) (hm : 2 ≤ m) (hm2 : m ≤ 2147483648) (x y : Nat) (hx : x < m) (hy : y < m)
    (caller : NState) (e1 e2 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ty1 : e1.resultType = u32) (ty2 : e2.resultType = u32)
    (d1 : e1.denote (envOf caller) = some (x : Int)) (d2 : e2.denote (envOf caller) = some (y : Int))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller prog.parameters [.value e1,.value e2] = some Sinit ∧
      prog.callFuel fuel caller [.value e1,.value e2] = .finished (res,.scalar (((x + y) % m : Nat) : Int)) ∧
      ScalarPostM (mvOp caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length) caller Sinit res (e1.nodes + e2.nodes) 80 caller.scalars.memory 0
        (fun _ => []) :=
  op_call prog (addBody m) hbody hpar hres (wr_add m) x y ((x + y) % m) (by have := Nat.mod_lt (x + y) (show 0 < m by omega); omega) (by omega) (by omega)
    (fun mv hnv fu P vv => add_exec mv hnv fu P vv m x y hm hm2 hx hy) caller e1 e2 hs1 hs2 ty1 ty2 d1 d2 valid lengths
    strict base

/-- `difference` of two `ModInt<m>` values (`2 <= m <= 2^31`, both operands in `[0, m)`) for any `prog` whose body is the
generated one: the result is the residue of the difference modulo `m`. -/
theorem operator_sub_correct (prog : NProgram) (m : Nat) (hbody : prog.body = subBody m)
    (hpar : prog.parameters = [.scalar u32 false true, .scalar u32 false true])
    (hres : prog.result = ResultKind.scalar u32) (hm : 2 ≤ m) (hm2 : m ≤ 2147483648) (x y : Nat) (hx : x < m) (hy : y < m)
    (caller : NState) (e1 e2 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ty1 : e1.resultType = u32) (ty2 : e2.resultType = u32)
    (d1 : e1.denote (envOf caller) = some (x : Int)) (d2 : e2.denote (envOf caller) = some (y : Int))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller prog.parameters [.value e1,.value e2] = some Sinit ∧
      prog.callFuel fuel caller [.value e1,.value e2] = .finished (res,.scalar (((x + m - y) % m : Nat) : Int)) ∧
      ScalarPostM (mvOp caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length) caller Sinit res (e1.nodes + e2.nodes) 80 caller.scalars.memory 0
        (fun _ => []) :=
  op_call prog (subBody m) hbody hpar hres (wr_sub m) x y ((x + m - y) % m) (by have := Nat.mod_lt (x + m - y) (show 0 < m by omega); omega) (by omega) (by omega)
    (fun mv hnv fu P vv => sub_exec mv hnv fu P vv m x y hm hm2 hx hy) caller e1 e2 hs1 hs2 ty1 ty2 d1 d2 valid lengths
    strict base

/-- `product` of two `ModInt<m>` values (`2 <= m <= 2^31`, both operands in `[0, m)`) for any `prog` whose body is the
generated one: the result is the residue of the product modulo `m`. -/
theorem operator_mul_correct (prog : NProgram) (m : Nat) (hbody : prog.body = mulBody m)
    (hpar : prog.parameters = [.scalar u32 false true, .scalar u32 false true])
    (hres : prog.result = ResultKind.scalar u32) (hm : 2 ≤ m) (hm2 : m ≤ 2147483648) (x y : Nat) (hx : x < m) (hy : y < m)
    (caller : NState) (e1 e2 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ty1 : e1.resultType = u32) (ty2 : e2.resultType = u32)
    (d1 : e1.denote (envOf caller) = some (x : Int)) (d2 : e2.denote (envOf caller) = some (y : Int))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller prog.parameters [.value e1,.value e2] = some Sinit ∧
      prog.callFuel fuel caller [.value e1,.value e2] = .finished (res,.scalar ((x * y % m : Nat) : Int)) ∧
      ScalarPostM (mvOp caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length) caller Sinit res (e1.nodes + e2.nodes) 80 caller.scalars.memory 0
        (fun _ => []) :=
  op_call prog (mulBody m) hbody hpar hres (wr_mul m) x y (x * y % m) (by have := Nat.mod_lt (x * y) (show 0 < m by omega); omega) (by omega) (by omega)
    (fun mv hnv fu P vv => mul_exec mv hnv fu P vv m x y hm hm2 hx hy) caller e1 e2 hs1 hs2 ty1 ty2 d1 d2 valid lengths
    strict base


/-- `sum` of two `ModInt<998244353>` values: `operator+` on operands in `[0, 998244353)` gives the residue of the sum
modulo `998244353`. -/
theorem operator_add_ModInt_998244353U_correct (x y : Nat) (hx : x < 998244353) (hy : y < 998244353)
    (caller : NState) (e1 e2 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ty1 : e1.resultType = u32) (ty2 : e2.resultType = u32)
    (d1 : e1.denote (envOf caller) = some (x : Int)) (d2 : e2.denote (envOf caller) = some (y : Int))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.ModIntInstance.operator_add_ModInt_998244353U.parameters [.value e1,.value e2] = some Sinit ∧
      Proofs.ModIntInstance.operator_add_ModInt_998244353U.callFuel fuel caller [.value e1,.value e2] =
        .finished (res,.scalar (((x + y) % 998244353 : Nat) : Int)) ∧
      ScalarPostM (mvOp caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length) caller Sinit res (e1.nodes + e2.nodes) 80 caller.scalars.memory 0
        (fun _ => []) :=
  operator_add_correct _ 998244353 rfl rfl rfl (by omega) (by omega) x y hx hy caller e1 e2 hs1 hs2 ty1 ty2 d1 d2
    valid lengths strict base

/-- `difference` of two `ModInt<998244353>` values: `operator-` on operands in `[0, 998244353)` gives the residue of the difference
modulo `998244353`. -/
theorem operator_sub_ModInt_998244353U_correct (x y : Nat) (hx : x < 998244353) (hy : y < 998244353)
    (caller : NState) (e1 e2 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ty1 : e1.resultType = u32) (ty2 : e2.resultType = u32)
    (d1 : e1.denote (envOf caller) = some (x : Int)) (d2 : e2.denote (envOf caller) = some (y : Int))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.ModIntInstance.operator_sub_ModInt_998244353U.parameters [.value e1,.value e2] = some Sinit ∧
      Proofs.ModIntInstance.operator_sub_ModInt_998244353U.callFuel fuel caller [.value e1,.value e2] =
        .finished (res,.scalar (((x + 998244353 - y) % 998244353 : Nat) : Int)) ∧
      ScalarPostM (mvOp caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length) caller Sinit res (e1.nodes + e2.nodes) 80 caller.scalars.memory 0
        (fun _ => []) :=
  operator_sub_correct _ 998244353 rfl rfl rfl (by omega) (by omega) x y hx hy caller e1 e2 hs1 hs2 ty1 ty2 d1 d2
    valid lengths strict base

/-- `product` of two `ModInt<998244353>` values: `operator*` on operands in `[0, 998244353)` gives the residue of the product
modulo `998244353`. -/
theorem operator_mul_ModInt_998244353U_correct (x y : Nat) (hx : x < 998244353) (hy : y < 998244353)
    (caller : NState) (e1 e2 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ty1 : e1.resultType = u32) (ty2 : e2.resultType = u32)
    (d1 : e1.denote (envOf caller) = some (x : Int)) (d2 : e2.denote (envOf caller) = some (y : Int))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.ModIntInstance.operator_mul_ModInt_998244353U.parameters [.value e1,.value e2] = some Sinit ∧
      Proofs.ModIntInstance.operator_mul_ModInt_998244353U.callFuel fuel caller [.value e1,.value e2] =
        .finished (res,.scalar ((x * y % 998244353 : Nat) : Int)) ∧
      ScalarPostM (mvOp caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length) caller Sinit res (e1.nodes + e2.nodes) 80 caller.scalars.memory 0
        (fun _ => []) :=
  operator_mul_correct _ 998244353 rfl rfl rfl (by omega) (by omega) x y hx hy caller e1 e2 hs1 hs2 ty1 ty2 d1 d2
    valid lengths strict base

/-- `sum` of two `ModInt<1000000007>` values: `operator+` on operands in `[0, 1000000007)` gives the residue of the sum
modulo `1000000007`. -/
theorem operator_add_ModInt_1000000007U_correct (x y : Nat) (hx : x < 1000000007) (hy : y < 1000000007)
    (caller : NState) (e1 e2 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ty1 : e1.resultType = u32) (ty2 : e2.resultType = u32)
    (d1 : e1.denote (envOf caller) = some (x : Int)) (d2 : e2.denote (envOf caller) = some (y : Int))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.ModIntInstance.operator_add_ModInt_1000000007U.parameters [.value e1,.value e2] = some Sinit ∧
      Proofs.ModIntInstance.operator_add_ModInt_1000000007U.callFuel fuel caller [.value e1,.value e2] =
        .finished (res,.scalar (((x + y) % 1000000007 : Nat) : Int)) ∧
      ScalarPostM (mvOp caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length) caller Sinit res (e1.nodes + e2.nodes) 80 caller.scalars.memory 0
        (fun _ => []) :=
  operator_add_correct _ 1000000007 rfl rfl rfl (by omega) (by omega) x y hx hy caller e1 e2 hs1 hs2 ty1 ty2 d1 d2
    valid lengths strict base

/-- `difference` of two `ModInt<1000000007>` values: `operator-` on operands in `[0, 1000000007)` gives the residue of the difference
modulo `1000000007`. -/
theorem operator_sub_ModInt_1000000007U_correct (x y : Nat) (hx : x < 1000000007) (hy : y < 1000000007)
    (caller : NState) (e1 e2 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ty1 : e1.resultType = u32) (ty2 : e2.resultType = u32)
    (d1 : e1.denote (envOf caller) = some (x : Int)) (d2 : e2.denote (envOf caller) = some (y : Int))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.ModIntInstance.operator_sub_ModInt_1000000007U.parameters [.value e1,.value e2] = some Sinit ∧
      Proofs.ModIntInstance.operator_sub_ModInt_1000000007U.callFuel fuel caller [.value e1,.value e2] =
        .finished (res,.scalar (((x + 1000000007 - y) % 1000000007 : Nat) : Int)) ∧
      ScalarPostM (mvOp caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length) caller Sinit res (e1.nodes + e2.nodes) 80 caller.scalars.memory 0
        (fun _ => []) :=
  operator_sub_correct _ 1000000007 rfl rfl rfl (by omega) (by omega) x y hx hy caller e1 e2 hs1 hs2 ty1 ty2 d1 d2
    valid lengths strict base

/-- `product` of two `ModInt<1000000007>` values: `operator*` on operands in `[0, 1000000007)` gives the residue of the product
modulo `1000000007`. -/
theorem operator_mul_ModInt_1000000007U_correct (x y : Nat) (hx : x < 1000000007) (hy : y < 1000000007)
    (caller : NState) (e1 e2 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ty1 : e1.resultType = u32) (ty2 : e2.resultType = u32)
    (d1 : e1.denote (envOf caller) = some (x : Int)) (d2 : e2.denote (envOf caller) = some (y : Int))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.ModIntInstance.operator_mul_ModInt_1000000007U.parameters [.value e1,.value e2] = some Sinit ∧
      Proofs.ModIntInstance.operator_mul_ModInt_1000000007U.callFuel fuel caller [.value e1,.value e2] =
        .finished (res,.scalar ((x * y % 1000000007 : Nat) : Int)) ∧
      ScalarPostM (mvOp caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length) caller Sinit res (e1.nodes + e2.nodes) 80 caller.scalars.memory 0
        (fun _ => []) :=
  operator_mul_correct _ 1000000007 rfl rfl rfl (by omega) (by omega) x y hx hy caller e1 e2 hs1 hs2 ty1 ty2 d1 d2
    valid lengths strict base


theorem prep_val_ref (caller : NState) (params : List CppVectorBindings.Parameter)
    (hp : params = [.scalar u32 false true, .scalar u32 true false]) (e : NExpr) (v : Int) (sb : Nat)
    (bb : CppState.Binding) (vb : Int) (cb : caller.scalarCell sb u32 = some (bb,⟨u32,vb⟩))
    (hs : e.scalarOnly = true) (hty : e.resultType = u32) (d : e.denote (envOf caller) = some v)
    (valid : caller.frame.state.wellFormed = true) (nv : u32.valid v = true) :
    ∃ t, Good caller t e.nodes e.nodes ∧
      ∃ Sinit, prepare caller params [.value e,.scalarReference sb] = some Sinit ∧
        Sinit.slots = [.scalar 0,.scalar 1] ∧ Sinit.scalars.memory = callerP caller ++ [⟨u32,v⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨bb.address,false⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
        Sinit.scalars.work = t.scalars.work+4 ∧ t.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ t.scalars.peak := by
  obtain ⟨t,ran,good⟩ := scalar_eval e caller v hs d
  refine ⟨t,good,?_⟩
  obtain ⟨ib,hslot,hbind,hmb,_,vvb⟩ := scalarCell_facts cb
  have ltb : bb.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hmb).1
  have frameT : t.frame = caller.frame := good.1.1
  have fs : t.frame.state = caller.frame.state := by rw [frameT]
  have fr : t.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t.scalars.memory = caller.scalars.memory := good.1.2.2.2.1
  have hbindT : t.scalars.bindings = caller.scalars.bindings := good.1.2.2.2.2.1
  have hbase : t.scalars.baseMemory = caller.scalars.baseMemory := good.1.2.2.2.2.2
  have res1 : resolve caller (.scalar u32 false true) (.value e) = some (t,.scalar u32 true v) := by
    simp [resolve,hty,ran]
  have cbT : t.scalarCell sb u32 = some (bb,⟨u32,vb⟩) := by
    have hsl : t.slots = caller.slots := good.1.2.1
    unfold NState.scalarCell NState.scalarSlot at cb ⊢
    rw [hsl, hbindT, hmem]
    exact cb
  have res2 : resolve t (.scalar u32 true false) (.scalarReference sb) =
      some (t.charge 1 1,.scalarAddress u32 bb.address false) := by simp [resolve,cbT]
  rw [hp]
  simp [prepare,valid,resolveAll,res1,res2]
  have hma' : (t.scalars.memory ++ List.replicate (t.scalars.bindings.length + caller.frame.bindings.length)
      (⟨bl,0⟩ : Cell))[bb.address]? = some ⟨u32,vb⟩ := by
    rw [hmem, List.getElem?_append_left ltb]; exact hmb
  have hma2 : (caller.scalars.memory ++ (List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
      (⟨bl,0⟩ : Cell) ++ [(⟨u32,v⟩ : Cell)]))[bb.address]? = some ⟨u32,vb⟩ := by
    rw [List.getElem?_append_left ltb]; exact hmb
  simp [fs,fr,fb,hmem,hbindT,hbase,bindAll,bindOne,CppState.bindArgument,nv,callerP,NState.observe,
    CppState.State.observe,hma',hma2,vvb]
  have h1 := good.2.2.2.2.1
  refine ⟨by simp [NState.charge, NState.observe, CppState.State.observe], Or.inl (by simp [NState.charge, NState.observe, CppState.State.observe]), h1⟩

set_option maxHeartbeats 4000000 in
/-- `a / b` of two `ModInt<m>` (`a` passed by value, `b` by reference): the result is `x * y^(m-2) % m` (the quotient when
`m` is prime), for `x, y < m` and `y != 0`. -/
theorem operator_div_correct (prog : NProgram) (m : Nat) (hbody : prog.body = Proofs.ModIntDiv.divBody m 2)
    (hpar : prog.parameters = [.scalar u32 false true, .scalar u32 true false])
    (hres : prog.result = ResultKind.scalar u32) (hm : 2 ≤ m) (hm2 : m < 4294967296) (x y : Nat) (hx : x < m) (hy : y < m)
    (hy0 : y ≠ 0) (caller : NState) (e : NExpr) (sb : Nat) (bb : CppState.Binding)
    (cb : caller.scalarCell sb u32 = some (bb,⟨u32,(y : Int)⟩)) (hs : e.scalarOnly = true) (hty : e.resultType = u32)
    (d : e.denote (envOf caller) = some (x : Int))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.value e,.scalarReference sb] = some Sinit ∧
      prog.callFuel fuel caller [.value e,.scalarReference sb] =
        .finished (res,.scalar ((x * ((y ^ (m - 2)) % m) % m : Nat) : Int)) ∧
      ScalarPost2 caller Sinit res e.nodes 5400 caller.scalars.memory := by
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,spC⟩ :=
    prep_val_ref caller prog.parameters hpar e (x : Int) sb bb (y : Int) cb hs hty d valid (u32_valid_nat x (by omega))
  obtain ⟨ib,_,_,hmb,_,_⟩ := scalarCell_facts cb
  have ltb : bb.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hmb).1
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have hPy0 : (callerP caller)[bb.address]? = some ⟨u32,(y : Int)⟩ := by
    simp only [callerP]; rw [List.getElem?_append_left ltb]; exact hmb
  have hlty0 : bb.address < (callerP caller).length := by omega
  have hPx : (callerP caller ++ [(⟨u32,(x : Int)⟩ : Cell)])[(callerP caller).length]? = some ⟨u32,(x : Int)⟩ := by
    simp
  have hPy : (callerP caller ++ [(⟨u32,(x : Int)⟩ : Cell)])[bb.address]? = some ⟨u32,(y : Int)⟩ := by
    rw [List.getElem?_append_left hlty0]; exact hPy0
  obtain ⟨r,L2,hexec,hret,hcost,hneed,hrps⟩ :=
    Proofs.ModIntDiv.div_exec_copies 2 (by decide) m hm hm2 (callerP caller ++ [(⟨u32,(x : Int)⟩ : Cell)]) (callerP caller).length bb.address x y
      hx hy hy0 hPx hPy (by simp) (by simp; omega)
  simp only [List.length_append, List.length_singleton] at hneed
  have hrl : (x * ((y ^ (m - 2)) % m) % m) < 4294967296 := by
    have := Nat.mod_lt (x * ((y ^ (m - 2)) % m)) (show 0 < m by omega); omega
  have takeM : (callerP caller ++ [(⟨u32,(x : Int)⟩ : Cell)]).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left' rfl
  have hpost := call_scalar caller prog [.value e,.scalarReference sb] Sinit
    (callerP caller ++ [(⟨u32,(x : Int)⟩ : Cell)]) [⟨(callerP caller).length,true⟩,⟨bb.address,false⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame (by omega)
    (by simp [hlen]; omega) (by rw [takeM]) valid lengths strict base (by rw [hbody]; rfl) 70 r
    (by rw [hbody]; exact hexec) _ hret u32 hres (u32_valid_nat _ hrl) (by simp [hlen]; omega) (by simp [hlen])
    e.nodes 5400 (by
      have a1 := good.2.2.1
      omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    have hset : (callerP caller ++ [(⟨u32,(x : Int)⟩ : Cell)]).set (callerP caller).length
        (⟨u32,((x * ((y ^ (m - 2)) % m) % m : Nat) : Int)⟩ : Cell) =
        callerP caller ++ [(⟨u32,((x * ((y ^ (m - 2)) % m) % m : Nat) : Int)⟩ : Cell)] := by
      rw [List.set_append_right _ _ (Nat.le_refl _)]
      simp
    rw [hset]
    simp only [callerP, List.append_assoc]
    exact List.take_left' rfl
  rw [hs'] at post
  exact post

/-- `a / b` of two `ModInt<998244353>`: `operator/` with `a = x` (by value) and `b = y` (by reference), `x, y < 998244353`, `y != 0`,
gives `x * y^(998244353 - 2) % 998244353` (the quotient, since 998244353 is prime). -/
theorem operator_div_ModInt_998244353U_correct (x y : Nat) (hx : x < 998244353) (hy : y < 998244353) (hy0 : y ≠ 0)
    (caller : NState) (e : NExpr) (sb : Nat) (bb : CppState.Binding)
    (cb : caller.scalarCell sb u32 = some (bb,⟨u32,(y : Int)⟩)) (hs : e.scalarOnly = true) (hty : e.resultType = u32)
    (d : e.denote (envOf caller) = some (x : Int))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.ModIntInstance.operator_div_ModInt_998244353U.parameters
        [.value e,.scalarReference sb] = some Sinit ∧
      Proofs.ModIntInstance.operator_div_ModInt_998244353U.callFuel fuel caller [.value e,.scalarReference sb] =
        .finished (res,.scalar ((x * ((y ^ (998244353 - 2)) % 998244353) % 998244353 : Nat) : Int)) ∧
      ScalarPost2 caller Sinit res e.nodes 5400 caller.scalars.memory :=
  operator_div_correct Proofs.ModIntInstance.operator_div_ModInt_998244353U 998244353 rfl rfl rfl (by omega) (by omega) x y hx hy hy0 caller e sb bb cb hs hty d valid lengths strict
    base

/-- `a / b` of two `ModInt<1000000007>`: `operator/` with `a = x` (by value) and `b = y` (by reference), `x, y < 1000000007`, `y != 0`,
gives `x * y^(1000000007 - 2) % 1000000007` (the quotient, since 1000000007 is prime). -/
theorem operator_div_ModInt_1000000007U_correct (x y : Nat) (hx : x < 1000000007) (hy : y < 1000000007) (hy0 : y ≠ 0)
    (caller : NState) (e : NExpr) (sb : Nat) (bb : CppState.Binding)
    (cb : caller.scalarCell sb u32 = some (bb,⟨u32,(y : Int)⟩)) (hs : e.scalarOnly = true) (hty : e.resultType = u32)
    (d : e.denote (envOf caller) = some (x : Int))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.ModIntInstance.operator_div_ModInt_1000000007U.parameters
        [.value e,.scalarReference sb] = some Sinit ∧
      Proofs.ModIntInstance.operator_div_ModInt_1000000007U.callFuel fuel caller [.value e,.scalarReference sb] =
        .finished (res,.scalar ((x * ((y ^ (1000000007 - 2)) % 1000000007) % 1000000007 : Nat) : Int)) ∧
      ScalarPost2 caller Sinit res e.nodes 5400 caller.scalars.memory :=
  operator_div_correct Proofs.ModIntInstance.operator_div_ModInt_1000000007U 1000000007 rfl rfl rfl (by omega) (by omega) x y hx hy hy0 caller e sb bb cb hs hty d valid lengths strict
    base

end Proofs.ModIntOps
