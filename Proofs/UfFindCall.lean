import Proofs.UfSameCall
import Proofs.Generated.UnionFind

namespace Proofs.UfFindCall
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

-- Determinism of the parent function: two nodes reachable from `a` are comparable.
theorem reach_det (ps : List Int) (a : Nat) : ∀ (v c : Nat), Reach ps a v → Reach ps a c → Reach ps v c ∨ Reach ps c v := by
  intro v c hv
  induction hv generalizing c with
  | refl => intro hc; exact Or.inl hc
  | step a' b' c' hp hr ih =>
    intro hc
    cases hc with
    | refl => exact Or.inr (Reach.step _ _ _ hp hr)
    | step _ b'' _ hp2 hr2 =>
      have : b'' = b' := by
        have h1 : ps[a']? = some (b' : Int) := hp
        have h2 : ps[a']? = some (b'' : Int) := hp2
        rw [h1] at h2; have := Option.some.inj h2; omega
      subst this
      exact ih _ hr2

theorem reach_trans (ps : List Int) : ∀ (a b c : Nat), Reach ps a b → Reach ps b c → Reach ps a c := by
  intro a b c h
  induction h with
  | refl => exact id
  | step a' b' c' hp hr ih => intro h2; exact Reach.step _ _ _ hp (ih h2)

-- Reachability lowers the rank.
theorem reach_rank (ps : List Int) (rank : Nat → Nat) (hF : Forest ps rank) :
    ∀ (a v : Nat), Reach ps a v → rank v ≤ rank a := by
  intro a v h
  induction h with
  | refl => exact Nat.le_refl _
  | step a' b' c' hp hr ih =>
    have h1 : ps[a']? = some (b' : Int) := hp
    have := hF.decrease a' (b' : Int) h1 (by omega)
    simp at this
    omega

theorem reach_rank_lt (ps : List Int) (rank : Nat → Nat) (hF : Forest ps rank) :
    ∀ (a v : Nat), Reach ps a v → a ≠ v → rank v < rank a := by
  intro a v h
  cases h with
  | refl => intro hne; exact absurd rfl hne
  | step _ b' _ hp hr =>
    intro _
    have h1 : ps[a]? = some (b' : Int) := hp
    have := hF.decrease a (b' : Int) h1 (by omega)
    simp at this
    have := reach_rank ps rank hF b' v hr
    omega

-- A root reaches only itself.
theorem root_reach (ps : List Int) (r : Nat) (hr : ∃ v, ps[r]? = some v ∧ v < 0) : ∀ v, Reach ps r v → v = r := by
  intro v h
  cases h with
  | refl => rfl
  | step _ b' _ hp _ =>
    obtain ⟨w, hw, hneg⟩ := hr
    have h1 : ps[r]? = some (b' : Int) := hp
    rw [hw] at h1
    have := Option.some.inj h1
    omega


abbrev loopBody2 : Command :=
  .sequence (.scope (.sequence (.primitive (.declare i32 true (rdK 0)))
    (.sequence (.primitive (.write (.local 0) i32 (.cast u64 (.variable i32 1)) (.variable i32 2)))
      (.sequence (.primitive (.assign 1 i32 (.variable i32 3))) Sk)))) Sk
abbrev cond2 : NExpr := .binary bT .ne (.variable i32 1) (.variable i32 2)
abbrev loop2 : Command := .whileLoop cond2 loopBody2
abbrev bodyF : Command :=
  .sequence (.primitive (.declare i32 true (.variable i32 1))) (.sequence (loopCK 1)
    (.sequence loop2 (.sequence (.primitive (.ret (.variable i32 2))) Sk)))

theorem body_eqF : Proofs.UnionFindInstance.UnionFind_root.body = UfBounds.bounds 1 bodyF := rfl

theorem scope_pop (ps0 : PS) (ad0 : Nat) (x y : Int) (l0 : ad0 < ps0.mem.length) :
    (⟨(setP (appI ps0 y) ad0 x).mem.take ps0.mem.length, (setP (appI ps0 y) ad0 x).bs.take ps0.bs.length⟩ : PS) =
      setP ps0 ad0 x := by
  obtain ⟨mem,bs⟩ := ps0
  simp only [setP, appI] at *
  simp only [PS.mk.injEq]
  constructor
  · apply List.ext_getElem?
    intro i
    simp only [List.getElem?_take, List.getElem?_set, List.length_set, List.length_append, List.getElem?_append]
    by_cases h1 : ad0 = i <;> by_cases h3 : i < mem.length <;> simp_all <;> omega
  · simp [List.take_append_of_le_length]

theorem iter2 (ps0 : PS) (vec : List Int) (ad0 ad1 cur r : Nat) (nxt : Int) (h0 : Loc ps0 0 ad0 cur)
    (h1 : Loc ps0 1 ad1 r) (hbs : ps0.bs.length = 2) (hcl : cur < vec.length) (hn : vec.length < 2147483648)
    (hv : vec[cur]? = some nxt) (gn : i32.valid nxt = true) (hr : r < 2147483648) (fu : Nat) :
    ∃ r1, pexecW i32 fu loopBody2 ps0 vec = some r1 ∧ r1.ps = setP ps0 ad0 nxt ∧ r1.vec = vec.set cur (r : Int) ∧
      r1.ret = none ∧ r1.cost ≤ 60 ∧ r1.need ≤ ps0.mem.length + ps0.bs.length + 40 ∧ r1.wk = 1 := by
  have hcv : i32.valid (cur : Int) = true := i32_valid cur (by omega) (by omega)
  have hrv : i32.valid (r : Int) = true := i32_valid r (by omega) (by omega)
  have l0 : ad0 < ps0.mem.length := (List.getElem?_eq_some_iff.mp h0.2).1
  -- declare next := vec[cur]
  have hval := rdK_val vec ps0 0 ad0 cur h0 hn hcl nxt hv gn
  have d1 := pstmtW_declare_ok i32 ps0 vec i32 true (rdK 0) nxt hval nxt (conv_signed i32 rfl rfl _ gn)
  have d1' := (pexecW_prim i32 fu (.declare i32 true (rdK 0)) _ _).trans d1
  -- write vec[cur] := r
  have L0 := loc_app_old ps0 0 ad0 (cur : Int) nxt h0
  have L1 := loc_app_old ps0 1 ad1 (r : Int) nxt h1
  have L2 : Loc (appI ps0 nxt) 2 ps0.mem.length nxt := by
    have := loc_app_new ps0 nxt
    rw [hbs] at this; exact this
  have hp : vdenL i32 vec (penv1 (appI ps0 nxt)) (NExpr.cast u64 (.variable i32 1)) = some (cur : Int) := by
    rw [vdenL_scalar _ _ _ _ rfl]; exact idxK (appI ps0 nxt) 0 ad0 cur L0 (by omega)
  have hx : vdenL i32 vec (penv1 (appI ps0 nxt)) (NExpr.variable i32 2) = some (r : Int) := by
    rw [vdenL_scalar _ _ _ _ rfl, den_variable]; exact env_loc _ 1 ad1 r L1 hrv
  have w := pstmtW_write_ok i32 (appI ps0 nxt) vec (NExpr.cast u64 (.variable i32 1)) (NExpr.variable i32 2) (r : Int) cur
    hx hp hcl hrv
  have a1 := (pexecW_prim i32 fu _ _ _).trans w
  -- assign cur := next
  obtain ⟨hb0, hm0⟩ := L0
  have hn3 : vdenL i32 (vec.set cur (r : Int)) (penv1 (appI ps0 nxt)) (NExpr.variable i32 3) = some nxt := by
    rw [vdenL_scalar _ _ _ _ rfl, den_variable]; exact env_loc _ 2 _ nxt L2 gn
  have s3 := pstmtW_assign_ok i32 (appI ps0 nxt) (vec.set cur (r : Int)) 0 i32 (.variable i32 3) nxt hn3
    ⟨ad0,true⟩ ⟨i32,(cur : Int)⟩ hb0 hm0 rfl hcv rfl nxt (conv_signed i32 rfl rfl _ gn)
  have a3 := (pexecW_prim i32 fu _ _ _).trans s3
  have a4 := seqW_some a3 rfl (pexecW_skip i32 fu (setP (appI ps0 nxt) ad0 nxt) (vec.set cur (r : Int)))
  have a5 := seqW_some a1 rfl a4
  have a6 := seqW_some d1' rfl a5
  have sc := pexecW_scope i32 fu _ _ _ _ a6
  simp only [scope_pop ps0 ad0 nxt nxt l0] at sc
  have a7 := seqW_some sc rfl (pexecW_skip i32 fu (setP ps0 ad0 nxt) (vec.set cur (r : Int)))
  refine ⟨_, a7, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, rdK, NExpr.nodes, Container.nodes]
  · simp [vwp, rdK, NExpr.nodes, Container.nodes, hbs]
  · simp


-- During the relinking loop: the nodes passed so far (reachable from `a`, before `cur`, not the root) hold `r`.
def Inv2 (ps vec : List Int) (a r cur : Nat) : Prop :=
  vec.length = ps.length ∧ ∀ v, ((Reach ps a v ∧ v ≠ r ∧ ¬ Reach ps cur v) → vec[v]? = some (r : Int)) ∧
    (¬ (Reach ps a v ∧ v ≠ r ∧ ¬ Reach ps cur v) → vec[v]? = ps[v]?)

theorem inv2_init (ps : List Int) (a r : Nat) : Inv2 ps ps a r a := by
  refine ⟨rfl, fun v => ⟨?_, ?_⟩⟩
  · intro h; exact absurd h.1 h.2.2
  · intro _; rfl

theorem inv2_step (ps vec : List Int) (rank : Nat → Nat) (hF : Forest ps rank) (a r cur : Nat) (nxt : Int)
    (hnxt0 : 0 ≤ nxt) (hps : ps[cur]? = some nxt) (hac : Reach ps a cur) (hcr : cur ≠ r) (hI : Inv2 ps vec a r cur)
    (hcl : cur < vec.length) : Inv2 ps (vec.set cur (r : Int)) a r nxt.toNat := by
  have hn : ((nxt.toNat : Nat) : Int) = nxt := Int.toNat_of_nonneg hnxt0
  have hP : ps[cur]? = some ((nxt.toNat : Nat) : Int) := by rw [hn]; exact hps
  have hcn : Reach ps cur nxt.toNat := Reach.step cur nxt.toNat nxt.toNat hP (Reach.refl _)
  refine ⟨by simp [hI.1], ?_⟩
  intro v
  by_cases hv : v = cur
  · subst hv
    have nR : ¬ Reach ps nxt.toNat v := by
      intro h
      have := reach_rank ps rank hF _ _ h
      have h2 := hF.decrease v nxt hps hnxt0
      omega
    constructor
    · intro _; rw [List.getElem?_set_self hcl]
    · intro h; exact absurd ⟨hac, hcr, nR⟩ h
  · have key : (Reach ps a v ∧ v ≠ r ∧ ¬ Reach ps nxt.toNat v) ↔ (Reach ps a v ∧ v ≠ r ∧ ¬ Reach ps cur v) := by
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, h2, ?_⟩
        intro hc
        cases hc with
        | refl => exact hv rfl
        | step _ b' _ hp hr =>
          have e : ps[cur]? = some (b' : Int) := hp
          rw [hP] at e
          have := Option.some.inj e
          have : b' = nxt.toNat := by omega
          subst this
          exact h3 hr
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, fun hh => h3 (reach_trans ps _ _ _ hcn hh)⟩
    rw [List.getElem?_set_ne (Ne.symm hv)]
    constructor
    · intro h; exact (hI.2 v).1 (key.mp h)
    · intro h; exact (hI.2 v).2 (fun hh => h (key.mpr hh))


theorem vwp_cond2 : vwp cond2 = (3,3) := rfl

theorem cond2_val (ps0 : PS) (vec : List Int) (ad0 ad1 cur r : Nat) (h0 : Loc ps0 0 ad0 cur) (h1 : Loc ps0 1 ad1 r)
    (hc : cur < 2147483648) (hr : r < 2147483648) :
    vdenL i32 vec (penv1 ps0) cond2 = some (if cur = r then 0 else 1) := by
  have e1 := env_loc ps0 0 ad0 cur h0 (i32_valid cur (by omega) (by omega))
  have e2 := env_loc ps0 1 ad1 r h1 (i32_valid r (by omega) (by omega))
  rw [vdenL_scalar _ _ _ _ rfl, den_binary, den_variable, den_variable, e1, e2]
  simp only [Option.bind_some]
  have : binaryValue .ne (cur : Int) (r : Int) = if cur = r then 0 else 1 := by
    by_cases h : cur = r <;> simp [binaryValue, h]
  rw [this]
  simp only [bT]; unfold Ty.convert
  by_cases h : cur = r <;> simp [h]

theorem loop_run2 (ps : List Int) (rank : Nat → Nat) (hF : Forest ps rank) (hn : ps.length < 2147483648)
    (a r : Nat) (hr : r < ps.length) (ad0 ad1 : Nat) (hne : ad0 ≠ ad1) :
    ∀ (m cur : Nat) (ps0 : PS) (vec : List Int), rank cur ≤ m → cur < ps.length → Reach ps a cur → Reach ps cur r →
      Loc ps0 0 ad0 cur → Loc ps0 1 ad1 r → ps0.bs.length = 2 → Inv2 ps vec a r cur → ∀ fu, m + 2 ≤ fu →
      ∃ res, pexecW i32 fu loop2 ps0 vec = some res ∧ res.ps = setP ps0 ad0 r ∧ Inv2 ps res.vec a r r ∧
        res.ret = none ∧ res.cost ≤ 70 * m + 10 ∧ res.need ≤ ps0.mem.length + ps0.bs.length + 40 ∧ res.wk ≤ m := by
  intro m
  induction m with
  | zero =>
    intro cur ps0 vec hrk hcl hac hcr h0 h1 hbs hI fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu'+1 := ⟨fu-1, by omega⟩
    have hcr' : cur = r := by
      by_contra hne'
      cases hcr with
      | refl => exact hne' rfl
      | step _ b' _ hp hr' =>
        have h1' : ps[cur]? = some (b' : Int) := hp
        have := hF.decrease cur (b' : Int) h1' (by omega)
        simp at this
        omega
    subst hcr'
    have hc := cond2_val ps0 vec ad0 ad1 cur cur h0 h1 (by omega) (by omega)
    rw [if_pos rfl] at hc
    rw [pexecW_while, hc]
    simp only [Bind.bind, Option.bind, ite_true, vwp_cond2]
    refine ⟨_, rfl, (setP_same ps0 0 ad0 (cur : Int) h0).symm, hI, rfl, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
  | succ m ih =>
    intro cur ps0 vec hrk hcl hac hcr h0 h1 hbs hI fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu'+1 := ⟨fu-1, by omega⟩
    by_cases hcrr : cur = r
    · subst hcrr
      have hc := cond2_val ps0 vec ad0 ad1 cur cur h0 h1 (by omega) (by omega)
      rw [if_pos rfl] at hc
      rw [pexecW_while, hc]
      simp only [Bind.bind, Option.bind, ite_true, vwp_cond2]
      refine ⟨_, rfl, (setP_same ps0 0 ad0 (cur : Int) h0).symm, hI, rfl, ?_, ?_, ?_⟩
      · simp
      · simp
      · simp
    · cases hcr with
      | refl => exact absurd rfl hcrr
      | step _ nx _ hp hr' =>
        have hps : ps[cur]? = some (nx : Int) := hp
        have hnl : nx < ps.length := by
          have := hF.inside cur (nx : Int) hps (by omega)
          simpa using this
        have hdec := hF.decrease cur (nx : Int) hps (by omega)
        simp at hdec
        have hvec : vec[cur]? = some (nx : Int) := by
          have := (hI.2 cur).2 (fun h => absurd (Reach.refl cur) h.2.2)
          rw [this, hps]
        have gnx : i32.valid (nx : Int) = true := i32_valid nx (by omega) (by omega)
        have hc := cond2_val ps0 vec ad0 ad1 cur r h0 h1 (by omega) (by omega)
        rw [if_neg hcrr] at hc
        obtain ⟨r1, h1', p1, v1, ret1, c1, n1, w1⟩ := iter2 ps0 vec ad0 ad1 cur r (nx : Int) h0 h1 hbs
          (by have := hI.1; omega) (by have := hI.1; omega) hvec gnx (by omega) (fu'+1)
        have hI' := inv2_step ps vec rank hF a r cur (nx : Int) (by omega) hps hac hcrr hI (by have := hI.1; omega)
        have hnn : ((nx : Int)).toNat = nx := by simp
        rw [hnn] at hI'
        have l0 := (List.getElem?_eq_some_iff.mp h0.2).1
        have h0' : Loc (setP ps0 ad0 (nx : Int)) 0 ad0 nx := loc_set ps0 0 ad0 (cur : Int) (nx : Int) h0
        have h1'' : Loc (setP ps0 ad0 (nx : Int)) 1 ad1 r := loc_set_other ps0 1 ad1 ad0 (r : Int) (nx : Int) h1 hne
        have hbs' : (setP ps0 ad0 (nx : Int)).bs.length = 2 := by simp [hbs]
        have hacn : Reach ps a nx := reach_trans ps _ _ _ hac (Reach.step cur nx nx hp (Reach.refl _))
        obtain ⟨r2, h2, p2, I2, ret2, c2, n2, w2⟩ := ih nx (setP ps0 ad0 (nx : Int)) (vec.set cur (r : Int))
          (by omega) hnl hacn hr' h0' h1'' hbs' hI' fu' (by omega)
        rw [pexecW_while, hc]
        simp only [Bind.bind, Option.bind, h1', ret1, p1, v1, h2, vwp_cond2]
        refine ⟨⟨r2.ps, r2.vec, r2.ret, 3+1+r1.cost+r2.cost, max (ps0.mem.length +
          ps0.bs.length + 3 + 2) (max r1.need r2.need), r1.wk+r2.wk⟩, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · show r2.ps = _
          rw [p2]; simp only [setP]; rw [List.set_set]
        · exact I2
        · exact ret2
        · simp; omega
        · simp [n1, n2] at *; omega
        · simp [w1]; omega


theorem body_exec_find_state (P : List Cell) (ps : List Int) (rank : Nat → Nat) (hF : Forest ps rank)
    (hn : ps.length < 2147483648) (a : Nat) (ha : a < ps.length) (fu : Nat) (hfu : rank a + 2 ≤ fu) :
    ∃ (res : PRW) (r : Nat), pexecW i32 fu bodyF (stI P a) ps = some res ∧ res.ret = some (r : Int) ∧
      Reach ps a r ∧ r < ps.length ∧ (∃ v, ps[r]? = some v ∧ v < 0) ∧ Inv2 ps res.vec a r r ∧
      res.cost ≤ 90 * rank a + 60 ∧ res.need ≤ P.length + 60 ∧ res.wk ≤ rank a ∧ res.ps.mem.take P.length = P ∧
      res.ps = setP (setP (appI (stI P a) a) (P.length+1) (r : Int)) P.length (r : Int) := by
  have hav : i32.valid (a : Int) = true := i32_valid a (by omega) (by omega)
  have L0 : Loc (stI P a) 0 P.length a := ⟨by simp [stI], by
    have := Proofs.ModIntExec.get_tail P [⟨i32,(a : Int)⟩] 0
    simpa [stI] using this⟩
  have d1 := decl_step (stI P a) ps 0 P.length (a : Int) L0 hav
  have d1' := (pexecW_prim i32 fu (.declare i32 true (.variable i32 1)) _ _).trans d1
  have L1 : Loc (appI (stI P a) a) 1 (P.length+1) a := by
    simpa [stI] using loc_app_new (stI P a) (a : Int)
  obtain ⟨q1, r, hq1, pq1, vq1, retq1, reach1, hr1, hroot1, cq1, nq1, wq1⟩ :=
    loop_runK ps rank hF hn (rank a) a (appI (stI P a) a) 1 (P.length+1) L1 ha (le_refl _) fu hfu
  have hrv : i32.valid (r : Int) = true := i32_valid r (by omega) (by omega)
  -- the second loop starts from the state after the first
  have M0 : Loc (setP (appI (stI P a) a) (P.length+1) (r : Int)) 0 P.length a :=
    loc_set_other _ _ _ _ _ _ (loc_app_old _ _ _ _ _ L0) (by omega)
  have M1 : Loc (setP (appI (stI P a) a) (P.length+1) (r : Int)) 1 (P.length+1) r := loc_set _ _ _ _ _ L1
  have hbs : (setP (appI (stI P a) a) (P.length+1) (r : Int)).bs.length = 2 := by simp [stI]
  obtain ⟨q2, hq2, pq2, I2, retq2, cq2, nq2, wq2⟩ := loop_run2 ps rank hF hn a r hr1 P.length (P.length+1) (by omega)
    (rank a) a _ ps (le_refl _) ha (Reach.refl a) reach1 M0 M1 hbs (inv2_init ps a r) fu (by omega)
  -- return r
  have M1' : Loc (setP (setP (appI (stI P a) a) (P.length+1) (r : Int)) P.length (r : Int)) 1 (P.length+1) r :=
    loc_set_other _ _ _ _ _ _ M1 (by omega)
  have rv : vdenL i32 q2.vec (penv1 (setP (setP (appI (stI P a) a) (P.length+1) (r : Int)) P.length (r : Int)))
      (NExpr.variable i32 2) = some (r : Int) := by
    rw [vdenL_scalar _ _ _ _ rfl, den_variable]; exact env_loc _ 1 _ r M1' hrv
  have rs := pstmtW_ret_ok i32 (setP (setP (appI (stI P a) a) (P.length+1) (r : Int)) P.length (r : Int)) q2.vec
    (NExpr.variable i32 2) (r : Int) rv
  have e4 := seqW_ret (b := Sk) ((pexecW_prim i32 fu (.ret (.variable i32 2)) _ _).trans rs) rfl
  have e3 := seqW_some hq2 retq2 (by rw [pq2] at *; exact e4)
  rw [← pq1, ← vq1] at e3
  have e2 := seqW_some hq1 retq1 e3
  have e1 := seqW_some d1' rfl e2
  refine ⟨_, r, e1, rfl, reach1, hr1, hroot1, I2, ?_, ?_, ?_, ?_, ?_⟩
  · have hv : (NExpr.variable i32 2).nodes = 1 := rfl
    show 2 + (q1.cost + (q2.cost + ((NExpr.variable i32 2).nodes + 1))) ≤ 90 * rank a + 60
    omega
  · have hs1 : q1.ps.mem.length + q1.ps.bs.length = P.length + 4 := by rw [pq1]; simp [stI]
    simp [stI] at nq1 nq2
    simp [vwp]
    have hv : (NExpr.variable i32 2).nodes = 1 := rfl
    refine ⟨by simp [stI], by omega, by omega, by omega⟩
  · simp [wq1, wq2]
  · show (setP q1.ps P.length (r : Int)).mem.take P.length = P
    rw [pq1, take_setP _ _ _ _ (by omega), take_setP _ _ _ _ (by simp [stI]), take_appI _ _ _ (by simp [stI])]
    simp [stI]


  · show setP q1.ps P.length (r : Int) = _
    rw [pq1]

theorem body_exec_find (P : List Cell) (ps : List Int) (rank : Nat → Nat) (hF : Forest ps rank)
    (hn : ps.length < 2147483648) (a : Nat) (ha : a < ps.length) (fu : Nat) (hfu : rank a + 2 ≤ fu) :
    ∃ (res : PRW) (r : Nat), pexecW i32 fu bodyF (stI P a) ps = some res ∧ res.ret = some (r : Int) ∧
      Reach ps a r ∧ r < ps.length ∧ (∃ v, ps[r]? = some v ∧ v < 0) ∧ Inv2 ps res.vec a r r ∧
      res.cost ≤ 90 * rank a + 60 ∧ res.need ≤ P.length + 60 ∧ res.wk ≤ rank a ∧ res.ps.mem.take P.length = P := by
  obtain ⟨res,r,run,ret,reach,inside,root,inv,cost,need,work,saved,_⟩ :=
    body_exec_find_state P ps rank hF hn a ha fu hfu
  exact ⟨res,r,run,ret,reach,inside,root,inv,cost,need,work,saved⟩


-- The compressed forest: nodes on the path from `a` (except the root) hold `r`, all others are unchanged.
def PathSet (ps : List Int) (a r v : Nat) : Prop := Reach ps a v ∧ v ≠ r

theorem inv2_final (ps vec : List Int) (a r : Nat) (hroot : ∃ w, ps[r]? = some w ∧ w < 0) (hI : Inv2 ps vec a r r) :
    vec.length = ps.length ∧ ∀ v, (PathSet ps a r v → vec[v]? = some (r : Int)) ∧ (¬ PathSet ps a r v → vec[v]? = ps[v]?) := by
  refine ⟨hI.1, fun v => ⟨?_, ?_⟩⟩
  · intro h
    refine (hI.2 v).1 ⟨h.1, h.2, ?_⟩
    intro hr
    exact h.2 (root_reach ps r hroot v hr)
  · intro h
    refine (hI.2 v).2 ?_
    intro hh
    exact h ⟨hh.1, hh.2.1⟩

theorem find_forest (ps vec : List Int) (rank : Nat → Nat) (hF : Forest ps rank) (a r : Nat) (hra : Reach ps a r)
    (hr : r < ps.length) (hroot : ∃ w, ps[r]? = some w ∧ w < 0) (hv : vec.length = ps.length)
    (hspec : ∀ v, (PathSet ps a r v → vec[v]? = some (r : Int)) ∧ (¬ PathSet ps a r v → vec[v]? = ps[v]?))
    (hrv : i32.valid (r : Int) = true) : Forest vec rank := by
  have onpath : ∀ v, PathSet ps a r v → Reach ps v r := by
    intro v hp
    rcases reach_det ps a v r hp.1 hra with h | h
    · exact h
    · exact absurd (root_reach ps r hroot v h) hp.2
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
    by_cases hp : PathSet ps a r i
    · rw [(hspec i).1 hp] at hi
      have := Option.some.inj hi; subst this; exact hrv
    · rw [(hspec i).2 hp] at hi
      exact hF.valid x (List.mem_of_getElem? hi)
  · intro i p hi h0
    by_cases hp : PathSet ps a r i
    · rw [(hspec i).1 hp] at hi
      have := Option.some.inj hi; subst this
      simpa [hv] using hr
    · rw [(hspec i).2 hp] at hi
      have := hF.inside i p hi h0
      rw [hv]; exact this
  · intro i p hi h0
    by_cases hp : PathSet ps a r i
    · rw [(hspec i).1 hp] at hi
      have := Option.some.inj hi; subst this
      simp
      exact reach_rank_lt ps rank hF i r (onpath i hp) hp.2
    · rw [(hspec i).2 hp] at hi
      exact hF.decrease i p hi h0


-- The caller owns a writable root vector of `int` bound at its vector slot `vslot`.
structure VOKWF (caller : NState) (vslot vb V vsc : Nat) (vbuf : Buffer Value) : Prop where
  valid : caller.frame.state.wellFormed = true
  slot : caller.vectorSlot vslot = some vb
  binding : caller.frame.bindings[vb]? = some ⟨V,.integer i32,true,.root vsc⟩
  vtag : caller.frame.state.forest.lookup V = some ⟨.integer i32,none,some vsc,[]⟩
  vfound : caller.frame.state.storage.lookup V = some vbuf
  lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length
  flag : caller.frame.rootWritable[V]? = some true
  strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope
  base : caller.scalars.baseMemory ≤ caller.scalars.memory.length

theorem prepare_fd (caller : NState) {vslot vb V vsc : Nat} {vbuf : Buffer Value}
    (ok : VOKWF caller vslot vb V vsc vbuf) (e : NExpr) (v : Int) (hs : e.scalarOnly = true)
    (hty : e.resultType = i32) (value : e.denote (envOf caller) = some v) (hv : i32.valid v = true) :
    ∃ t, Good (caller.charge 1 1) t e.nodes e.nodes ∧
      ∃ Sinit, prepare caller Proofs.UnionFindInstance.UnionFind_root.parameters [.vectorReference vslot,.value e] = some Sinit ∧
        Sinit.slots = [.vector 0,.scalar 0] ∧ Sinit.scalars.memory = callerP caller ++ [⟨i32,v⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer i32,true,.root vsc⟩]⟩ ∧
        Sinit.scalars.work = t.scalars.work+3 ∧ t.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨resolved,_,_⟩ := resolve_vroot caller.frame vb V vsc i32 true true vbuf ok.binding ok.valid ok.vtag ok.vfound
    ok.lengths ok.flag (fun _ => rfl)
  have rvec : resolve caller (.vector i32 true) (.vectorReference vslot) =
      some (caller.charge 1 1,.vector V vsc i32 true) := by
    simp [resolve,ok.slot,ok.binding,resolved]
  obtain ⟨t,ran,good⟩ := scalar_eval e (caller.charge 1 1) v hs
    (by rw [envOf_core (core_charge caller 1 1)]; exact value)
  refine ⟨t,good,?_⟩
  have res : resolve (caller.charge 1 1) (.scalar i32 false true) (.value e) = some (t,.scalar i32 true v) := by
    simp [resolve,hty,ran]
  have frameT : t.frame = caller.frame := good.1.1
  have fs : t.frame.state = caller.frame.state := by rw [frameT]
  have fr : t.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t.scalars.memory = caller.scalars.memory := good.1.2.2.2.1
  have hbind : t.scalars.bindings = caller.scalars.bindings := good.1.2.2.2.2.1
  have hbase : t.scalars.baseMemory = caller.scalars.baseMemory := good.1.2.2.2.2.2
  have bound : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).bindRoot V (.integer i32) vsc true =
      some (⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer i32,true,.root vsc⟩]⟩,0) := by
    have vobject : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).object V (.integer i32) =
        some (vbuf,⟨.integer i32,none,some vsc,[]⟩) :=
      object_runs _ V _ vbuf _ ok.valid ok.vfound ok.vtag rfl
    have vrooted : caller.frame.state.forest.rootOwner V = some V := CppVectorOwnership.root_runs _ V _ ok.vtag rfl
    have vmax : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).maximum V = some true :=
      maximum_runs _ V V true ok.lengths vrooted ok.flag
    simp only [Frame.bindRoot,vobject,vmax,Bind.bind,Option.bind]
    simp [Frame.addBinding]
  have hp : Proofs.UnionFindInstance.UnionFind_root.parameters = [.vector i32 true,.scalar i32 false true] := rfl
  rw [hp]
  simp [prepare,ok.valid,resolveAll,rvec,res]
  simp [fs,fr,fb,hmem,hbind,hbase,bound,bindAll,bindOne,CppState.bindArgument,hv,callerP,
    NState.observe,CppState.State.observe]
  left
  have g := good.2.2.2.2.1
  simp [NState.charge,NState.observe,CppState.State.observe] at g
  omega

set_option maxHeartbeats 4000000 in
theorem uf_find_correct (caller : NState) {vslot vb V vsc : Nat} {vbuf : Buffer Value}
    (ok : VOKWF caller vslot vb V vsc vbuf) (ps : List Int) (rank : Nat → Nat) (hF : Forest ps rank)
    (hitems : vbuf.items = ps.map Value.integer) (hn : ps.length < 2147483648)
    (hbvalid : vbuf.Valid (accepts (.integer i32))) (hlimit : vbuf.limit = CppVectorBindings.sizeLimit i32)
    (howner : vbuf.owner = V)
    (e : NExpr) (a : Nat) (hs : e.scalarOnly = true) (ht : e.resultType = i32)
    (value : e.denote (envOf caller) = some (a : Int)) (ha : a + 1 < ps.length) :
    ∃ Sinit fuel res, ∃ (r : Nat) (vec' : List Int), prepare caller Proofs.UnionFindInstance.UnionFind_root.parameters
        [.vectorReference vslot,.value e] = some Sinit ∧
      Proofs.UnionFindInstance.UnionFind_root.callFuel fuel caller [.vectorReference vslot,.value e] =
        .finished (res,.scalar (r : Int)) ∧
      Reach ps a r ∧ r < ps.length ∧ (∃ v, ps[r]? = some v ∧ v < 0) ∧ vec'.length = ps.length ∧
      (∀ v, (PathSet ps a r v → vec'[v]? = some (r : Int)) ∧ (¬ PathSet ps a r v → vec'[v]? = ps[v]?)) ∧
      Forest vec' rank ∧
      ScalarPost3 caller Sinit res e.nodes (90 * rank a + 160) caller.scalars.memory (rank a) V vec' := by
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_fd caller ok e (a : Int) hs ht value (i32_valid a (by omega) (by omega))
  let vc : VCtx := ⟨i32,true,true,V,vsc,vbuf,ps,hitems,fun _ => rfl,by omega,
    caller.frame.state.liveSpace,caller.frame.state.storage.work,caller.scope+1,
    caller.frame.state.storage.objects.length⟩
  have fwS : FW vc ps vbuf 0 Sinit.frame := by
    rw [sFrame]
    refine ⟨ok.valid,ok.lengths,rfl,rfl,?_,rfl,rfl,ok.vtag,ok.vfound,ok.flag,hitems,hbvalid,hlimit,howner,by omega⟩
    intro owner k h
    have := ok.strict owner k h
    show k < caller.scope+1
    omega
  obtain ⟨rr,r,hexec,hret,hreach,hrl,hroot,hI,hcost,hneed,hwk,htake⟩ :=
    body_exec_find (callerP caller) ps rank hF hn a (by omega) (rank a + 2) (le_refl _)
  have hexec' := UfBounds.prepend_bounds (j := 1) (a := (a : Int))
    (env_i1 (callerP caller) a (i32_valid a (by omega) (by omega))) hn (by omega) (by omega) hexec
  have hneed' : (UfBounds.bounded (stI (callerP caller) a) rr).need ≤ (callerP caller).length+112 := by
    simp only [UfBounds.bounded,stI,List.length_append,List.length_cons,List.length_nil]
    omega
  have hcost' : (UfBounds.bounded (stI (callerP caller) a) rr).cost ≤ 90 * rank a + 140 := by
    dsimp [UfBounds.bounded]; omega
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have gw1 := good.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1
  have hres : i32.valid (r : Int) = true := i32_valid r (by omega) (by omega)
  have hpost := call_vecw vc true (fun _ => ⟨rfl,rfl⟩) caller Proofs.UnionFindInstance.UnionFind_root
    [.vectorReference vslot,.value e] Sinit
    (callerP caller ++ [(⟨i32,(a : Int)⟩ : Cell)]) [(⟨(callerP caller).length,true⟩ : CppState.Binding)]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [UfRootCall.take_P caller]) ok.base (by decide) (rank a + 2) (UfBounds.bounded (stI (callerP caller) a) rr)
    (by rw [body_eqF]; exact hexec') (r : Int) hret i32 rfl hres hneed' (by simp) e.nodes
    (90 * rank a + 160) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  dsimp only [UfBounds.bounded,UfBounds.charged] at post
  obtain ⟨hlen', hspec⟩ := inv2_final ps rr.vec a r hroot hI
  refine ⟨Sinit,fuel,res,r,rr.vec,hprep,hrun,hreach,hrl,hroot,hlen',hspec,
    find_forest ps rr.vec rank hF a r hreach hrl hroot hlen' hspec hres,?_⟩
  have hle : caller.scalars.memory.length ≤ (callerP caller).length := by omega
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    calc rr.ps.mem.take caller.scalars.memory.length
        = (rr.ps.mem.take (callerP caller).length).take caller.scalars.memory.length := by
          rw [List.take_take, Nat.min_eq_left hle]
      _ = (callerP caller).take caller.scalars.memory.length := by rw [htake]
      _ = caller.scalars.memory := by simp only [callerP]; exact List.take_left' rfl
  rw [hs'] at post
  exact post.relax (le_refl _) (le_refl _) hwk

end Proofs.UfFindCall
