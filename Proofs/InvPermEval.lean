import Proofs.InvPermFrame

namespace Proofs.InvPermEval
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppMixedInvoke
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.FlatVectorStmt Proofs.FillWriteStmt
open Proofs.InvPermFrame Proofs.InvPermMath
open Proofs.CppState (Cell)

abbrev iV : NExpr := .variable i32 3
abbrev iCast : NExpr := .cast u64 iV
abbrev rvE : NExpr := .read i32 (.local 0) iCast
abbrev nV : NExpr := .variable i32 1
abbrev c1E : NExpr := .logical true (.binary bl .le (.literal i32 0) rvE) (.binary bl .lt rvE nV)
abbrev rvCast : NExpr := .cast u64 rvE
abbrev invRd : NExpr := .read i32 (.local 2) rvCast
abbrev negOne : NExpr := .unary i32 .neg (.literal i32 1)
abbrev c2E : NExpr := .binary bl .eq invRd negOne
abbrev wrStmt : NStmt := .write (.local 2) i32 rvCast iV
abbrev incIE : NExpr := .binary i32 .add iV (.literal i32 1)
abbrev ibodyScope : Command :=
  .scope (.sequence (.primitive (.check c1E)) (.sequence (.primitive (.check c2E))
    (.sequence (.primitive wrStmt) (.primitive .skip))))
abbrev ibodyC : Command := .sequence ibodyScope (.sequence (.primitive (.assign 3 i32 incIE)) (.primitive .skip))
abbrev icondE : NExpr := .binary bl .lt iV nV
abbrev iloopC : Command := .whileLoop icondE ibodyC
abbrev declIStmt : NStmt := .declare i32 true (.literal i32 0)
abbrev iscopeC : Command := .scope (.sequence (.primitive declIStmt) (.sequence iloopC (.primitive .skip)))
abbrev invBody : Command :=
  .sequence (.primitive declNStmt) (.sequence (.primitive fillStmt)
    (.sequence iscopeC (.sequence (.primitive (.retVector 2)) (.primitive .skip))))

-- Everything the per-iteration steps need to know about a state.
structure St (F : Fixed) (items : List Int) (rw0 : List Bool) (sc L0 Tw i ib : Nat) (T : NState) (b : Buffer Value) : Prop where
  pt : PT F sc rw0 T (cellsNI items.length i) (bindsNI F) slotsNRI
  fb : IF T.frame F.V F.vsc F.R F.sc L0 Tw F.vbuf b
  vb : F.vbuf.items = items.map Value.integer
  itemsB : b.items = (pinv items items.length ib).map Value.integer
  cap : b.capacity = items.length
  small : items.length < 2147483648
  scope : F.sc ≤ sc

theorem St.env_i {F : Fixed} {items rw0 sc L0 Tw i ib T b} (st : St F items rw0 sc L0 Tw i ib T b) (hi : i < 2147483648) :
    envOf T 3 i32 = some (i : Int) :=
  envOf_at T 3 1 ⟨F.P.length+1,true⟩ i32 i (by simp [st.pt.slots,slotsNRI]) (by simp [st.pt.bindings,bindsNI])
    (by simp [st.pt.memory,cellsNI]) (i32_valid_nat i hi)

theorem St.env_n {F : Fixed} {items rw0 sc L0 Tw i ib T b} (st : St F items rw0 sc L0 Tw i ib T b) :
    envOf T 1 i32 = some (items.length : Int) :=
  envOf_at T 1 0 ⟨F.P.length,true⟩ i32 items.length (by simp [st.pt.slots,slotsNRI]) (by simp [st.pt.bindings,bindsNI])
    (by simp [st.pt.memory,cellsNI]) (i32_valid_nat _ st.small)

def EvB (k : Nat) (u : NState) (e : NExpr) (v : Int) : Prop :=
  ∃ t, Ev u e t v [] k k

theorem EvB.mono {k k' : Nat} {u : NState} {e : NExpr} {v : Int} (h : EvB k u e v) (le : k ≤ k') : EvB k' u e v := by
  obtain ⟨t,ev⟩ := h
  exact ⟨t,ev.mono le le⟩

theorem Core.charge_of {T u : NState} (core : Core T u) (w q : Nat) : Core T (u.charge w q) :=
  core.trans (core_charge u w q)

theorem EvB.next {T u : NState} {k : Nat} {e : NExpr} {v : Int} (h : EvB k u e v) (core : Core T u) :
    ∃ t, Ev u e t v [] k k ∧ Core T t := by
  obtain ⟨t,ev⟩ := h
  exact ⟨t,ev,core.trans (Ev.good ev).1⟩

-- A literal or variable reads no vector.
theorem evB_scalar {T u : NState} (core : Core T u) (e : NExpr) (v : Int) (scalar : e.scalarOnly = true)
    (value : e.denote (envOf T) = some v) (k : Nat) (hn : e.nodes ≤ k) : EvB k u e v := by
  obtain ⟨t,ev⟩ := Ev.scalar scalar (v := v) (s := u) (by rw [envOf_core core]; exact value)
  exact ⟨t,ev.mono hn hn⟩

-- `v[i]`
theorem rv_evB {F : Fixed} {items rw0 sc L0 Tw i ib T b} (st : St F items rw0 sc L0 Tw i ib T b) (hi : i < items.length)
    (x : Int) (hx : items[i]? = some x) {u : NState} (core : Core T u) : EvB 5 u rvE x := by
  have sm := st.small
  have iv : iCast.denote (envOf T) = some (i : Int) := by
    have e3 := st.env_i (by omega)
    have valid : u64.valid (i : Int) = true := u64_valid_nat i (by omega)
    simp [NExpr.denote,e3,Ty.convert_of_valid _ _ valid]
  have hs : u.vectorSlot 0 = some 0 := by simp [NState.vectorSlot,core.2.1,st.pt.slots,slotsNRI]
  have fbind : u.frame.bindings[0]? = some ⟨F.V,.integer i32,false,.root F.vsc⟩ := by
    rw [core.1,st.pt.frameBindings]; simp [vbind,atom]
  obtain ⟨m,hm⟩ := st.fb.vflag
  have item : F.vbuf.items[i]? = some (Value.integer x) := by
    rw [st.vb]; simp [List.getElem?_map,hx]
  obtain ⟨t,ev⟩ := Ev.readRoot u 0 0 F.V F.vsc iCast i i32 false m F.vbuf x (by simp [NExpr.scalarOnly])
    (by rw [envOf_core core]; exact iv) hs fbind (by rw [core.1]; exact st.fb.valid) (by rw [core.1]; exact st.fb.vtag)
    (by rw [core.1]; exact st.fb.vfound) (by rw [core.1]; exact st.fb.lengths) (by rw [core.1]; exact hm)
    (by simp) item
  exact ⟨t,ev.mono (by simp [NExpr.nodes]) (by simp [NExpr.nodes])⟩


theorem Ev.land1 {left right : NExpr} {s t1 t2 : NState} {a b : Int} {extra1 extra2 : List Binding}
    {w1 p1 w2 p2 : Nat}
    (first : Ev (s.charge 0 (left.nodes+right.nodes+1)) left t1 a extra1 w1 p1)
    (second : Ev t1 right t2 b extra2 w2 p2) (na : a ≠ 0) (nb : b ≠ 0) :
    Ev s (.logical true left right) (t2.charge 1 1) 1 (extra1 ++ extra2)
      (w1+w2+1) (max (left.nodes+right.nodes+1) (max (max p1 p2) 1)) := by
  obtain ⟨ran1,good1,bind1⟩ := first
  obtain ⟨ran2,good2,bind2⟩ := second
  have na' : (a == 0) = false := by simpa using na
  have nb' : (b == 0) = false := by simpa using nb
  refine ⟨by simp [NExpr.eval,ran1,ran2,na,nb],?_,?_⟩
  · have := ((GoodF.charge s 0 (left.nodes+right.nodes+1)).trans (good1.trans good2)).trans (GoodF.charge t2 1 1)
    exact this.mono (by omega) (by omega)
  · simp only [charge_frame_bindings]
    rw [bind2,bind1]; simp

theorem bl_one : bl.convert 1 = some 1 := Ty.convert_of_valid bl 1 (by simp [Ty.valid])

-- `0 <= v[i]`
theorem le_evB {F : Fixed} {items rw0 sc L0 Tw i ib T b} (st : St F items rw0 sc L0 Tw i ib T b) (hi : i < items.length)
    (x : Int) (hx : items[i]? = some x) (h0 : 0 ≤ x) {u : NState} (core : Core T u) :
    EvB 20 u (.binary bl .le (.literal i32 0) rvE) 1 := by
  have lit : i32.valid 0 = true := by simp [Ty.valid]
  obtain ⟨t1,ev1,core1⟩ := (evB_scalar (Core.charge_of core 0 ((NExpr.literal i32 0).nodes+rvE.nodes+1))
    (.literal i32 0) 0 (by simp [NExpr.scalarOnly]) (by simp [NExpr.denote,lit]) 5 (by simp [NExpr.nodes])).next
    (Core.charge_of core 0 _)
  obtain ⟨t2,ev2,core2⟩ := (rv_evB st hi x hx core1).next core1
  have conv : bl.convert (binaryValue .le 0 x) = some 1 := by
    simp only [binaryValue,h0,ite_true]; exact bl_one
  have ev := Ev.binary ev1 ev2 conv
  refine ⟨t2.charge 1 1,?_⟩
  have := ev.mono (w' := 20) (p' := 20) (by omega) (by simp [NExpr.nodes,Container.nodes])
  simpa using this

-- `v[i] < n`
theorem lt_evB {F : Fixed} {items rw0 sc L0 Tw i ib T b} (st : St F items rw0 sc L0 Tw i ib T b) (hi : i < items.length)
    (x : Int) (hx : items[i]? = some x) (h1 : x < items.length) {u : NState} (core : Core T u) :
    EvB 20 u (.binary bl .lt rvE nV) 1 := by
  obtain ⟨t1,ev1,core1⟩ := (rv_evB st hi x hx (Core.charge_of core 0 (rvE.nodes+nV.nodes+1))).next
    (Core.charge_of core 0 _)
  obtain ⟨t2,ev2,core2⟩ := (evB_scalar core1 nV (items.length : Int) (by simp [NExpr.scalarOnly])
    (by simp [NExpr.denote]; exact st.env_n) 5 (by simp [NExpr.nodes])).next core1
  have conv : bl.convert (binaryValue .lt x (items.length : Int)) = some 1 := by
    simp only [binaryValue,h1,ite_true]; exact bl_one
  have ev := Ev.binary ev1 ev2 conv
  refine ⟨t2.charge 1 1,?_⟩
  have := ev.mono (w' := 20) (p' := 20) (by omega) (by simp [NExpr.nodes,Container.nodes])
  simpa using this

-- `0 <= v[i] && v[i] < n`
theorem c1_evB {F : Fixed} {items rw0 sc L0 Tw i ib T b} (st : St F items rw0 sc L0 Tw i ib T b) (hi : i < items.length)
    (x : Int) (hx : items[i]? = some x) (h0 : 0 ≤ x) (h1 : x < items.length) {u : NState} (core : Core T u) :
    EvB 60 u c1E 1 := by
  obtain ⟨t1,ev1,core1⟩ := (le_evB st hi x hx h0 (Core.charge_of core 0 _)).next (Core.charge_of core 0 _)
  obtain ⟨t2,ev2,core2⟩ := (lt_evB st hi x hx h1 core1).next core1
  have ev := Ev.land1 ev1 ev2 (by decide) (by decide)
  refine ⟨t2.charge 1 1,?_⟩
  have := ev.mono (w' := 60) (p' := 60) (by omega) (by simp [NExpr.nodes,Container.nodes])
  simpa using this


theorem negOne_value (env : Nat → Ty → Option Int) : negOne.denote env = some (-1) := by
  have lit : i32.valid (1 : Int) = true := by simp [Ty.valid]
  have neg : i32.valid (-1 : Int) = true := by simp [Ty.valid]
  have c1 := Ty.convert_of_valid i32 (-1) neg
  simp [NExpr.denote,lit,unaryValue,c1]

-- `(uint64_t) v[i]`
theorem rvCast_evB {F : Fixed} {items rw0 sc L0 Tw i ib T b} (st : St F items rw0 sc L0 Tw i ib T b) (hi : i < items.length)
    (x : Int) (hx : items[i]? = some x) (h0 : 0 ≤ x) (h1 : x < items.length) {u : NState} (core : Core T u) :
    EvB 20 u rvCast x := by
  have sm := st.small
  obtain ⟨t1,ev1,core1⟩ := (rv_evB st hi x hx (Core.charge_of core 0 (rvE.nodes+1))).next (Core.charge_of core 0 _)
  have conv : u64.convert x = some x := Ty.convert_of_valid _ _ (by simp [Ty.valid]; omega)
  have ev := Ev.cast ev1 conv
  refine ⟨t1.charge 1 1,?_⟩
  have := ev.mono (w' := 20) (p' := 20) (by omega) (by simp [NExpr.nodes,Container.nodes])
  simpa using this

-- `inv[v[i]]` while the target is still -1
theorem invRd_evB {F : Fixed} {items rw0 sc L0 Tw i ib T b} (st : St F items rw0 sc L0 Tw i ib T b) (hi : i < items.length)
    (x : Int) (hx : items[i]? = some x) (h0 : 0 ≤ x) (h1 : x < items.length)
    (hinv : b.items[x.toNat]? = some (Value.integer (-1))) {u : NState} (core : Core T u) :
    EvB 60 u invRd (-1) := by
  have hs : u.vectorSlot 2 = some 1 := by simp [NState.vectorSlot,core.2.1,st.pt.slots,slotsNRI]
  have fbind : u.frame.bindings[1]? = some ⟨F.R,.integer i32,true,.root F.sc⟩ := by
    rw [core.1,st.pt.frameBindings]; simp [vbind,atom,flatBinding]
  have idx : ∀ u' : NState, Core u u' → ∃ t, Ev u' rvCast t (x.toNat : Int) [] 20 20 := by
    intro u' c'
    obtain ⟨t,ev⟩ := rvCast_evB st hi x hx h0 h1 (core.trans c')
    exact ⟨t,by rw [Int.toNat_of_nonneg h0]; exact ev⟩
  obtain ⟨t,ev⟩ := Ev.readRootEv u 2 1 F.R F.sc rvCast x.toNat i32 true true b (-1) 20 20 idx hs fbind
    (by rw [core.1]; exact st.fb.valid) (by rw [core.1]; simpa [flatTag] using st.fb.tag)
    (by rw [core.1]; exact st.fb.found) (by rw [core.1]; exact st.fb.lengths) (by rw [core.1]; exact st.fb.flag)
    (fun h => rfl) hinv
  exact ⟨t,ev.mono (by omega) (by simp [NExpr.nodes,Container.nodes])⟩


-- `inv[v[i]] == -1`
theorem c2_evB {F : Fixed} {items rw0 sc L0 Tw i ib T b} (st : St F items rw0 sc L0 Tw i ib T b) (hi : i < items.length)
    (x : Int) (hx : items[i]? = some x) (h0 : 0 ≤ x) (h1 : x < items.length)
    (hinv : b.items[x.toNat]? = some (Value.integer (-1))) {u : NState} (core : Core T u) :
    EvB 120 u c2E 1 := by
  obtain ⟨t1,ev1,core1⟩ := (invRd_evB st hi x hx h0 h1 hinv (Core.charge_of core 0 (invRd.nodes+negOne.nodes+1))).next
    (Core.charge_of core 0 _)
  obtain ⟨t2,ev2,core2⟩ := (evB_scalar core1 negOne (-1) (by simp [NExpr.scalarOnly]) (negOne_value _) 5
    (by simp [NExpr.nodes])).next core1
  have conv : bl.convert (binaryValue .eq (-1) (-1)) = some 1 := by
    simp only [binaryValue]; simpa using bl_one
  have ev := Ev.binary ev1 ev2 conv
  refine ⟨t2.charge 1 1,?_⟩
  have := ev.mono (w' := 120) (p' := 120) (by omega) (by simp [NExpr.nodes,Container.nodes])
  simpa using this

end Proofs.InvPermEval
