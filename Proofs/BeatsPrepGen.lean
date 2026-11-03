import Proofs.MatMulPrepare
namespace Proofs.BeatsPrepare
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare

/-- `i` unit charges of the caller state. -/
def chargeN (c : NState) : Nat → NState
  | 0 => c
  | i + 1 => (chargeN c i).charge 1 1

theorem chargeN_core (c : NState) : ∀ i, Core c (chargeN c i)
  | 0 => Core.refl c
  | i + 1 => (chargeN_core c i).trans (core_charge _ 1 1)

theorem chargeN_peak (c : NState) : ∀ i, c.scalars.peak ≤ (chargeN c i).scalars.peak
  | 0 => le_refl _
  | i + 1 => le_trans (chargeN_peak c i) (Good.charge (chargeN c i) 1 1).2.2.2.2.1

theorem chargeN_work (c : NState) : ∀ i, (chargeN c i).scalars.work = c.scalars.work + i
  | 0 => rfl
  | i + 1 => by
    have := (Good.charge (chargeN c i) 1 1)
    simp [chargeN, NState.charge, NState.observe, CppState.State.observe, chargeN_work c i]
    omega

def vparams (ty : Nat → Ty) (w : Nat → Bool) (k nv : Nat) : List CppVectorBindings.Parameter :=
  (List.range' k (nv - k)).map (fun i => .vector (ty i) (w i))
def vargs (s : Nat → Nat) (k nv : Nat) : List NArgument :=
  (List.range' k (nv - k)).map (fun i => .vectorReference (s i))
def vres (ty : Nat → Ty) (V vsc : Nat → Nat) (w : Nat → Bool) (k nv : Nat) : List Resolved :=
  (List.range' k (nv - k)).map (fun i => .vector (V i) (vsc i) (ty i) (w i))

theorem resolve_step (caller : NState) (ty : Nat → Ty) (w : Nat → Bool) (s vb V vsc : Nat → Nat) (m : Nat → Bool) (vbuf : Nat → Buffer Value)
    (nv : Nat) (hok : ∀ i, i < nv → VOKG caller (ty i) (s i) (vb i) (V i) (vsc i) (w i) (m i) (vbuf i)) (i : Nat) (hi : i < nv) :
    resolve (chargeN caller i) (.vector (ty i) (w i)) (.vectorReference (s i)) =
      some (chargeN caller (i + 1), .vector (V i) (vsc i) (ty i) (w i)) := by
  obtain ⟨hf, hsl, -, -, -, -⟩ := chargeN_core caller i
  have o := hok i hi
  exact resolve_vref (chargeN caller i) (ty i) (w i) (by unfold NState.vectorSlot; rw [hsl]; exact o.slot)
    (by rw [hf]; exact o.binding) (by rw [hf]; exact o.valid) (by rw [hf]; exact o.vtag) (by rw [hf]; exact o.vfound)
    (by rw [hf]; exact o.lengths) (by rw [hf]; exact o.flag) o.perm (fun h => h)


theorem resolveAll_vec (caller : NState) (ty : Nat → Ty) (w : Nat → Bool) (s vb V vsc : Nat → Nat) (m : Nat → Bool) (vbuf : Nat → Buffer Value)
    (nv : Nat) (hok : ∀ i, i < nv → VOKG caller (ty i) (s i) (vb i) (V i) (vsc i) (w i) (m i) (vbuf i))
    (ps : List CppVectorBindings.Parameter) (as : List NArgument) :
    ∀ d k, k + d = nv → resolveAll (chargeN caller k) (vparams ty w k nv ++ ps) (vargs s k nv ++ as) =
      (resolveAll (chargeN caller nv) ps as).map (fun p => (p.1, vres ty V vsc w k nv ++ p.2)) := by
  intro d
  induction d with
  | zero =>
    intro k hk
    have hk' : k = nv := by omega
    subst hk'
    simp [vparams, vargs, vres]
  | succ d ih =>
    intro k hk
    have hr : nv - k = (nv - (k + 1)) + 1 := by omega
    have e1 : vparams ty w k nv = .vector (ty k) (w k) :: vparams ty w (k + 1) nv := by
      simp only [vparams, hr, List.range'_succ, List.map_cons]
    have e2 : vargs s k nv = .vectorReference (s k) :: vargs s (k + 1) nv := by
      simp only [vargs, hr, List.range'_succ, List.map_cons]
    have e3 : vres ty V vsc w k nv = .vector (V k) (vsc k) (ty k) (w k) :: vres ty V vsc w (k + 1) nv := by
      simp only [vres, hr, List.range'_succ, List.map_cons]
    rw [e1, e2, List.cons_append, List.cons_append]
    have step := resolve_step caller ty w s vb V vsc m vbuf nv hok k (by omega)
    have ih' := ih (k + 1) (by omega)
    simp only [resolveAll, step, Bind.bind, Option.bind]
    rw [ih']
    cases hh : resolveAll (chargeN caller nv) ps as with
    | none => rfl
    | some p => simp [e3]


def bstep (ty : Nat → Ty) (V vsc : Nat → Nat) (w : Nat → Bool) (s : NState) (i : Nat) : NState :=
  ({s with frame := (s.frame.addBinding ⟨V i, .integer (ty i), w i, .root (vsc i)⟩).1,
           slots := s.slots ++ [.vector (s.frame.addBinding ⟨V i, .integer (ty i), w i, .root (vsc i)⟩).2]} : NState).observe

def bindVecs (ty : Nat → Ty) (V vsc : Nat → Nat) (w : Nat → Bool) : NState → Nat → Nat → NState
  | s, 0, _ => s
  | s, d + 1, k => bindVecs ty V vsc w (bstep ty V vsc w s k) d (k + 1)

theorem bindOne_vec (caller s : NState) (ty : Nat → Ty) (w : Nat → Bool) (sl vb V vsc : Nat → Nat) (m : Nat → Bool) (vbuf : Nat → Buffer Value)
    (nv : Nat) (hok : ∀ i, i < nv → VOKG caller (ty i) (sl i) (vb i) (V i) (vsc i) (w i) (m i) (vbuf i))
    (h1 : s.frame.state = caller.frame.state) (h2 : s.frame.rootWritable = caller.frame.rootWritable) (i : Nat) (hi : i < nv) :
    bindOne s (.vector (V i) (vsc i) (ty i) (w i)) = some (bstep ty V vsc w s i) := by
  have o := hok i hi
  have hg := bindRoot_g s.frame (V := V i) (vsc := vsc i) (m := m i) (vbuf := vbuf i) (ty i) (w i)
    (by rw [h1]; exact o.valid) (by rw [h1]; exact o.vtag) (by rw [h1]; exact o.vfound) (by rw [h2, h1]; exact o.lengths)
    (by rw [h2]; exact o.flag) o.perm
  simp only [bindOne, hg, Bind.bind, Option.bind]
  rfl

theorem bstep_inv (caller s : NState) (ty : Nat → Ty) (V vsc : Nat → Nat) (w : Nat → Bool) (i : Nat)
    (h1 : s.frame.state = caller.frame.state) (h2 : s.frame.rootWritable = caller.frame.rootWritable) :
    (bstep ty V vsc w s i).frame.state = caller.frame.state ∧ (bstep ty V vsc w s i).frame.rootWritable = caller.frame.rootWritable :=
  ⟨h1, h2⟩

theorem bindAll_vec (caller : NState) (ty : Nat → Ty) (w : Nat → Bool) (sl vb V vsc : Nat → Nat) (m : Nat → Bool) (vbuf : Nat → Buffer Value)
    (nv : Nat) (hok : ∀ i, i < nv → VOKG caller (ty i) (sl i) (vb i) (V i) (vsc i) (w i) (m i) (vbuf i)) (rs : List Resolved) :
    ∀ d k s, k + d = nv → s.frame.state = caller.frame.state → s.frame.rootWritable = caller.frame.rootWritable →
      bindAll s (vres ty V vsc w k nv ++ rs) = bindAll (bindVecs ty V vsc w s d k) rs := by
  intro d
  induction d with
  | zero =>
    intro k s hk h1 h2
    have : k = nv := by omega
    subst this
    simp [vres, bindVecs]
  | succ d ih =>
    intro k s hk h1 h2
    have hr : nv - k = (nv - (k + 1)) + 1 := by omega
    have e3 : vres ty V vsc w k nv = .vector (V k) (vsc k) (ty k) (w k) :: vres ty V vsc w (k + 1) nv := by
      simp only [vres, hr, List.range'_succ, List.map_cons]
    rw [e3, List.cons_append]
    simp only [bindAll, bindOne_vec caller s ty w sl vb V vsc m vbuf nv hok h1 h2 k (by omega), Bind.bind, Option.bind]
    rw [ih (k + 1) (bstep ty V vsc w s k) (by omega) h1 h2]
    rfl


def bl (ty : Nat → Ty) (V vsc : Nat → Nat) (w : Nat → Bool) (k d : Nat) : List Binding :=
  (List.range' k d).map (fun i => ⟨V i, .integer (ty i), w i, .root (vsc i)⟩)

theorem bindVecs_frame (ty : Nat → Ty) (V vsc : Nat → Nat) (w : Nat → Bool) :
    ∀ d k (s : NState), (bindVecs ty V vsc w s d k).frame = {s.frame with bindings := s.frame.bindings ++ bl ty V vsc w k d} := by
  intro d
  induction d with
  | zero => intro k s; simp [bindVecs, bl]
  | succ d ih =>
    intro k s
    rw [bindVecs, ih]
    simp [bstep, NState.observe, Frame.addBinding, bl, List.range'_succ]

theorem bindVecs_slots (ty : Nat → Ty) (V vsc : Nat → Nat) (w : Nat → Bool) :
    ∀ d k (s : NState), (bindVecs ty V vsc w s d k).slots = s.slots ++ (List.range d).map (fun j => CppMixedInvoke.Location.vector (s.frame.bindings.length + j)) := by
  intro d
  induction d with
  | zero => intro k s; simp [bindVecs]
  | succ d ih =>
    intro k s
    rw [bindVecs, ih]
    simp [bstep, NState.observe, Frame.addBinding, List.range_succ_eq_map, Function.comp_def, Nat.add_assoc, Nat.add_comm 1]

theorem bindVecs_rest (ty : Nat → Ty) (V vsc : Nat → Nat) (w : Nat → Bool) :
    ∀ d k (s : NState), (bindVecs ty V vsc w s d k).scalars = s.scalars ∧ (bindVecs ty V vsc w s d k).scope = s.scope ∧
      s.peak ≤ (bindVecs ty V vsc w s d k).peak := by
  intro d
  induction d with
  | zero => intro k s; simp [bindVecs]
  | succ d ih =>
    intro k s
    rw [bindVecs]
    obtain ⟨a, b, c⟩ := ih (k + 1) (bstep ty V vsc w s k)
    refine ⟨by rw [a]; simp [bstep, NState.observe], by rw [b]; simp [bstep, NState.observe], ?_⟩
    have : s.peak ≤ (bstep ty V vsc w s k).peak := by simp [bstep, NState.observe]
    omega


def initS (caller last : NState) (np : Nat) : NState :=
  let released := last.release caller
  let scalars : CppState.State := {released.scalars with
    memory := released.scalars.memory ++ List.replicate
      (released.scalars.bindings.length+released.frame.bindings.length) ⟨⟨1,false,true⟩,0⟩,
    bindings := [],work := released.scalars.work+1+np}
  (({scalars := scalars, frame := {released.frame with bindings := []}, slots := [], scope := caller.scope+1, peak := released.peak} : NState)).observe

theorem prepare_core (caller : NState) (ty : Nat → Ty) (w : Nat → Bool) (sl vb V vsc : Nat → Nat) (m : Nat → Bool) (vbuf : Nat → Buffer Value)
    (nv : Nat) (hnv : 0 < nv) (hok : ∀ i, i < nv → VOKG caller (ty i) (sl i) (vb i) (V i) (vsc i) (w i) (m i) (vbuf i))
    (ps : List CppVectorBindings.Parameter) (as : List NArgument) (last : NState) (resRest : List Resolved)
    (hres : resolveAll (chargeN caller nv) ps as = some (last, resRest)) (hlast : Core caller last) :
    prepare caller (vparams ty w 0 nv ++ ps) (vargs sl 0 nv ++ as) =
      bindAll (bindVecs ty V vsc w (initS caller last (nv + ps.length)) nv 0) resRest := by
  have hwf : caller.frame.state.wellFormed = true := (hok 0 hnv).valid
  have hall := resolveAll_vec caller ty w sl vb V vsc m vbuf nv hok ps as nv 0 (by omega)
  rw [hres] at hall
  have h0 : chargeN caller 0 = caller := rfl
  rw [h0] at hall
  have hlen : (vparams ty w 0 nv ++ ps).length = nv + ps.length := by simp [vparams]
  obtain ⟨hf, hsl, hsc, hm, hb, hbase⟩ := hlast
  unfold prepare
  rw [if_pos hwf]
  simp only [hall, Option.map_some, Bind.bind, Option.bind]
  have hbA := bindAll_vec caller ty w sl vb V vsc m vbuf nv hok resRest nv 0 (initS caller last (nv + ps.length)) (by omega)
    (by simp [initS, NState.observe, NState.release, hf]) (by simp [initS, NState.observe, NState.release, hf])
  rw [hlen]
  simp only [initS] at hbA ⊢
  rw [hbA]


/-- Evaluating the scalar arguments one after the other. -/
theorem evalChain : ∀ (L : List (NExpr × Ty × Int)) (c : NState),
    (∀ x ∈ L, x.1.scalarOnly = true ∧ x.1.resultType = x.2.1 ∧ x.1.denote (envOf c) = some x.2.2) →
    ∃ last, resolveAll c (L.map (fun x => CppVectorBindings.Parameter.scalar x.2.1 false true)) (L.map (fun x => NArgument.value x.1)) =
        some (last, L.map (fun x => Resolved.scalar x.2.1 true x.2.2)) ∧
      Good c last (L.map (fun x => x.1.nodes)).sum (L.map (fun x => x.1.nodes)).sum
  | [], c, _ => ⟨c, by simp [resolveAll], by simpa using Good.refl c⟩
  | x :: L, c, h => by
    obtain ⟨hs, hty, hd⟩ := h x (by simp)
    obtain ⟨t, ran, g⟩ := scalar_eval x.1 c x.2.2 hs hd
    have henv : envOf t = envOf c := envOf_core g.1
    obtain ⟨last, hres, hg⟩ := evalChain L t (fun y hy => by
      obtain ⟨a, b, d⟩ := h y (by simp [hy])
      exact ⟨a, b, by rw [henv]; exact d⟩)
    refine ⟨last, ?_, ?_⟩
    · simp [resolveAll, resolve, hty, ran, hres]
    · have g1 : Good c t x.1.nodes x.1.nodes := g
      have := g1.trans hg
      simp only [List.map_cons, List.sum_cons]
      exact this.mono (by omega) (by omega)


def bscal (s : NState) (p : Ty × Int) : NState :=
  ({s with scalars := ({s.scalars with memory := s.scalars.memory ++ [⟨p.1, p.2⟩], bindings := s.scalars.bindings ++ [⟨s.scalars.memory.length, true⟩]} : CppState.State).observe 0,
           slots := s.slots ++ [CppMixedInvoke.Location.scalar s.scalars.bindings.length]} : NState).observe

def bindScal : NState → List (Ty × Int) → NState
  | s, [] => s
  | s, p :: L => bindScal (bscal s p) L

theorem bindOne_scalar (s : NState) (T : Ty) (v : Int) (hv : T.valid v = true) :
    bindOne s (.scalar T true v) = some (bscal s (T, v)) := by
  simp [bindOne, CppState.bindArgument, hv, bscal]

theorem bindAll_scal : ∀ (L : List (Ty × Int)) (s : NState), (∀ x ∈ L, x.1.valid x.2 = true) →
    bindAll s (L.map (fun x => Resolved.scalar x.1 true x.2)) = some (bindScal s L)
  | [], s, _ => by simp [bindAll, bindScal]
  | p :: L, s, h => by
    simp only [List.map_cons, bindAll, bindOne_scalar s p.1 p.2 (h p (by simp)), Bind.bind, Option.bind, bindScal]
    exact bindAll_scal L (bscal s p) (fun x hx => h x (by simp [hx]))

theorem bindScal_facts : ∀ (L : List (Ty × Int)) (s : NState),
    (bindScal s L).frame = s.frame ∧ (bindScal s L).scope = s.scope ∧
    (bindScal s L).scalars.memory = s.scalars.memory ++ L.map (fun p => (⟨p.1, p.2⟩ : Cell)) ∧
    (bindScal s L).scalars.bindings = s.scalars.bindings ++ (List.range L.length).map (fun j => (⟨s.scalars.memory.length + j, true⟩ : CppState.Binding)) ∧
    (bindScal s L).slots = s.slots ++ (List.range L.length).map (fun j => CppMixedInvoke.Location.scalar (s.scalars.bindings.length + j)) ∧
    (bindScal s L).scalars.baseMemory = s.scalars.baseMemory ∧ (bindScal s L).scalars.work = s.scalars.work ∧
    s.scalars.peak ≤ (bindScal s L).scalars.peak ∧ s.peak ≤ (bindScal s L).peak
  | [], s => by simp [bindScal]
  | p :: L, s => by
    obtain ⟨a, b, c, d, e, f, g, h, i⟩ := bindScal_facts L (bscal s p)
    have sf : (bscal s p).scalars.peak ≥ s.scalars.peak := by simp [bscal, NState.observe, CppState.State.observe]
    have sp : (bscal s p).peak ≥ s.peak := by simp [bscal, NState.observe]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [bindScal, a]; simp [bscal, NState.observe]
    · simp only [bindScal, b]; simp [bscal, NState.observe]
    · simp only [bindScal, c]; simp [bscal, NState.observe, CppState.State.observe]
    · simp only [bindScal, d]; simp [bscal, NState.observe, CppState.State.observe, List.range_succ_eq_map, Function.comp_def, Nat.add_assoc, Nat.add_comm 1]
    · simp only [bindScal, e]; simp [bscal, NState.observe, CppState.State.observe, List.range_succ_eq_map, Function.comp_def, Nat.add_assoc, Nat.add_comm 1]
    · simp only [bindScal, f]; simp [bscal, NState.observe, CppState.State.observe]
    · simp only [bindScal, g]; simp [bscal, NState.observe, CppState.State.observe]
    · simp only [bindScal]; omega
    · simp only [bindScal]; omega


theorem prepare_gen (caller : NState) (nv : Nat) (hnv : 0 < nv) (ty : Nat → Ty) (w : Nat → Bool) (sl vb V vsc : Nat → Nat) (m : Nat → Bool)
    (vbuf : Nat → Buffer Value) (hok : ∀ i, i < nv → VOKG caller (ty i) (sl i) (vb i) (V i) (vsc i) (w i) (m i) (vbuf i))
    (L : List (NExpr × Ty × Int)) (prog : NProgram)
    (hp : prog.parameters = vparams ty w 0 nv ++ L.map (fun x => CppVectorBindings.Parameter.scalar x.2.1 false true))
    (hL : ∀ x ∈ L, x.1.scalarOnly = true ∧ x.1.resultType = x.2.1 ∧ x.1.denote (envOf caller) = some x.2.2 ∧ x.2.1.valid x.2.2 = true) :
    ∃ last, Good (chargeN caller nv) last (L.map (fun x => x.1.nodes)).sum (L.map (fun x => x.1.nodes)).sum ∧
      ∃ Sinit, prepare caller prog.parameters (vargs sl 0 nv ++ L.map (fun x => NArgument.value x.1)) = some Sinit ∧
        Sinit.slots = slN nv L.length ∧ Sinit.scalars.memory = callerP caller ++ L.map (fun x => (⟨x.2.1, x.2.2⟩ : Cell)) ∧
        Sinit.scalars.bindings = (List.range L.length).map (fun j => (⟨(callerP caller).length + j, true⟩ : CppState.Binding)) ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope + 1 ∧
        Sinit.frame = ⟨caller.frame.state, caller.frame.rootWritable, bl ty V vsc w 0 nv⟩ ∧
        Sinit.scalars.work = last.scalars.work + (nv + L.length + 1) ∧ last.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨last, hres, hg⟩ := evalChain L (chargeN caller nv) (fun x hx => by
    obtain ⟨a, b, c, -⟩ := hL x hx
    exact ⟨a, b, by rw [envOf_core (chargeN_core caller nv)]; exact c⟩)
  have hlast : Core caller last := (chargeN_core caller nv).trans hg.1
  refine ⟨last, hg, ?_⟩
  have hpr := prepare_core caller ty w sl vb V vsc m vbuf nv hnv hok _ _ last _ hres hlast
  have hlen : (L.map (fun x => CppVectorBindings.Parameter.scalar x.2.1 false true)).length = L.length := by simp
  rw [hlen] at hpr
  have hargs : prepare caller prog.parameters (vargs sl 0 nv ++ L.map (fun x => NArgument.value x.1)) =
      bindAll (bindVecs ty V vsc w (initS caller last (nv + L.length)) nv 0) (L.map (fun x => Resolved.scalar x.2.1 true x.2.2)) := by
    rw [hp]; exact hpr
  obtain ⟨hf, hsl, hsc, hm, hb, hbase⟩ := hlast
  set sv := bindVecs ty V vsc w (initS caller last (nv + L.length)) nv 0 with hsv
  have hbs : bindAll sv (L.map (fun x => Resolved.scalar x.2.1 true x.2.2)) = some (bindScal sv (L.map (fun x => (x.2.1, x.2.2)))) := by
    have := bindAll_scal (L.map (fun x => (x.2.1, x.2.2))) sv (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      exact (hL x hx).2.2.2)
    simpa [List.map_map, Function.comp_def] using this
  refine ⟨_, hargs.trans hbs, ?_⟩
  obtain ⟨a1, a2, a3⟩ := bindVecs_rest ty V vsc w nv 0 (initS caller last (nv + L.length))
  have a4 := bindVecs_frame ty V vsc w nv 0 (initS caller last (nv + L.length))
  have a5 := bindVecs_slots ty V vsc w nv 0 (initS caller last (nv + L.length))
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := bindScal_facts (L.map (fun x => (x.2.1, x.2.2))) sv
  have hI1 : (initS caller last (nv + L.length)).frame.bindings = [] := by simp [initS, NState.observe]
  have hI2 : (initS caller last (nv + L.length)).slots = [] := by simp [initS, NState.observe]
  have hI3 : (initS caller last (nv + L.length)).scalars.bindings = [] := by simp [initS, NState.observe]
  have hI4 : (initS caller last (nv + L.length)).scalars.memory = callerP caller := by
    simp [initS, NState.observe, NState.release, hm, hb, hf, callerP]
  have hI5 : (initS caller last (nv + L.length)).frame.state = caller.frame.state := by simp [initS, NState.observe, NState.release, hf]
  have hI6 : (initS caller last (nv + L.length)).frame.rootWritable = caller.frame.rootWritable := by simp [initS, NState.observe, NState.release, hf]
  have hI7 : (initS caller last (nv + L.length)).scalars.work = last.scalars.work + (nv + L.length + 1) := by
    simp [initS, NState.observe, NState.release]; omega
  have hI8 : (initS caller last (nv + L.length)).scalars.baseMemory = caller.scalars.baseMemory := by simp [initS, NState.observe, NState.release, hbase]
  have hI9 : (initS caller last (nv + L.length)).scope = caller.scope + 1 := by simp [initS, NState.observe]
  have hI10 : last.scalars.peak ≤ (initS caller last (nv + L.length)).scalars.peak := by simp [initS, NState.observe, NState.release]
  have hI11 : caller.scalars.peak ≤ last.scalars.peak := by
    exact le_trans (chargeN_peak caller nv) hg.2.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [c5, a5, a1, hI2, hI1, hI3]; simp [slN, ssl]
  · rw [c3, a1, hI4]; simp [List.map_map, Function.comp_def]
  · rw [c4, a1, hI3, hI4]; simp [callerP]
  · rw [c6, a1, hI8]
  · rw [c2, a2, hI9]
  · rw [c1, a4]; simp [hI1, hI5, hI6, bl]
  · rw [c7, a1, hI7]
  · rw [a1] at c8; exact hI10.trans c8
  · rw [a1] at c8; exact (hI11.trans hI10).trans c8

end Proofs.BeatsPrepare
