import Proofs.VecKitW

namespace Proofs.MultiVec
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedFacts
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppMixedInvoke
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.FlatVectorStmt Proofs.QuotientFrame
open Proofs.StraightLine Proofs.Mod61Body Proofs.VecExpr Proofs.FillWriteStmt Proofs.InvPermFrame
open Proofs.VecStraight Proofs.VecStmt Proofs.VecWrite Proofs.VecKitW
open Proofs.CppState (Cell)

/-- A callee with `nv` flat vector parameters (location slots `0 .. nv-1`) and scalar locals from slot `nv` on. -/
structure MV where
  nv : Nat
  ty : Nat → Ty
  wV : Nat → Bool
  flag : Nat → Bool
  R : Nat → Nat
  vsc : Nat → Nat
  perm : ∀ k, wV k = true → flag k = true
  L0 : Nat
  T0 : Nat
  sc : Nat
  N : Nat
  distinct : ∀ j k, j < nv → k < nv → j ≠ k → wV k = true → R j ≠ R k

def slN (nv n : Nat) : List Location := (List.range nv).map (fun k => Location.vector k) ++ ssl n

theorem slN_succ (nv n : Nat) : slN nv (n + 1) = slN nv n ++ [.scalar n] := by
  simp [slN, ssl_succ]

theorem slN_get_scalar (nv n k : Nat) (h : k < n) : (slN nv n)[nv + k]? = some (.scalar k) := by
  simp [slN, ssl, h]

theorem slN_get_vec (nv n k : Nat) (h : k < nv) : (slN nv n)[k]? = some (.vector k) := by
  unfold slN
  rw [List.getElem?_append_left (by simpa using h)]
  simp [h]

theorem vectorSlot_N {S : NState} {nv n k : Nat} (h : S.slots = slN nv n) (hk : k < nv) : S.vectorSlot k = some k := by
  simp [NState.vectorSlot, h, slN_get_vec nv n k hk]

/-- The scalar locals of `ps` follow the `nv` vector slots. -/
def penvN (nv : Nat) (ps : PS) : Nat → Ty → Option Int := fun slot ty =>
  if slot < nv then none else penv ps (slot - nv) ty

theorem envN_of_qs {S : NState} {nv B sc : Nat} {ps : PS} (qs : QS S [] B sc ps.mem ps.bs (slN nv ps.bs.length)) :
    envOf S = penvN nv ps := by
  funext slot ty
  by_cases hs : slot < nv
  · simp [envOf, NState.scalarCell, NState.scalarSlot, qs.slots, slN_get_vec nv _ slot hs, hs, penvN]
  · obtain ⟨k, rfl⟩ : ∃ k, slot = nv + k := ⟨slot - nv, by omega⟩
    have hk : nv + k - nv = k := by omega
    simp only [penvN, if_neg hs, hk]
    unfold envOf NState.scalarCell NState.scalarSlot penv
    rw [qs.slots, qs.bindings, qs.memory]
    by_cases h : k < ps.bs.length
    · have e : (slN nv ps.bs.length)[nv + k]? = some (.scalar k) := slN_get_scalar nv _ k h
      rw [e]
      cases hb : ps.bs[k]? with
      | none => simp at hb; omega
      | some b =>
        cases hm : ps.mem[b.address]? with
        | none => simp [hb, hm]
        | some c =>
          by_cases ok : c.type = ty ∧ ty.valid c.value = true
          · simp [hb, hm, ok]
          · simp [hb, hm, ok]
    · have e : (slN nv ps.bs.length)[nv + k]? = none := by simp [slN, ssl]; omega
      have e2 : ps.bs[k]? = none := by simp; omega
      simp [e, e2]

theorem live_psN {S : NState} {nv B sc : Nat} {ps : PS} (qs : QS S [] B sc ps.mem ps.bs (slN nv ps.bs.length)) :
    liveS S = ps.mem.length - B + ps.bs.length := by
  rw [qs.live_eq]; simp

/-- The meaning of vector expressions (vector `k` has the element type `mv.ty k` and the contents `vv k`). -/
def vdenM (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (e : NExpr) : Option Int :=
  if e.scalarOnly = true then e.denote env else
  match e with
  | .cast t op => (vdenM mv vv env op).bind t.convert
  | .binary t op l r => (vdenM mv vv env l).bind fun a => (vdenM mv vv env r).bind fun b => t.convert (binaryValue op a b)
  | .size (.integer t) (.local k) => if k < mv.nv ∧ t = mv.ty k then some ((vv k).length : Int) else none
  | .read t (.local k) index =>
      if k < mv.nv ∧ t = mv.ty k ∧ index.scalarOnly = true then (index.denote env).bind (elemAtL (mv.ty k) (vv k)) else none
  | _ => none

/-- Replace the `k`-th entry of a family. -/
def upd {α : Type} (f : Nat → α) (k : Nat) (x : α) : Nat → α := fun j => if j = k then x else f j

theorem upd_self {α : Type} (f : Nat → α) (k : Nat) (x : α) : upd f k x k = x := by simp [upd]
theorem upd_other {α : Type} (f : Nat → α) (k j : Nat) (x : α) (h : j ≠ k) : upd f k x j = f j := by simp [upd, h]

def bindOf (mv : MV) (k : Nat) : Binding := ⟨mv.R k, .integer (mv.ty k), mv.wV k, .root (mv.vsc k)⟩

/-- Frame facts about the `nv` writable flat roots, after `wk` units of storage work. -/
structure FWM (mv : MV) (vv : Nat → List Int) (bb : Nat → Buffer Value) (wk : Nat) (fr : Frame) : Prop where
  valid : fr.state.wellFormed = true
  lengths : fr.rootWritable.length = fr.state.forest.objects.length
  live : fr.state.liveSpace = mv.L0
  work : fr.state.storage.work = mv.T0 + wk
  strict : ∀ owner k, fr.state.forest.context owner = some k → k < mv.sc
  count : fr.state.storage.objects.length = mv.N
  bindings : fr.bindings = (List.range mv.nv).map (bindOf mv)
  vtag : ∀ k, k < mv.nv → fr.state.forest.lookup (mv.R k) = some ⟨.integer (mv.ty k),none,some (mv.vsc k),[]⟩
  vfound : ∀ k, k < mv.nv → fr.state.storage.lookup (mv.R k) = some (bb k)
  flagR : ∀ k, k < mv.nv → fr.rootWritable[mv.R k]? = some (mv.flag k)
  items : ∀ k, k < mv.nv → (bb k).items = (vv k).map Value.integer
  bvalid : ∀ k, k < mv.nv → (bb k).Valid (accepts (.integer (mv.ty k)))
  limit : ∀ k, k < mv.nv → (bb k).limit = CppVectorBindings.sizeLimit (mv.ty k)
  owner : ∀ k, k < mv.nv → (bb k).owner = mv.R k
  small : ∀ k, k < mv.nv → (vv k).length < 18446744073709551616

theorem FWM.of_eq {mv : MV} {vv : Nat → List Int} {bb : Nat → Buffer Value} {wk : Nat} {fr fr' : Frame}
    (fw : FWM mv vv bb wk fr) (h : fr' = fr) : FWM mv vv bb wk fr' := by rw [h]; exact fw

theorem FWM.wk_eq {mv : MV} {vv : Nat → List Int} {bb : Nat → Buffer Value} {wk wk' : Nat} {fr : Frame}
    (fw : FWM mv vv bb wk fr) (h : wk = wk') : FWM mv vv bb wk' fr := by rw [← h]; exact fw

theorem FWM.noop {mv : MV} {vv : Nat → List Int} {bb : Nat → Buffer Value} {wk : Nat} {fr fr' : Frame}
    (fw : FWM mv vv bb wk fr) (same : SameObjects fr.state fr'.state)
    (rw : fr'.rootWritable = fr.rootWritable) (work : fr'.state.storage.work = fr.state.storage.work)
    (hb : fr'.bindings = fr.bindings) : FWM mv vv bb wk fr' := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,fw.items,fw.bvalid,fw.limit,fw.owner,fw.small⟩
  · rw [same.wellFormed]; exact fw.valid
  · rw [rw,same.1]; exact fw.lengths
  · rw [same.liveSpace]; exact fw.live
  · rw [work]; exact fw.work
  · intro owner k h
    rw [same.1] at h
    exact fw.strict owner k h
  · rw [same.2.1]; exact fw.count
  · rw [hb]; exact fw.bindings
  · intro k hk; rw [same.1]; exact fw.vtag k hk
  · intro k hk; rw [same.lookup]; exact fw.vfound k hk
  · intro k hk; rw [rw]; exact fw.flagR k hk

theorem FWM.fresh {mv : MV} {vv : Nat → List Int} {bb : Nat → Buffer Value} {wk : Nat} {fr : Frame}
    (fw : FWM mv vv bb wk fr) {scope : Nat} (hsc : mv.sc ≤ scope) :
    ∀ owner, fr.state.forest.context owner ≠ some (scope+1) := by
  intro owner h
  have := fw.strict owner _ h
  omega

/-- A write of one element of vector `k`: its contents change, nothing else does. -/
theorem FWM.write {mv : MV} {vv : Nat → List Int} {bb : Nat → Buffer Value} {wk : Nat} {fr : Frame}
    (fw : FWM mv vv bb wk fr) (k : Nat) (hk : k < mv.nv) (hwr : mv.wV k = true) (p : Nat) (hp : p < (vv k).length) (x : Int)
    (hx : (mv.ty k).valid x = true) :
    FWM mv (upd vv k ((vv k).set p x)) (upd bb k {bb k with items := (bb k).items.set p (Value.integer x)}) (wk + 1)
      (fr.updated (mv.R k) (bb k) ⟨{bb k with items := (bb k).items.set p (Value.integer x)},(),1,(bb k).capacity+2⟩) := by
  have bound : mv.R k < fr.state.storage.objects.length := CppVectorStore.lookup_bound _ (mv.R k) (bb k) (fw.vfound k hk)
  have lengthsEq : (fr.updated (mv.R k) (bb k) ⟨{bb k with items := (bb k).items.set p (Value.integer x)},(),1,(bb k).capacity+2⟩).state.storage.objects.length =
      fr.state.storage.objects.length := by simp [Frame.updated]
  have forestEq : (fr.updated (mv.R k) (bb k) ⟨{bb k with items := (bb k).items.set p (Value.integer x)},(),1,(bb k).capacity+2⟩).state.forest =
      fr.state.forest := rfl
  have other : ∀ o, o ≠ mv.R k → (fr.updated (mv.R k) (bb k) ⟨{bb k with items := (bb k).items.set p (Value.integer x)},(),1,(bb k).capacity+2⟩).state.storage.lookup o =
      fr.state.storage.lookup o :=
    fun o ho => CppNestedOps.updated_lookup_other fr (mv.R k) o (bb k) _ (Ne.symm ho)
  have self := CppNestedOps.updated_lookup_self fr (mv.R k) (bb k) ⟨{bb k with items := (bb k).items.set p (Value.integer x)},(),1,(bb k).capacity+2⟩ bound
  have live := liveSpace_update fr.state (fr.updated (mv.R k) (bb k) ⟨{bb k with items := (bb k).items.set p (Value.integer x)},(),1,(bb k).capacity+2⟩).state
    (mv.R k) bound lengthsEq forestEq other
  have tag : fr.state.forest.lookup (mv.R k) = some (flatTag (mv.ty k) (mv.vsc k)) := fw.vtag k hk
  have n0 := nodeSpace_flat_ty fr.state (mv.R k) (mv.vsc k) (mv.ty k) (bb k) tag (fw.vfound k hk)
  have n1 := nodeSpace_flat_ty (fr.updated (mv.R k) (bb k) ⟨{bb k with items := (bb k).items.set p (Value.integer x)},(),1,(bb k).capacity+2⟩).state
    (mv.R k) (mv.vsc k) (mv.ty k) {bb k with items := (bb k).items.set p (Value.integer x)} (by rw [forestEq]; exact tag) self
  have newValid := CppVector.writeRef_preserves_valid (bb k) (accepts (.integer (mv.ty k))) p (Value.integer x)
    (fw.bvalid k hk) (by simpa [accepts] using hx)
  have owns : ({bb k with items := (bb k).items.set p (Value.integer x)} : Buffer Value).owner = mv.R k := fw.owner k hk
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact updated_wellFormed fr (mv.R k) (bb k) (flatTag (mv.ty k) (mv.vsc k)) _ fw.valid tag bound owns
      (by simp [payloadOK,flatTag,newValid])
  · simpa [Frame.updated] using fw.lengths
  · rw [n0,n1] at live
    exact (Nat.add_right_cancel live).trans fw.live
  · simp [Frame.updated,fw.work]
    omega
  · intro owner k' h
    exact fw.strict owner k' h
  · rw [lengthsEq]; exact fw.count
  · simpa [Frame.updated] using fw.bindings
  · intro j hj; exact fw.vtag j hj
  · intro j hj
    by_cases hjk : j = k
    · subst hjk; rw [upd_self]; exact self
    · rw [upd_other _ _ _ _ hjk, other _ (mv.distinct j k hj hk hjk hwr)]; exact fw.vfound j hj
  · intro j hj; simpa [Frame.updated] using fw.flagR j hj
  · intro j hj
    by_cases hjk : j = k
    · subst hjk; rw [upd_self, upd_self]; simp [fw.items j hj, List.map_set]
    · rw [upd_other _ _ _ _ hjk, upd_other _ _ _ _ hjk]; exact fw.items j hj
  · intro j hj
    by_cases hjk : j = k
    · subst hjk; rw [upd_self]; exact newValid
    · rw [upd_other _ _ _ _ hjk]; exact fw.bvalid j hj
  · intro j hj
    by_cases hjk : j = k
    · subst hjk; rw [upd_self]; exact fw.limit j hj
    · rw [upd_other _ _ _ _ hjk]; exact fw.limit j hj
  · intro j hj
    by_cases hjk : j = k
    · subst hjk; rw [upd_self]; exact owns
    · rw [upd_other _ _ _ _ hjk]; exact fw.owner j hj
  · intro j hj
    by_cases hjk : j = k
    · subst hjk; rw [upd_self]; simpa using fw.small j hj
    · rw [upd_other _ _ _ _ hjk]; exact fw.small j hj

/-- Replacing the buffer of the writable vector `k` by `nb` (same owner, limit and capacity) holding `L'`, at cost `d`. -/
theorem FWM.replace {mv : MV} {vv : Nat → List Int} {bb : Nat → Buffer Value} {wk : Nat} {fr : Frame}
    (fw : FWM mv vv bb wk fr) (k : Nat) (hk : k < mv.nv) (hwr : mv.wV k = true) (L' : List Int) (nb : Buffer Value) (d : Nat)
    (hitems : nb.items = L'.map Value.integer) (hlimit : nb.limit = (bb k).limit) (howner : nb.owner = (bb k).owner)
    (hcap : nb.capacity = (bb k).capacity) (hvalid : nb.Valid (accepts (.integer (mv.ty k))))
    (hsmall : L'.length < 18446744073709551616) :
    FWM mv (upd vv k L') (upd bb k nb) (wk + d) (fr.updated (mv.R k) (bb k) ⟨nb,(),d,(bb k).capacity+2⟩) := by
  have bound : mv.R k < fr.state.storage.objects.length := CppVectorStore.lookup_bound _ (mv.R k) (bb k) (fw.vfound k hk)
  have lengthsEq : (fr.updated (mv.R k) (bb k) ⟨nb,(),d,(bb k).capacity+2⟩).state.storage.objects.length =
      fr.state.storage.objects.length := by simp [Frame.updated]
  have forestEq : (fr.updated (mv.R k) (bb k) ⟨nb,(),d,(bb k).capacity+2⟩).state.forest = fr.state.forest := rfl
  have other : ∀ o, o ≠ mv.R k → (fr.updated (mv.R k) (bb k) ⟨nb,(),d,(bb k).capacity+2⟩).state.storage.lookup o =
      fr.state.storage.lookup o :=
    fun o ho => CppNestedOps.updated_lookup_other fr (mv.R k) o (bb k) _ (Ne.symm ho)
  have self := CppNestedOps.updated_lookup_self fr (mv.R k) (bb k) ⟨nb,(),d,(bb k).capacity+2⟩ bound
  have live := liveSpace_update fr.state (fr.updated (mv.R k) (bb k) ⟨nb,(),d,(bb k).capacity+2⟩).state
    (mv.R k) bound lengthsEq forestEq other
  have tag : fr.state.forest.lookup (mv.R k) = some (flatTag (mv.ty k) (mv.vsc k)) := fw.vtag k hk
  have n0 := nodeSpace_flat_ty fr.state (mv.R k) (mv.vsc k) (mv.ty k) (bb k) tag (fw.vfound k hk)
  have n1 := nodeSpace_flat_ty (fr.updated (mv.R k) (bb k) ⟨nb,(),d,(bb k).capacity+2⟩).state
    (mv.R k) (mv.vsc k) (mv.ty k) nb (by rw [forestEq]; exact tag) self
  have owns : nb.owner = mv.R k := howner.trans (fw.owner k hk)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact updated_wellFormed fr (mv.R k) (bb k) (flatTag (mv.ty k) (mv.vsc k)) _ fw.valid tag bound owns
      (by simp [payloadOK,flatTag,hvalid])
  · simpa [Frame.updated] using fw.lengths
  · rw [n0,n1] at live
    rw [hcap] at live
    exact (Nat.add_right_cancel live).trans fw.live
  · simp [Frame.updated,fw.work]
    omega
  · intro owner k' h
    exact fw.strict owner k' h
  · rw [lengthsEq]; exact fw.count
  · simpa [Frame.updated] using fw.bindings
  · intro j hj; exact fw.vtag j hj
  · intro j hj
    by_cases hjk : j = k
    · subst hjk; rw [upd_self]; exact self
    · rw [upd_other _ _ _ _ hjk, other _ (mv.distinct j k hj hk hjk hwr)]; exact fw.vfound j hj
  · intro j hj; simpa [Frame.updated] using fw.flagR j hj
  · intro j hj
    by_cases hjk : j = k
    · subst hjk; rw [upd_self, upd_self]; exact hitems
    · rw [upd_other _ _ _ _ hjk, upd_other _ _ _ _ hjk]; exact fw.items j hj
  · intro j hj
    by_cases hjk : j = k
    · subst hjk; rw [upd_self]; exact hvalid
    · rw [upd_other _ _ _ _ hjk]; exact fw.bvalid j hj
  · intro j hj
    by_cases hjk : j = k
    · subst hjk; rw [upd_self]; exact hlimit.trans (fw.limit j hj)
    · rw [upd_other _ _ _ _ hjk]; exact fw.limit j hj
  · intro j hj
    by_cases hjk : j = k
    · subst hjk; rw [upd_self]; exact owns
    · rw [upd_other _ _ _ _ hjk]; exact fw.owner j hj
  · intro j hj
    by_cases hjk : j = k
    · subst hjk; rw [upd_self]; exact hsmall
    · rw [upd_other _ _ _ _ hjk]; exact fw.small j hj

theorem bind_get (mv : MV) (k : Nat) (hk : k < mv.nv) : ((List.range mv.nv).map (bindOf mv))[k]? = some (bindOf mv k) := by
  simp [List.getElem?_map, hk]

theorem ev_vdenM (mv : MV) {vv : Nat → List Int} {bb : Nat → Buffer Value} {wk : Nat} : ∀ (e : NExpr) (S : NState) (ps : PS)
    {B sc : Nat} (v : Int) (qs : QS S [] B sc ps.mem ps.bs (slN mv.nv ps.bs.length)) {fr : Frame}
    (hfr : S.frame = fr) (fw : FWM mv vv bb wk fr) (h : vdenM mv vv (penvN mv.nv ps) e = some v),
    ∃ t, Ev S e t v [] (vwp e).1 (vwp e).2
  | e, S, ps, B, sc, v, qs, fr, hfr, fw, h => by
    subst hfr
    by_cases hs : e.scalarOnly = true
    · have h' : e.denote (envOf S) = some v := by
        rw [envN_of_qs qs]; have := h; unfold vdenM at this; simpa [hs] using this
      obtain ⟨t, ev⟩ := Ev.scalar hs h'
      exact ⟨t, by rw [vwp_scalar e hs]; exact ev⟩
    · cases e with
      | cast ty op =>
        have hn : (vdenM mv vv (penvN mv.nv ps) op).bind ty.convert = some v := by
          have := h; unfold vdenM at this; simpa [hs] using this
        obtain ⟨a, ha, hc⟩ := Option.bind_eq_some_iff.mp hn
        obtain ⟨t, ev⟩ := ev_vdenM mv op (S.charge 0 (op.nodes+1)) ps a (qs.core (core_charge S 0 _)) rfl fw ha
        refine ⟨t.charge 1 1, ?_⟩
        have := Ev.cast ev hc
        simpa [vwp, hs] using this
      | binary ty o l r =>
        have hn : (vdenM mv vv (penvN mv.nv ps) l).bind (fun a => (vdenM mv vv (penvN mv.nv ps) r).bind fun b => ty.convert (binaryValue o a b)) = some v := by
          have := h; unfold vdenM at this; simpa [hs] using this
        obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.mp hn
        obtain ⟨b, hb', hc⟩ := Option.bind_eq_some_iff.mp hb
        obtain ⟨t1, ev1⟩ := ev_vdenM mv l (S.charge 0 (l.nodes+r.nodes+1)) ps a (qs.core (core_charge S 0 _)) rfl fw ha
        have g1 := Ev.good ev1
        have core1 : Core S t1 := (core_charge S 0 _).trans g1.1
        obtain ⟨t2, ev2⟩ := ev_vdenM mv r t1 ps b (qs.core core1) rfl (fw.of_eq core1.1) hb'
        refine ⟨t2.charge 1 1, ?_⟩
        have := Ev.binary ev1 ev2 hc
        simpa [vwp, hs] using this
      | size el ct =>
        cases el with
        | vector _ => unfold vdenM at h; simp [hs] at h
        | integer ty =>
          cases ct with
          | row _ _ _ => unfold vdenM at h; simp [hs] at h
          | «local» k =>
            have hn : (if k < mv.nv ∧ ty = mv.ty k then some ((vv k).length : Int) else none) = some v := by
              have := h; unfold vdenM at this; simpa [hs] using this
            have hc : k < mv.nv ∧ ty = mv.ty k := by
              by_cases t : k < mv.nv ∧ ty = mv.ty k
              · exact t
              · simp [t] at hn
            obtain ⟨hk, hty⟩ := hc
            subst hty
            have hsz : (bb k).items.length = (vv k).length := by rw [fw.items k hk, List.length_map]
            have hv : ((vv k).length : Int) = v := by simp [hk] at hn; exact hn
            have small : (bb k).items.length < 2 ^ 64 := by
              rw [hsz]; have := fw.small k hk; simpa using this
            obtain ⟨t, ev⟩ := Ev.sizeRoot S k k (mv.R k) (mv.vsc k) (mv.ty k) (mv.wV k) (mv.flag k) (bb k) (vectorSlot_N qs.slots hk)
              (by rw [fw.bindings]; exact bind_get mv k hk) fw.valid (fw.vtag k hk) (fw.vfound k hk) fw.lengths
              (fw.flagR k hk) (mv.perm k) small
            refine ⟨t, ?_⟩
            rw [hsz, hv] at ev
            simpa [vwp] using ev
      | read ty ct index =>
        cases ct with
        | row _ _ _ => unfold vdenM at h; simp [hs] at h
        | «local» k =>
          have hn : (if k < mv.nv ∧ ty = mv.ty k ∧ index.scalarOnly = true then
              (index.denote (penvN mv.nv ps)).bind (elemAtL (mv.ty k) (vv k)) else none) = some v := by
            have := h; unfold vdenM at this; simpa [hs] using this
          have hc : k < mv.nv ∧ ty = mv.ty k ∧ index.scalarOnly = true := by
            by_cases t : k < mv.nv ∧ ty = mv.ty k ∧ index.scalarOnly = true
            · exact t
            · simp [t] at hn
          obtain ⟨hk, hty, hidx⟩ := hc
          subst hty
          simp only [hk, hidx, and_self, ite_true] at hn
          obtain ⟨j, hj, he⟩ := Option.bind_eq_some_iff.mp hn
          unfold elemAtL at he
          by_cases hj0 : 0 ≤ j
          · simp only [hj0, ite_true] at he
            obtain ⟨x, hx, hxv⟩ := Option.bind_eq_some_iff.mp he
            by_cases hvalid : (mv.ty k).valid x = true
            · simp only [hvalid, ite_true] at hxv
              have hxv' : x = v := Option.some.inj hxv
              have jnat : ((j.toNat : Nat) : Int) = j := Int.toNat_of_nonneg hj0
              have item : (bb k).items[j.toNat]? = some (Value.integer v) := by
                rw [fw.items k hk]; simp [List.getElem?_map, hx, hxv']
              have idxv : index.denote (envOf S) = some ((j.toNat : Nat) : Int) := by
                rw [envN_of_qs qs, jnat]; exact hj
              obtain ⟨t, ev⟩ := Ev.readRoot S k k (mv.R k) (mv.vsc k) index j.toNat (mv.ty k) (mv.wV k) (mv.flag k) (bb k) v hidx idxv
                (vectorSlot_N qs.slots hk) (by rw [fw.bindings]; exact bind_get mv k hk) fw.valid (fw.vtag k hk)
                (fw.vfound k hk) fw.lengths (fw.flagR k hk) (mv.perm k) item
              exact ⟨t, by simpa [vwp] using ev⟩
            · simp [hvalid] at hxv
          · simp [hj0] at he
      | literal _ _ => simp [NExpr.scalarOnly] at hs
      | «variable» _ _ => simp [NExpr.scalarOnly] at hs
      | targetCast _ _ => unfold vdenM at h; simp [hs] at h
      | unary _ _ _ => unfold vdenM at h; simp [hs] at h
      | divrem _ _ _ _ => unfold vdenM at h; simp [hs] at h
      | logical _ _ _ => unfold vdenM at h; simp [hs] at h

-- `x_k[index] = value;` on the writable vector `k`.
theorem write_stepM (mv : MV) (k : Nat) (hk : k < mv.nv) (hwr : mv.wV k = true) (hfl : mv.flag k = true)
    {vv : Nat → List Int} {bb : Nat → Buffer Value} {wk : Nat} (S : NState) (ps : PS)
    {B sc SPB TPB W : Nat} (qs : QS S [] B sc ps.mem ps.bs (slN mv.nv ps.bs.length)) (fw : FWM mv vv bb wk S.frame)
    (cq : Cq SPB TPB W S) (iE vE : NExpr) (p : Nat) (x : Int) (wv pv wi pi : Nat)
    (vEv : ∀ u : NState, Core S u → ∃ t, Ev u vE t x [] wv pv)
    (idx : ∀ u : NState, Core S u → ∃ t, Ev u iE t (p : Int) [] wi pi)
    (hp : p < (vv k).length) (hx : (mv.ty k).valid x = true)
    (cap : liveS S+iE.nodes+vE.nodes+pv+pi+5 ≤ SPB) (space : mv.L0+1 ≤ TPB) :
    ∃ t, (NStmt.write (.local k) (mv.ty k) iE vE).run S = some ⟨t,none,false⟩ ∧
      QS t [] B sc ps.mem ps.bs (slN mv.nv ps.bs.length) ∧
      FWM mv (upd vv k ((vv k).set p x)) (upd bb k {bb k with items := (bb k).items.set p (Value.integer x)}) (wk+1) t.frame ∧
      Cq SPB TPB (W+wv+wi+3) t := by
  have hs : S.vectorSlot k = some k := vectorSlot_N qs.slots hk
  have fbind : S.frame.bindings[k]? = some (flatBinding (mv.R k) (mv.ty k) (mv.vsc k)) := by
    rw [fw.bindings, bind_get mv k hk]
    simp [bindOf, flatBinding, hwr]
  have lenB : (bb k).items.length = (vv k).length := by rw [fw.items k hk]; simp
  obtain ⟨t,run,tf,tsl,tsc,tm,tb,tbase,gw1,gw2,gp1,gp2,gq1,gq2⟩ := write_flat_stmtE S k k iE vE p x wv pv (mv.R k) (mv.vsc k)
    (mv.ty k) (bb k) wi pi vEv idx hs fbind fw.valid (fw.vtag k hk) (fw.vfound k hk) fw.lengths
    (by rw [fw.flagR k hk, hfl]) hx (by omega)
  have fw' := fw.write k hk hwr p hp x hx
  rw [← tf] at fw'
  have storageT : t.frame.state.storage.peak = max S.frame.state.storage.peak
      (S.frame.state.liveSpace+((bb k).capacity+2-((bb k).capacity+1))-S.frame.state.storage.baseSpace) := by
    rw [tf]; simp [Frame.updated]
  have spB := cq.scalarPeak
  have stB := cq.storagePeak
  have opB := cq.outerPeak
  have liveS0 := fw.live
  have eS : (fx SPB TPB).SPB = SPB := rfl
  have eT : (fx SPB TPB).TPB = TPB := rfl
  rw [eS] at spB opB
  rw [eT] at stB opB
  refine ⟨t,run,⟨?_,?_,?_,?_,?_⟩,fw',?_⟩
  · rw [tsl]; exact qs.slots
  · rw [tm]; exact qs.memory
  · rw [tb]; exact qs.bindings
  · rw [tbase]; exact qs.base
  · rw [tsc]; exact qs.scope
  · refine ⟨?_,?_,?_,?_⟩
    · have := cq.work; omega
    · show t.scalars.peak ≤ SPB
      omega
    · show t.frame.state.storage.peak ≤ TPB
      rw [storageT]; omega
    · show t.peak ≤ SPB + TPB
      omega


-- `std::sort(x_k.begin(), x_k.end());` on the writable vector `k`.
theorem sort_stepM (mv : MV) (k : Nat) (hk : k < mv.nv) (hwr : mv.wV k = true) (hfl : mv.flag k = true)
    {vv : Nat → List Int} {bb : Nat → Buffer Value} {wk : Nat} (S : NState) (ps : PS)
    {B sc SPB TPB W : Nat} (qs : QS S [] B sc ps.mem ps.bs (slN mv.nv ps.bs.length)) (fw : FWM mv vv bb wk S.frame)
    (cq : Cq SPB TPB W S)
    (cap : liveS S+3 ≤ SPB) (space : mv.L0+1 ≤ TPB) :
    ∃ t, (NStmt.sortVec (.local k) (mv.ty k)).run S = some ⟨t,none,false⟩ ∧
      QS t [] B sc ps.mem ps.bs (slN mv.nv ps.bs.length) ∧
      FWM mv (upd vv k ((vv k).mergeSort (fun x y => decide (x ≤ y))))
        (upd bb k {bb k with items := ((vv k).mergeSort (fun x y => decide (x ≤ y))).map Value.integer})
        (wk + (Proofs.StlContracts.sortComparisons (vv k).length + (vv k).length)) t.frame ∧
      Cq SPB TPB (W+3) t := by
  have hs : S.vectorSlot k = some k := vectorSlot_N qs.slots hk
  have fbind : S.frame.bindings[k]? = some (flatBinding (mv.R k) (mv.ty k) (mv.vsc k)) := by
    rw [fw.bindings, bind_get mv k hk]
    simp [bindOf, flatBinding, hwr]
  have hints : (bb k).items.mapM Value.intOf = some (vv k) := by
    rw [fw.items k hk]; exact mapM_integer (vv k)
  obtain ⟨t,run,tf,tsl,tsc,tm,tb,tbase,gw1,gw2,gp1,gp2,gq1,gq2⟩ := sort_flat_stmtE S k k (mv.R k) (mv.vsc k) (mv.ty k) (bb k) (vv k)
    hs fbind fw.valid (fw.vtag k hk) (fw.vfound k hk) fw.lengths (by rw [fw.flagR k hk, hfl]) hints
  have fw' := fw.replace k hk hwr _ {bb k with items := ((vv k).mergeSort (fun x y => decide (x ≤ y))).map Value.integer}
    (Proofs.StlContracts.sortComparisons (vv k).length + (vv k).length) rfl rfl rfl rfl
    (sorted_valid (bb k) (mv.ty k) (vv k) (fw.bvalid k hk) hints)
    (by rw [List.length_mergeSort]; exact fw.small k hk)
  rw [← tf] at fw'
  have storageT : t.frame.state.storage.peak = max S.frame.state.storage.peak
      (S.frame.state.liveSpace+((bb k).capacity+2-((bb k).capacity+1))-S.frame.state.storage.baseSpace) := by
    rw [tf]; simp [Frame.updated]
  have spB := cq.scalarPeak
  have stB := cq.storagePeak
  have opB := cq.outerPeak
  have liveS0 := fw.live
  have eS : (fx SPB TPB).SPB = SPB := rfl
  have eT : (fx SPB TPB).TPB = TPB := rfl
  rw [eS] at spB opB
  rw [eT] at stB opB
  refine ⟨t,run,⟨?_,?_,?_,?_,?_⟩,fw',?_⟩
  · rw [tsl]; exact qs.slots
  · rw [tm]; exact qs.memory
  · rw [tb]; exact qs.bindings
  · rw [tbase]; exact qs.base
  · rw [tsc]; exact qs.scope
  · refine ⟨?_,?_,?_,?_⟩
    · have := cq.work; omega
    · show t.scalars.peak ≤ SPB
      omega
    · show t.frame.state.storage.peak ≤ TPB
      rw [storageT]; omega
    · show t.peak ≤ SPB + TPB
      omega

-- `x_k.erase(std::unique(x_k.begin(), x_k.end()), x_k.end());` on the writable vector `k`.
theorem dedup_stepM (mv : MV) (k : Nat) (hk : k < mv.nv) (hwr : mv.wV k = true) (hfl : mv.flag k = true)
    {vv : Nat → List Int} {bb : Nat → Buffer Value} {wk : Nat} (S : NState) (ps : PS)
    {B sc SPB TPB W : Nat} (qs : QS S [] B sc ps.mem ps.bs (slN mv.nv ps.bs.length)) (fw : FWM mv vv bb wk S.frame)
    (cq : Cq SPB TPB W S)
    (cap : liveS S+3 ≤ SPB) (space : mv.L0+1 ≤ TPB) :
    ∃ t, (NStmt.dedupVec (.local k) (mv.ty k)).run S = some ⟨t,none,false⟩ ∧
      QS t [] B sc ps.mem ps.bs (slN mv.nv ps.bs.length) ∧
      FWM mv (upd vv k (uniqAdj (vv k)))
        (upd bb k {bb k with items := (uniqAdj (vv k)).map Value.integer, epoch := (bb k).epoch+1})
        (wk + ((vv k).length + (vv k).length)) t.frame ∧
      Cq SPB TPB (W+3) t := by
  have hs : S.vectorSlot k = some k := vectorSlot_N qs.slots hk
  have fbind : S.frame.bindings[k]? = some (flatBinding (mv.R k) (mv.ty k) (mv.vsc k)) := by
    rw [fw.bindings, bind_get mv k hk]
    simp [bindOf, flatBinding, hwr]
  have hints : (bb k).items.mapM Value.intOf = some (vv k) := by
    rw [fw.items k hk]; exact mapM_integer (vv k)
  obtain ⟨t,run,tf,tsl,tsc,tm,tb,tbase,gw1,gw2,gp1,gp2,gq1,gq2⟩ := dedup_flat_stmtE S k k (mv.R k) (mv.vsc k) (mv.ty k) (bb k) (vv k)
    hs fbind fw.valid (fw.vtag k hk) (fw.vfound k hk) fw.lengths (by rw [fw.flagR k hk, hfl]) hints
  have fw' := fw.replace k hk hwr _ {bb k with items := (uniqAdj (vv k)).map Value.integer, epoch := (bb k).epoch+1}
    ((vv k).length + (vv k).length) rfl rfl rfl rfl
    (dedup_valid (bb k) (mv.ty k) (vv k) (fw.bvalid k hk) hints)
    (by have := uniqAdj_length (vv k); have h := fw.small k hk; omega)
  rw [← tf] at fw'
  have storageT : t.frame.state.storage.peak = max S.frame.state.storage.peak
      (S.frame.state.liveSpace+((bb k).capacity+2-((bb k).capacity+1))-S.frame.state.storage.baseSpace) := by
    rw [tf]; simp [Frame.updated]
  have spB := cq.scalarPeak
  have stB := cq.storagePeak
  have opB := cq.outerPeak
  have liveS0 := fw.live
  have eS : (fx SPB TPB).SPB = SPB := rfl
  have eT : (fx SPB TPB).TPB = TPB := rfl
  rw [eS] at spB opB
  rw [eT] at stB opB
  refine ⟨t,run,⟨?_,?_,?_,?_,?_⟩,fw',?_⟩
  · rw [tsl]; exact qs.slots
  · rw [tm]; exact qs.memory
  · rw [tb]; exact qs.bindings
  · rw [tbase]; exact qs.base
  · rw [tsc]; exact qs.scope
  · refine ⟨?_,?_,?_,?_⟩
    · have := cq.work; omega
    · show t.scalars.peak ≤ SPB
      omega
    · show t.frame.state.storage.peak ≤ TPB
      rw [storageT]; omega
    · show t.peak ≤ SPB + TPB
      omega


-- ===== the pure executor and its soundness (ported from VecWrite) =====
def WrM (w : Nat → Bool) : Command → Bool
  | .primitive (.declare _ _ e) => true
  | .primitive (.assign _ _ e) => true
  | .primitive (.ret e) => true
  | .primitive (.check e) => true
  | .primitive (.write (.local k) _ _ _) => w k
  | .primitive (.sortVec (.local k) _) => w k
  | .primitive (.dedupVec (.local k) _) => w k
  | .primitive .skip => true
  | .sequence a b => WrM w a && WrM w b
  | .scope body => WrM w body
  | .branch c y n => WrM w y && WrM w n
  | .whileLoop c b => WrM w b
  | _ => false

structure PRM where
  ps : PS
  vv : Nat → List Int
  ret : Option Int
  cost : Nat
  need : Nat
  wk : Nat

def pstmtM (mv : MV) : NStmt → PS → (Nat → List Int) → Option PRM
  | .declare ty w e, ps, vv => do
      let v ← vdenM mv vv (penvN mv.nv ps) e
      let v' ← ty.convert v
      some ⟨⟨ps.mem ++ [⟨ty,v'⟩],ps.bs ++ [⟨ps.mem.length,w⟩]⟩,vv,none,(vwp e).1+1,ps.mem.length+ps.bs.length+(vwp e).2+4,0⟩
  | .assign s ty e, ps, vv => do
      let slot := s - mv.nv
      let v ← vdenM mv vv (penvN mv.nv ps) e
      let b ← ps.bs[slot]?
      let c ← ps.mem[b.address]?
      if mv.nv ≤ s ∧ c.type = ty ∧ ty.valid c.value = true ∧ b.writable = true then do
        let v' ← ty.convert v
        some ⟨⟨ps.mem.set b.address ⟨ty,v'⟩,ps.bs⟩,vv,none,(vwp e).1+1,ps.mem.length+ps.bs.length+(vwp e).2+2,0⟩
      else none
  | .ret e, ps, vv => do
      let v ← vdenM mv vv (penvN mv.nv ps) e
      some ⟨ps,vv,some v,(vwp e).1+1,ps.mem.length+ps.bs.length+(vwp e).2+2,0⟩
  | .check e, ps, vv => do
      let v ← vdenM mv vv (penvN mv.nv ps) e
      if v ≠ 0 then some ⟨ps,vv,none,(vwp e).1+1,ps.mem.length+ps.bs.length+(vwp e).2+2,0⟩ else none
  | .write (.local k) ty iE vE, ps, vv => do
      let x ← vdenM mv vv (penvN mv.nv ps) vE
      let p ← vdenM mv vv (penvN mv.nv ps) iE
      if k < mv.nv ∧ ty = mv.ty k ∧ 0 ≤ p ∧ p.toNat < (vv k).length ∧ (mv.ty k).valid x = true then
        some ⟨ps,upd vv k ((vv k).set p.toNat x),none,(vwp vE).1+(vwp iE).1+3,
          ps.mem.length+ps.bs.length+iE.nodes+vE.nodes+(vwp vE).2+(vwp iE).2+5,1⟩
      else none
  | .sortVec (.local k) ty, ps, vv =>
      if k < mv.nv ∧ ty = mv.ty k then
        some ⟨ps,upd vv k ((vv k).mergeSort (fun x y => decide (x ≤ y))),none,3,ps.mem.length+ps.bs.length+3,
          Proofs.StlContracts.sortComparisons (vv k).length + (vv k).length⟩
      else none
  | .dedupVec (.local k) ty, ps, vv =>
      if k < mv.nv ∧ ty = mv.ty k then
        some ⟨ps,upd vv k (uniqAdj (vv k)),none,3,ps.mem.length+ps.bs.length+3,(vv k).length+(vv k).length⟩
      else none
  | .skip, ps, vv => some ⟨ps,vv,none,0,ps.mem.length+ps.bs.length,0⟩
  | _, _, _ => none

theorem pstmtM_write_inv (mv : MV) (container : Container) (ty : Ty) (iE vE : NExpr) (ps : PS) (vv : Nat → List Int) (r : PRM)
    (h : pstmtM mv (.write container ty iE vE) ps vv = some r) :
    r.ps = ps ∧ r.need = ps.mem.length+ps.bs.length+iE.nodes+vE.nodes+(vwp vE).2+(vwp iE).2+5 := by
  cases container with
  | «local» k =>
    simp only [pstmtM, Bind.bind, Option.bind] at h
    cases h1 : vdenM mv vv (penvN mv.nv ps) vE with
    | none => simp [h1] at h
    | some x =>
      simp only [h1] at h
      cases h2 : vdenM mv vv (penvN mv.nv ps) iE with
      | none => simp [h2] at h
      | some p =>
        simp only [h2] at h
        by_cases ok : k < mv.nv ∧ ty = mv.ty k ∧ 0 ≤ p ∧ p.toNat < (vv k).length ∧ (mv.ty k).valid x = true
        · rw [if_pos ok] at h
          cases h
          exact ⟨rfl,rfl⟩
        · rw [if_neg ok] at h; simp at h
  | row _ _ _ => simp [pstmtM] at h


theorem pstmtM_sort_inv (mv : MV) (container : Container) (ty : Ty) (ps : PS) (vv : Nat → List Int) (r : PRM)
    (h : pstmtM mv (.sortVec container ty) ps vv = some r) :
    r.ps = ps ∧ r.need = ps.mem.length+ps.bs.length+3 := by
  cases container with
  | «local» k =>
    simp only [pstmtM] at h
    by_cases ok : k < mv.nv ∧ ty = mv.ty k
    · rw [if_pos ok] at h; cases h; exact ⟨rfl,rfl⟩
    · rw [if_neg ok] at h; simp at h
  | row _ _ _ => simp [pstmtM] at h

theorem pstmtM_dedup_inv (mv : MV) (container : Container) (ty : Ty) (ps : PS) (vv : Nat → List Int) (r : PRM)
    (h : pstmtM mv (.dedupVec container ty) ps vv = some r) :
    r.ps = ps ∧ r.need = ps.mem.length+ps.bs.length+3 := by
  cases container with
  | «local» k =>
    simp only [pstmtM] at h
    by_cases ok : k < mv.nv ∧ ty = mv.ty k
    · rw [if_pos ok] at h; cases h; exact ⟨rfl,rfl⟩
    · rw [if_neg ok] at h; simp at h
  | row _ _ _ => simp [pstmtM] at h

def pexecM (mv : MV) : Nat → Command → PS → (Nat → List Int) → Option PRM
  | _, .primitive st, ps, vv => pstmtM mv st ps vv
  | fu, .sequence a b, ps, vv => do
      let r ← pexecM mv fu a ps vv
      match r.ret with
      | some _ => some r
      | none => do
          let r2 ← pexecM mv fu b r.ps r.vv
          some ⟨r2.ps,r2.vv,r2.ret,r.cost+r2.cost,max r.need r2.need,r.wk+r2.wk⟩
  | fu, .scope body, ps, vv => do
      let r ← pexecM mv fu body ps vv
      some ⟨⟨r.ps.mem.take ps.mem.length,r.ps.bs.take ps.bs.length⟩,r.vv,r.ret,r.cost+1,r.need,r.wk⟩
  | fu, .branch c y n, ps, vv => do
      let v ← vdenM mv vv (penvN mv.nv ps) c
      if v = 0 then do
        let r ← pexecM mv fu n ps vv
        some ⟨r.ps,r.vv,r.ret,r.cost+(vwp c).1+1,max (ps.mem.length+ps.bs.length+(vwp c).2+2) r.need,r.wk⟩
      else do
        let r ← pexecM mv fu y ps vv
        some ⟨r.ps,r.vv,r.ret,r.cost+(vwp c).1+1,max (ps.mem.length+ps.bs.length+(vwp c).2+2) r.need,r.wk⟩
  | 0, .whileLoop _ _, _, _ => none
  | fu+1, .whileLoop c b, ps, vv => do
      let v ← vdenM mv vv (penvN mv.nv ps) c
      if v = 0 then some ⟨ps,vv,none,(vwp c).1+1,ps.mem.length+ps.bs.length+(vwp c).2+2,0⟩
      else do
        let r ← pexecM mv (fu+1) b ps vv
        match r.ret with
        | some _ => none
        | none => do
            let r2 ← pexecM mv fu (.whileLoop c b) r.ps r.vv
            some ⟨r2.ps,r2.vv,r2.ret,(vwp c).1+1+r.cost+r2.cost,
              max (ps.mem.length+ps.bs.length+(vwp c).2+2) (max r.need r2.need),r.wk+r2.wk⟩
  | _, _, _, _ => none
termination_by fu c => (fu, c)


theorem pexecM_ext (mv : MV) (w : Nat → Bool) : ∀ (c : Command), WrM w c = true → ∀ (fu : Nat) (ps : PS) (vv : Nat → List Int) (r : PRM), pexecM mv fu c ps vv = some r → Ext ps r.ps := by
  intro c
  induction c with
  | primitive st =>
    intro hs fu ps vv r hr
    cases st with
    | declare ty w e =>
      simp only [pexecM,pstmtM,Bind.bind,Option.bind] at hr
      cases h1 : vdenM mv vv (penvN mv.nv ps) e with
      | none => simp [h1] at hr
      | some v =>
        simp only [h1] at hr
        cases h2 : ty.convert v with
        | none => simp [h2] at hr
        | some v' =>
          simp only [h2] at hr
          cases hr
          refine ⟨by simp,?_,by simp,?_⟩
          · simp [List.take_left']
          · simp [List.take_left']
    | assign s ty e =>
      simp only [pexecM,pstmtM,Bind.bind,Option.bind] at hr
      cases h1 : vdenM mv vv (penvN mv.nv ps) e with
      | none => simp [h1] at hr
      | some v =>
        simp only [h1] at hr
        cases h2 : ps.bs[s - mv.nv]? with
        | none => simp [h2] at hr
        | some b =>
          simp only [h2] at hr
          cases h3 : ps.mem[b.address]? with
          | none => simp [h3] at hr
          | some c =>
            simp only [h3] at hr
            by_cases ok : mv.nv ≤ s ∧ c.type = ty ∧ ty.valid c.value = true ∧ b.writable = true
            · simp only [ok,and_self,if_true] at hr
              cases h4 : ty.convert v with
              | none => simp [h4] at hr
              | some v' =>
                simp only [h4] at hr
                cases hr
                refine ⟨Nat.le_refl _,List.take_length,by simp,?_⟩
                have hl : (ps.mem.set b.address ⟨ty,v'⟩).take ps.mem.length = ps.mem.set b.address ⟨ty,v'⟩ :=
                  List.take_of_length_le (by simp)
                show ((ps.mem.set b.address ⟨ty,v'⟩).take ps.mem.length).map Cell.type = ps.mem.map Cell.type
                rw [hl]
                exact map_type_set_gen ps.mem b.address c ty v' h3 ok.2.1
            · simp [ok] at hr
    | ret e =>
      simp only [pexecM,pstmtM,Bind.bind,Option.bind] at hr
      cases h1 : vdenM mv vv (penvN mv.nv ps) e with
      | none => simp [h1] at hr
      | some v => simp only [h1] at hr; cases hr; exact Ext.refl _
    | check e =>
      simp only [pexecM,pstmtM,Bind.bind,Option.bind] at hr
      cases h1 : vdenM mv vv (penvN mv.nv ps) e with
      | none => simp [h1] at hr
      | some v =>
        simp only [h1] at hr
        by_cases nz : v ≠ 0
        · simp [nz] at hr; cases hr; exact Ext.refl _
        · simp [nz] at hr
    | skip => simp only [pexecM,pstmtM] at hr; cases hr; exact Ext.refl _
    | write container ty iE vE =>
      rw [pexecM] at hr
      obtain ⟨h1,_⟩ := pstmtM_write_inv _ _ _ _ _ _ _ _ hr
      rw [h1]; exact Ext.refl _
    | sortVec container ty =>
      rw [pexecM] at hr
      obtain ⟨h1,_⟩ := pstmtM_sort_inv _ _ _ _ _ _ hr
      rw [h1]; exact Ext.refl _
    | dedupVec container ty =>
      rw [pexecM] at hr
      obtain ⟨h1,_⟩ := pstmtM_dedup_inv _ _ _ _ _ _ hr
      rw [h1]; exact Ext.refl _
    | _ => simp [pexecM,pstmtM] at hr
  | sequence a b iha ihb =>
    intro hs fu ps vv r hr
    simp only [WrM,Bool.and_eq_true] at hs
    simp only [pexecM,Bind.bind,Option.bind] at hr
    cases h1 : pexecM mv fu a ps vv with
    | none => simp [h1] at hr
    | some r1 =>
      simp only [h1] at hr
      cases hret : r1.ret with
      | some v => simp only [hret] at hr; rw [← Option.some.inj hr]; exact iha hs.1 fu ps vv r1 h1
      | none =>
        simp only [hret] at hr
        cases h2 : pexecM mv fu b r1.ps r1.vv with
        | none => simp [h2] at hr
        | some r2 =>
          simp only [h2] at hr
          cases hr
          exact (iha hs.1 fu ps vv r1 h1).trans (ihb hs.2 fu r1.ps r1.vv r2 h2)
  | scope body ih =>
    intro hs fu ps vv r hr
    simp only [WrM,Bool.and_eq_true] at hs
    simp only [pexecM,Bind.bind,Option.bind] at hr
    cases h1 : pexecM mv fu body ps vv with
    | none => simp [h1] at hr
    | some r1 =>
      simp only [h1] at hr
      cases hr
      obtain ⟨l1,t1,m1,y1⟩ := ih hs fu ps vv r1 h1
      refine ⟨by simp; omega,?_,by simp; omega,?_⟩
      · simp [List.take_take,t1]
      · simp [List.take_take,y1]
  | branch c y n ihy ihn =>
    intro hs fu ps vv r hr
    simp only [WrM,Bool.and_eq_true] at hs
    simp only [pexecM,Bind.bind,Option.bind] at hr
    cases h1 : vdenM mv vv (penvN mv.nv ps) c with
    | none => simp [h1] at hr
    | some v =>
      simp only [h1] at hr
      by_cases z : v = 0
      · simp only [z,if_true] at hr
        cases h2 : pexecM mv fu n ps vv with
        | none => simp [h2] at hr
        | some r1 => simp only [h2] at hr; cases hr; exact ihn hs.2 fu ps vv r1 h2
      · simp only [z,if_false] at hr
        cases h2 : pexecM mv fu y ps vv with
        | none => simp [h2] at hr
        | some r1 => simp only [h2] at hr; cases hr; exact ihy hs.1 fu ps vv r1 h2
  | whileLoop cnd b ih =>
    intro hs fu
    simp only [WrM,Bool.and_eq_true] at hs
    induction fu with
    | zero => intro ps vv r hr; simp [pexecM] at hr
    | succ fu ihf =>
      intro ps vv r hr
      simp only [pexecM,Bind.bind,Option.bind] at hr
      cases h1 : vdenM mv vv (penvN mv.nv ps) cnd with
      | none => simp [h1] at hr
      | some v =>
        simp only [h1] at hr
        by_cases z : v = 0
        · simp only [z,if_true] at hr; cases hr; exact Ext.refl _
        · simp only [z,if_false] at hr
          cases h2 : pexecM mv (fu+1) b ps vv with
          | none => simp [h2] at hr
          | some r1 =>
            simp only [h2] at hr
            cases hret : r1.ret with
            | some _ => simp [hret] at hr
            | none =>
              simp only [hret] at hr
              cases h3 : pexecM mv fu (.whileLoop cnd b) r1.ps r1.vv with
              | none => simp [h3] at hr
              | some r2 =>
                simp only [h3] at hr
                cases hr
                exact (ih hs (fu+1) ps vv r1 h2).trans (ihf r1.ps r1.vv r2 h3)
  | _ => intro hs; simp [WrM] at hs





theorem pexecM_need (mv : MV) (w : Nat → Bool) : ∀ (c : Command), WrM w c = true → ∀ (fu : Nat) (ps : PS) (vv : Nat → List Int) (r : PRM), pexecM mv fu c ps vv = some r →
    r.ps.mem.length+r.ps.bs.length ≤ r.need := by
  intro c
  induction c with
  | primitive st =>
    intro hs fu ps vv r hr
    cases st with
    | declare ty w e =>
      simp only [pexecM,pstmtM,Bind.bind,Option.bind] at hr
      cases h1 : vdenM mv vv (penvN mv.nv ps) e with
      | none => simp [h1] at hr
      | some v =>
        simp only [h1] at hr
        cases h2 : ty.convert v with
        | none => simp [h2] at hr
        | some v' => simp only [h2] at hr; cases hr; simp; omega
    | assign s ty e =>
      simp only [pexecM,pstmtM,Bind.bind,Option.bind] at hr
      cases h1 : vdenM mv vv (penvN mv.nv ps) e with
      | none => simp [h1] at hr
      | some v =>
        simp only [h1] at hr
        cases h2 : ps.bs[s - mv.nv]? with
        | none => simp [h2] at hr
        | some b =>
          simp only [h2] at hr
          cases h3 : ps.mem[b.address]? with
          | none => simp [h3] at hr
          | some c =>
            simp only [h3] at hr
            by_cases ok : mv.nv ≤ s ∧ c.type = ty ∧ ty.valid c.value = true ∧ b.writable = true
            · simp only [ok,and_self,if_true] at hr
              cases h4 : ty.convert v with
              | none => simp [h4] at hr
              | some v' => simp only [h4] at hr; cases hr; simp; omega
            · simp [ok] at hr
    | ret e =>
      simp only [pexecM,pstmtM,Bind.bind,Option.bind] at hr
      cases h1 : vdenM mv vv (penvN mv.nv ps) e with
      | none => simp [h1] at hr
      | some v => simp only [h1] at hr; cases hr; simp; omega
    | check e =>
      simp only [pexecM,pstmtM,Bind.bind,Option.bind] at hr
      cases h1 : vdenM mv vv (penvN mv.nv ps) e with
      | none => simp [h1] at hr
      | some v =>
        simp only [h1] at hr
        by_cases nz : v ≠ 0
        · simp [nz] at hr; cases hr; simp; omega
        · simp [nz] at hr
    | skip => simp only [pexecM,pstmtM] at hr; cases hr; simp
    | write container ty iE vE =>
      rw [pexecM] at hr
      obtain ⟨h1,h2⟩ := pstmtM_write_inv _ _ _ _ _ _ _ _ hr
      rw [h1,h2]; omega
    | sortVec container ty =>
      rw [pexecM] at hr
      obtain ⟨h1,h2⟩ := pstmtM_sort_inv _ _ _ _ _ _ hr
      rw [h1,h2]; omega
    | dedupVec container ty =>
      rw [pexecM] at hr
      obtain ⟨h1,h2⟩ := pstmtM_dedup_inv _ _ _ _ _ _ hr
      rw [h1,h2]; omega
    | _ => simp [pexecM,pstmtM] at hr
  | sequence a b iha ihb =>
    intro hs fu ps vv r hr
    simp only [WrM,Bool.and_eq_true] at hs
    simp only [pexecM,Bind.bind,Option.bind] at hr
    cases h1 : pexecM mv fu a ps vv with
    | none => simp [h1] at hr
    | some r1 =>
      simp only [h1] at hr
      cases hret : r1.ret with
      | some v => simp only [hret] at hr; rw [← Option.some.inj hr]; exact iha hs.1 fu ps vv r1 h1
      | none =>
        simp only [hret] at hr
        cases h2 : pexecM mv fu b r1.ps r1.vv with
        | none => simp [h2] at hr
        | some r2 =>
          simp only [h2] at hr
          cases hr
          have := ihb hs.2 fu r1.ps r1.vv r2 h2
          simp; omega
  | scope body ih =>
    intro hs fu ps vv r hr
    simp only [WrM,Bool.and_eq_true] at hs
    simp only [pexecM,Bind.bind,Option.bind] at hr
    cases h1 : pexecM mv fu body ps vv with
    | none => simp [h1] at hr
    | some r1 =>
      simp only [h1] at hr
      cases hr
      have := ih hs fu ps vv r1 h1
      simp; omega
  | branch c y n ihy ihn =>
    intro hs fu ps vv r hr
    simp only [WrM,Bool.and_eq_true] at hs
    simp only [pexecM,Bind.bind,Option.bind] at hr
    cases h1 : vdenM mv vv (penvN mv.nv ps) c with
    | none => simp [h1] at hr
    | some v =>
      simp only [h1] at hr
      by_cases z : v = 0
      · simp only [z,if_true] at hr
        cases h2 : pexecM mv fu n ps vv with
        | none => simp [h2] at hr
        | some r1 => simp only [h2] at hr; cases hr; have := ihn hs.2 fu ps vv r1 h2; simp; omega
      · simp only [z,if_false] at hr
        cases h2 : pexecM mv fu y ps vv with
        | none => simp [h2] at hr
        | some r1 => simp only [h2] at hr; cases hr; have := ihy hs.1 fu ps vv r1 h2; simp; omega
  | whileLoop cnd b ih =>
    intro hs fu
    simp only [WrM,Bool.and_eq_true] at hs
    induction fu with
    | zero => intro ps vv r hr; simp [pexecM] at hr
    | succ fu ihf =>
      intro ps vv r hr
      simp only [pexecM,Bind.bind,Option.bind] at hr
      cases h1 : vdenM mv vv (penvN mv.nv ps) cnd with
      | none => simp [h1] at hr
      | some v =>
        simp only [h1] at hr
        by_cases z : v = 0
        · simp only [z,if_true] at hr; cases hr; simp; omega
        · simp only [z,if_false] at hr
          cases h2 : pexecM mv (fu+1) b ps vv with
          | none => simp [h2] at hr
          | some r1 =>
            simp only [h2] at hr
            cases hret : r1.ret with
            | some _ => simp [hret] at hr
            | none =>
              simp only [hret] at hr
              cases h3 : pexecM mv fu (.whileLoop cnd b) r1.ps r1.vv with
              | none => simp [h3] at hr
              | some r2 =>
                simp only [h3] at hr
                cases hr
                have := ihf r1.ps r1.vv r2 h3
                simp; omega
  | _ => intro hs; simp [WrM] at hs




abbrev QpostM (mv : MV) (r : PRM) (B sc : Nat) (SPB TPB W wk : Nat) (step : NStep) : Prop :=
  step.returned = r.ret.map Ret.scalar ∧ step.breaking = false ∧
  QS step.state [] B sc r.ps.mem r.ps.bs (slN mv.nv r.ps.bs.length) ∧
  (∃ bb', FWM mv r.vv bb' (wk+r.wk) step.state.frame) ∧
  Cq SPB TPB (W+r.cost) step.state

theorem soundM_prim (mv : MV) (w : Nat → Bool) (hw : ∀ k, w k = true → mv.wV k = true ∧ mv.flag k = true) (st : NStmt) (hs : WrM w (.primitive st) = true) (ps : PS) (vv : Nat → List Int) (r : PRM)
    (hr : pstmtM mv st ps vv = some r) {B sc SPB TPB W wk : Nat} {bb : Nat → Buffer Value} (S : NState)
    (qs : QS S [] B sc ps.mem ps.bs (slN mv.nv ps.bs.length)) (fw : FWM mv vv bb wk S.frame) (cq : Cq SPB TPB W S)
    (hB : B ≤ ps.mem.length) (hneed : r.need ≤ SPB+B) (space : mv.L0+1 ≤ TPB) :
    RunsTo (.primitive st) S (QpostM mv r B sc SPB TPB W wk) := by
  have eS : (fx SPB TPB).SPB = SPB := rfl
  have live := live_psN qs
  cases st with
  | declare ty w e =>
    simp only [pstmtM,Bind.bind,Option.bind] at hr
    cases h1 : vdenM mv vv (penvN mv.nv ps) e with
    | none => simp [h1] at hr
    | some v =>
      simp only [h1] at hr
      cases h2 : ty.convert v with
      | none => simp [h2] at hr
      | some v' =>
        simp only [h2] at hr
        cases hr
        obtain ⟨t0,ev⟩ := ev_vdenM mv e S ps v qs rfl fw h1
        have good := Ev.good ev
        obtain ⟨t,run,fr,qs',cq'⟩ := decl_stepG S t0 e ty w v v' _ _ qs cq (by simp at hneed; omega) ev.1 good
          (vwp_pos e) h2
        apply RunsTo.primitive run
        refine ⟨rfl,rfl,qs'.of_eq (by simp) (by simp) ?_,⟨bb,fw.of_eq fr⟩,cq'⟩
        simp [slN_succ]
  | assign s ty e =>
    simp only [pstmtM,Bind.bind,Option.bind] at hr
    cases h1 : vdenM mv vv (penvN mv.nv ps) e with
    | none => simp [h1] at hr
    | some v =>
      simp only [h1] at hr
      cases h2 : ps.bs[s - mv.nv]? with
      | none => simp [h2] at hr
      | some b =>
        simp only [h2] at hr
        cases h3 : ps.mem[b.address]? with
        | none => simp [h3] at hr
        | some c =>
          simp only [h3] at hr
          by_cases ok : mv.nv ≤ s ∧ c.type = ty ∧ ty.valid c.value = true ∧ b.writable = true
          · simp only [ok,and_self,if_true] at hr
            cases h4 : ty.convert v with
            | none => simp [h4] at hr
            | some v' =>
              simp only [h4] at hr
              cases hr
              have lt : s - mv.nv < ps.bs.length := (List.getElem?_eq_some_iff.mp h2).1
              obtain ⟨t0,ev⟩ := ev_vdenM mv e S ps v qs rfl fw h1
              have good := Ev.good ev
              have hsl : (slN mv.nv ps.bs.length)[s]? = some (.scalar (s - mv.nv)) := by
                have h := slN_get_scalar mv.nv ps.bs.length (s - mv.nv) lt
                rwa [show mv.nv + (s - mv.nv) = s by omega] at h
              obtain ⟨t,run,fr,qs',cq'⟩ := assign_stepG S t0 e s (s - mv.nv) ty v v' _ _ b c qs cq (by simp at hneed; omega)
                ev.1 good h4 hsl h2 (by simpa using h3) ok.2.1 ok.2.2.1 ok.2.2.2
                (cells' := ps.mem.set b.address ⟨ty,v'⟩) (by simp)
              apply RunsTo.primitive run
              exact ⟨rfl,rfl,qs',⟨bb,fw.of_eq fr⟩,cq'⟩
          · simp [ok] at hr
  | ret e =>
    simp only [pstmtM,Bind.bind,Option.bind] at hr
    cases h1 : vdenM mv vv (penvN mv.nv ps) e with
    | none => simp [h1] at hr
    | some v =>
      simp only [h1] at hr
      cases hr
      obtain ⟨u,ev⟩ := ev_vdenM mv e S ps v qs rfl fw h1
      have good := Ev.good ev
      have self := release_self good.1.1
      have run : (NStmt.ret e).run S = some ⟨u.charge 1 0,some (.scalar v),false⟩ := by
        simp [NStmt.run,ev.1,self]
      have cqU : Cq SPB TPB (W+(vwp e).1) u := cq.good good (by simp at hneed; omega)
      have cqC : Cq SPB TPB (W+(vwp e).1+1) (u.charge 1 0) :=
        cqU.good (Good.charge u 1 0) (by rw [liveS_core good.1]; simp at hneed; omega)
      apply RunsTo.primitive run
      exact ⟨rfl,rfl,qs.core (good.1.trans (core_charge u 1 0)),⟨bb,fw.of_eq (by simpa using good.1.1)⟩,cqC⟩
  | check e =>
    simp only [pstmtM,Bind.bind,Option.bind] at hr
    cases h1 : vdenM mv vv (penvN mv.nv ps) e with
    | none => simp [h1] at hr
    | some v =>
      simp only [h1] at hr
      by_cases nz : v ≠ 0
      · simp only [nz,ne_eq,not_false_eq_true,if_true] at hr
        cases hr
        obtain ⟨t0,ev⟩ := ev_vdenM mv e S ps v qs rfl fw h1
        obtain ⟨t,run,good⟩ := check_good_g e S t0 v _ _ ev.1 (Ev.good ev) nz
        apply RunsTo.primitive run
        refine ⟨rfl,rfl,qs.core good.1,⟨bb,fw.of_eq good.1.1⟩,?_⟩
        exact cq.good good (by simp at hneed; omega)
      · simp [nz] at hr
  | skip =>
    simp only [pstmtM] at hr
    cases hr
    apply RunsTo.skip
    exact ⟨rfl,rfl,qs,⟨bb,fw⟩,cq.mono (by omega)⟩
  | write container ty iE vE =>
    cases container with
    | «local» k =>
      simp only [pstmtM, Bind.bind, Option.bind] at hr
      cases h1 : vdenM mv vv (penvN mv.nv ps) vE with
      | none => simp [h1] at hr
      | some x =>
        simp only [h1] at hr
        cases h2 : vdenM mv vv (penvN mv.nv ps) iE with
        | none => simp [h2] at hr
        | some p =>
          simp only [h2] at hr
          by_cases ok : k < mv.nv ∧ ty = mv.ty k ∧ 0 ≤ p ∧ p.toNat < (vv k).length ∧ (mv.ty k).valid x = true
          · rw [if_pos ok] at hr
            cases hr
            obtain ⟨hk, hty, hp0, hp1, hxv⟩ := ok
            subst hty
            have hpn : ((p.toNat : Nat) : Int) = p := Int.toNat_of_nonneg hp0
            have vEv : ∀ u : NState, Core S u → ∃ t, Ev u vE t x [] (vwp vE).1 (vwp vE).2 :=
              fun u core => ev_vdenM mv vE u ps x (qs.core core) core.1 fw h1
            have idx : ∀ u : NState, Core S u → ∃ t, Ev u iE t ((p.toNat : Nat) : Int) [] (vwp iE).1 (vwp iE).2 := by
              intro u core
              rw [hpn]
              exact ev_vdenM mv iE u ps p (qs.core core) core.1 fw h2
            have cap : liveS S+iE.nodes+vE.nodes+(vwp vE).2+(vwp iE).2+5 ≤ SPB := by
              rw [live_psN qs]; simp at hneed; omega
            obtain ⟨hwv, hfl⟩ := hw k (by simpa [WrM] using hs)
            obtain ⟨t,run,qs',fw',cq'⟩ := write_stepM mv k hk hwv hfl S ps qs fw cq iE vE p.toNat x (vwp vE).1 (vwp vE).2 (vwp iE).1
              (vwp iE).2 vEv idx hp1 hxv cap space
            apply RunsTo.primitive run
            exact ⟨rfl,rfl,qs',⟨_,fw'⟩,cq'.mono (by dsimp only; omega)⟩
          · rw [if_neg ok] at hr; simp at hr
    | row _ _ _ => simp [pstmtM] at hr
  | sortVec container ty =>
    cases container with
    | «local» k =>
      simp only [pstmtM] at hr
      by_cases ok : k < mv.nv ∧ ty = mv.ty k
      · rw [if_pos ok] at hr
        cases hr
        obtain ⟨hk, hty⟩ := ok
        subst hty
        have cap : liveS S+3 ≤ SPB := by
          rw [live_psN qs]; simp at hneed; omega
        obtain ⟨hwv, hfl⟩ := hw k (by simpa [WrM] using hs)
        obtain ⟨t,run,qs',fw',cq'⟩ := sort_stepM mv k hk hwv hfl S ps qs fw cq cap space
        apply RunsTo.primitive run
        exact ⟨rfl,rfl,qs',⟨_,fw'⟩,cq'.mono (by dsimp only; omega)⟩
      · rw [if_neg ok] at hr; simp at hr
    | row _ _ _ => simp [pstmtM] at hr
  | dedupVec container ty =>
    cases container with
    | «local» k =>
      simp only [pstmtM] at hr
      by_cases ok : k < mv.nv ∧ ty = mv.ty k
      · rw [if_pos ok] at hr
        cases hr
        obtain ⟨hk, hty⟩ := ok
        subst hty
        have cap : liveS S+3 ≤ SPB := by
          rw [live_psN qs]; simp at hneed; omega
        obtain ⟨hwv, hfl⟩ := hw k (by simpa [WrM] using hs)
        obtain ⟨t,run,qs',fw',cq'⟩ := dedup_stepM mv k hk hwv hfl S ps qs fw cq cap space
        apply RunsTo.primitive run
        exact ⟨rfl,rfl,qs',⟨_,fw'⟩,cq'.mono (by dsimp only; omega)⟩
      · rw [if_neg ok] at hr; simp at hr
    | row _ _ _ => simp [pstmtM] at hr
  | _ => simp [WrM] at hs



theorem soundM (mv : MV) (w : Nat → Bool) (hw : ∀ k, w k = true → mv.wV k = true ∧ mv.flag k = true) : ∀ (c : Command), WrM w c = true → ∀ (fu : Nat) (ps : PS) (vv : Nat → List Int) (r : PRM), pexecM mv fu c ps vv = some r →
    ∀ {B sc SPB TPB W wk : Nat} {bb : Nat → Buffer Value} (S : NState), QS S [] B sc ps.mem ps.bs (slN mv.nv ps.bs.length) →
      FWM mv vv bb wk S.frame → Cq SPB TPB W S → B ≤ ps.mem.length → ps.mem.length+ps.bs.length ≤ SPB+B →
      r.need ≤ SPB+B → mv.sc ≤ sc → mv.L0+1 ≤ TPB →
      RunsTo c S (QpostM mv r B sc SPB TPB W wk) := by
  intro c
  induction c with
  | primitive st =>
    intro hs fu ps vv r hr B sc SPB TPB W wk bb S qs fw cq hB hlive hneed hsc hL
    exact soundM_prim mv w hw st hs ps vv r (by simpa [pexecM] using hr) S qs fw cq hB hneed hL
  | sequence a b iha ihb =>
    intro hs fu ps vv r hr B sc SPB TPB W wk bb S qs fw cq hB hlive hneed hsc hL
    simp only [WrM,Bool.and_eq_true] at hs
    simp only [pexecM,Bind.bind,Option.bind] at hr
    cases h1 : pexecM mv fu a ps vv with
    | none => simp [h1] at hr
    | some r1 =>
      simp only [h1] at hr
      cases hret : r1.ret with
      | some v =>
        simp only [hret] at hr
        have e := Option.some.inj hr
        rw [← e] at hneed ⊢
        apply RunsTo.sequence
        refine (iha hs.1 fu ps vv r1 h1 S qs fw cq hB hlive hneed hsc hL).mono ?_
        intro step post
        left
        exact ⟨Or.inl (by rw [post.1,hret]; rfl),post⟩
      | none =>
        simp only [hret] at hr
        cases h2 : pexecM mv fu b r1.ps r1.vv with
        | none => simp [h2] at hr
        | some r2 =>
          simp only [h2] at hr
          cases hr
          have ext := pexecM_ext mv w a hs.1 fu ps vv r1 h1
          have nd := pexecM_need mv w a hs.1 fu ps vv r1 h1
          apply RunsTo.sequence
          refine (iha hs.1 fu ps vv r1 h1 S qs fw cq hB hlive (by simp at hneed; omega) hsc hL).mono ?_
          intro step ⟨ret,brk,qs1,⟨bb1,fw1⟩,cq1⟩
          right
          refine ⟨by simpa [hret] using ret,brk,?_⟩
          have := ihb hs.2 fu r1.ps r1.vv r2 h2 step.state qs1 fw1 cq1 (Nat.le_trans hB ext.2.2.1)
            (by simp at hneed; omega) (by simp at hneed; omega) hsc hL
          refine this.mono ?_
          intro st2 ⟨a1,a2,a3,⟨bf,a4⟩,a5⟩
          exact ⟨a1,a2,a3,⟨bf,a4.wk_eq (by simp; omega)⟩,a5.mono (by simp; omega)⟩
  | scope body ih =>
    intro hs fu ps vv r hr B sc SPB TPB W wk bb S qs fw cq hB hlive hneed hsc hL
    simp only [WrM,Bool.and_eq_true] at hs
    simp only [pexecM,Bind.bind,Option.bind] at hr
    cases h1 : pexecM mv fu body ps vv with
    | none => simp [h1] at hr
    | some r1 =>
      simp only [h1] at hr
      cases hr
      have ext := pexecM_ext mv w body hs fu ps vv r1 h1
      obtain ⟨l1,t1,m1,y1⟩ := ext
      have eS : (fx SPB TPB).SPB = SPB := rfl
      have eT : (fx SPB TPB).TPB = TPB := rfl
      apply RunsTo.scope
      have qs' : QS (scopeUp S) [] B (sc+1) ps.mem ps.bs (slN mv.nv ps.bs.length) := qs.enter
      refine (ih hs fu ps vv r1 h1 (scopeUp S) qs' fw cq.enter hB hlive (by simp at hneed; omega) (by omega) hL).mono ?_
      intro inner ⟨ret,brk,qsI,⟨bbI,fwI⟩,cqI⟩
      have hscope : S.scope = sc := qs.scope
      have fits : S.scalars.memory.length ≤ inner.state.scalars.memory.length := by
        rw [qsI.memory,qs.memory]; simpa using m1
      have takeEq : inner.state.scalars.memory.take S.scalars.memory.length = r1.ps.mem.take ps.mem.length := by
        rw [qsI.memory,qs.memory]; simp
      have types : (inner.state.scalars.memory.take S.scalars.memory.length).map Cell.type =
          S.scalars.memory.map Cell.type := by
        rw [takeEq,qs.memory]; simpa using y1
      have notVec : ∀ owner element, inner.returned ≠ some (.vector owner element) := by
        intro owner element h
        rw [ret] at h
        cases hv : r1.ret <;> simp [hv] at h
      have leaveEq := leave_scalar S inner.state inner.returned notVec fits types fwI.valid
        (by rw [hscope]; exact fwI.fresh (by omega))
      refine ⟨S.left inner.state,leaveEq,ret,brk,?_,?_,?_⟩
      · refine ⟨?_,?_,?_,?_,?_⟩
        · rw [left_slots,qs.slots]
          have : (r1.ps.bs.take ps.bs.length) = ps.bs := t1
          simp only [this]
        · rw [left_memory,takeEq]; simp
        · rw [left_bindings,qs.bindings]
          have : (r1.ps.bs.take ps.bs.length) = ps.bs := t1
          simp only [this]
        · rw [left_baseMemory]; exact qs.base
        · rw [left_scope]; exact qs.scope
      · refine ⟨bbI, fwI.noop (by rw [left_state]; exact noopRetired_same _) (by rw [left_rootWritable]) ?_ ?_⟩
        · rw [left_state]; rfl
        · rw [left_frameBindings,fwI.bindings,fw.bindings]; exact List.take_length
      · have lengthTake : (inner.state.scalars.memory.take S.scalars.memory.length).length =
            S.scalars.memory.length := by
          rw [takeEq,qs.memory]; simp; omega
        have hl : inner.state.frame.state.liveSpace-inner.state.frame.state.storage.baseSpace ≤ TPB := by
          rw [fwI.live]; omega
        have := Cb.left cq cqI lengthTake (by rw [live_psN qs]; omega) hl
        exact this
  | branch cnd y n ihy ihn =>
    intro hs fu ps vv r hr B sc SPB TPB W wk bb S qs fw cq hB hlive hneed hsc hL
    simp only [WrM,Bool.and_eq_true] at hs
    simp only [pexecM,Bind.bind,Option.bind] at hr
    have eS : (fx SPB TPB).SPB = SPB := rfl
    cases h1 : vdenM mv vv (penvN mv.nv ps) cnd with
    | none => simp [h1] at hr
    | some v =>
      simp only [h1] at hr
      obtain ⟨u,ev⟩ := ev_vdenM mv cnd S ps v qs rfl fw h1
      have good := Ev.good ev
      have hu := ev.1
      have self := release_self good.1.1
      have qsU : QS (u.charge 1 0) [] B sc ps.mem ps.bs (slN mv.nv ps.bs.length) :=
        qs.core (good.1.trans (core_charge u 1 0))
      have fwU : FWM mv vv bb wk (u.charge 1 0).frame := fw.of_eq (by simpa using good.1.1)
      have live := live_psN qs
      by_cases z : v = 0
      · simp only [z,if_true] at hr
        cases h2 : pexecM mv fu n ps vv with
        | none => simp [h2] at hr
        | some r1 =>
          simp only [h2] at hr
          cases hr
          have cqC : Cq SPB TPB (W+(vwp cnd).1+1) (u.charge 1 0) := by
            have c1 := cq.good good (by simp at hneed; omega)
            exact c1.good (Good.charge u 1 0) (by rw [liveS_core good.1]; simp at hneed; omega)
          apply RunsTo.branch (next := u) (value := v) hu
          rw [z,if_pos rfl,self]
          refine (ihn hs.2 fu ps vv r1 h2 (u.charge 1 0) qsU fwU cqC hB hlive (by simp at hneed; omega) hsc hL).mono ?_
          intro st ⟨a1,a2,a3,a4,a5⟩
          exact ⟨a1,a2,a3,a4,a5.mono (by simp; omega)⟩
      · simp only [z,if_false] at hr
        cases h2 : pexecM mv fu y ps vv with
        | none => simp [h2] at hr
        | some r1 =>
          simp only [h2] at hr
          cases hr
          have cqC : Cq SPB TPB (W+(vwp cnd).1+1) (u.charge 1 0) := by
            have c1 := cq.good good (by simp at hneed; omega)
            exact c1.good (Good.charge u 1 0) (by rw [liveS_core good.1]; simp at hneed; omega)
          apply RunsTo.branch (next := u) (value := v) hu
          rw [if_neg z,self]
          refine (ihy hs.1 fu ps vv r1 h2 (u.charge 1 0) qsU fwU cqC hB hlive (by simp at hneed; omega) hsc hL).mono ?_
          intro st ⟨a1,a2,a3,a4,a5⟩
          exact ⟨a1,a2,a3,a4,a5.mono (by simp; omega)⟩
  | whileLoop cnd b ih =>
    intro hs fu ps vv r hr B sc SPB TPB W wk bb S qs fw cq hB hlive hneed hsc hL
    simp only [WrM] at hs
    have eS : (fx SPB TPB).SPB = SPB := rfl
    refine RunsTo.whileGhost (fun g t => ∃ (ps1 : PS) (vv1 : Nat → List Int) (r1 : PRM) (k j : Nat) (bb1 : Nat → Buffer Value),
        pexecM mv g (.whileLoop cnd b) ps1 vv1 = some r1 ∧
        r.ps = r1.ps ∧ r.vv = r1.vv ∧ r.ret = r1.ret ∧ r.cost = k + r1.cost ∧ r.wk = j + r1.wk ∧ r1.need ≤ r.need ∧
        QS t [] B sc ps1.mem ps1.bs (slN mv.nv ps1.bs.length) ∧ FWM mv vv1 bb1 (wk+j) t.frame ∧ Cq SPB TPB (W+k) t ∧
        B ≤ ps1.mem.length ∧ ps1.mem.length+ps1.bs.length ≤ SPB+B) _ ?_ fu fu S (Nat.le_refl _)
      ⟨ps,vv,r,0,0,bb,hr,rfl,rfl,rfl,by omega,by omega,Nat.le_refl _,qs,fw,cq,hB,hlive⟩
    intro g t ⟨ps1,vv1,r1,k,j,bb1,hr1,hrps,hrvec,hrret,hrcost,hrwk,hrneed,qs1,fw1,cq1,hB1,hsz⟩
    cases g with
    | zero => simp [pexecM] at hr1
    | succ g' =>
      simp only [pexecM,Bind.bind,Option.bind] at hr1
      cases h1 : vdenM mv vv1 (penvN mv.nv ps1) cnd with
      | none => simp [h1] at hr1
      | some v =>
        simp only [h1] at hr1
        obtain ⟨u,ev⟩ := ev_vdenM mv cnd t ps1 v qs1 rfl fw1 h1
        have good := Ev.good ev
        have hu := ev.1
        have self := release_self good.1.1
        have qsU : QS (u.charge 1 0) [] B sc ps1.mem ps1.bs (slN mv.nv ps1.bs.length) :=
          qs1.core (good.1.trans (core_charge u 1 0))
        have fwU : FWM mv vv1 bb1 (wk+j) (u.charge 1 0).frame := fw1.of_eq (by simpa using good.1.1)
        have live := live_psN qs1
        refine ⟨u,v,hu,?_,?_⟩
        · intro z
          simp only [z,if_true] at hr1
          cases hr1
          rw [self]
          simp at hrneed hrps hrvec hrret hrcost hrwk
          have cqC : Cq SPB TPB (W+k+(vwp cnd).1+1) (u.charge 1 0) := by
            have c1 := cq1.good good (by omega)
            exact c1.good (Good.charge u 1 0) (by rw [liveS_core good.1]; omega)
          refine ⟨by rw [hrret]; rfl,rfl,?_,⟨bb1,?_⟩,?_⟩
          · rw [hrps]; exact qsU
          · rw [hrvec]
            exact fwU.wk_eq (by omega)
          · rw [hrcost]; exact cqC.mono (by omega)
        · intro z
          simp only [z,if_false] at hr1
          cases h2 : pexecM mv (g'+1) b ps1 vv1 with
          | none => simp [h2] at hr1
          | some rb =>
            simp only [h2] at hr1
            cases hret : rb.ret with
            | some _ => simp [hret] at hr1
            | none =>
              simp only [hret] at hr1
              cases h3 : pexecM mv g' (.whileLoop cnd b) rb.ps rb.vv with
              | none => simp [h3] at hr1
              | some r2 =>
                simp only [h3] at hr1
                cases hr1
                have ext := pexecM_ext mv w b hs (g'+1) ps1 vv1 rb h2
                have nd := pexecM_need mv w b hs (g'+1) ps1 vv1 rb h2
                simp at hrneed hrps hrvec hrret hrcost hrwk
                have cqC : Cq SPB TPB (W+k+(vwp cnd).1+1) (u.charge 1 0) := by
                  have c1 := cq1.good good (by omega)
                  exact c1.good (Good.charge u 1 0) (by rw [liveS_core good.1]; omega)
                rw [self]
                refine (ih hs (g'+1) ps1 vv1 rb h2 (u.charge 1 0) qsU fwU cqC hB1 hsz (by omega) hsc hL).mono ?_
                intro inner ⟨ret,brk,qsI,⟨bbI,fwI⟩,cqI⟩
                refine ⟨by rw [ret,hret]; rfl,brk,g',Nat.lt_succ_self _,rb.ps,rb.vv,r2,k+(vwp cnd).1+1+rb.cost,j+rb.wk,bbI,h3,?_,?_,?_,?_,?_,?_,qsI,?_,?_,?_,?_⟩
                · exact hrps
                · exact hrvec
                · exact hrret
                · omega
                · omega
                · omega
                · exact fwI.wk_eq (by omega)
                · have : W+k+(vwp cnd).1+1+rb.cost = W+(k+(vwp cnd).1+1+rb.cost) := by omega
                  rw [this] at cqI; exact cqI
                · exact Nat.le_trans hB1 ext.2.2.1
                · omega
  | _ => intro hs; simp [WrM] at hs


end Proofs.MultiVec
