import Proofs.QuotientSearch

namespace Proofs.QuotientBuild
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppMixedInvoke
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.FlatVectorStmt Proofs.QuotientFrame
open Proofs.QuotientSearch Proofs.EnumerateQuotientsMath
open Proofs.CppState (Cell)

-- Every owner of the extended forest is an old owner or the new root itself.
theorem declare_ctx (T next : Proofs.CppNestedVectorStore.State) (ty : Ty) (scope : Nat)
    (ran : T.declareVector ty scope = some next) (owner context : Nat)
    (h : next.forest.context owner = some context) :
    T.forest.context owner = some context ∨ (owner = T.forest.objects.length ∧ context = scope) := by
  have forestEq := declareVector_forest T ty scope next ran
  rw [forestEq] at h
  by_cases old : owner < T.forest.objects.length
  · have agree : ∀ i, i < T.forest.objects.length →
        (T.forest.declareRoot ty scope).lookup i = T.forest.lookup i :=
      fun i hi => declareRoot_old T.forest ty scope i hi
    rw [context_agree T.forest _ _ agree owner old] at h
    exact Or.inl h
  · by_cases isNew : owner = T.forest.objects.length
    · subst isNew
      have rooted : (T.forest.declareRoot ty scope).rootOwner T.forest.objects.length =
          some T.forest.objects.length := by
        rw [rootOwner_eq]
        simp [declareRoot_new,flatTag]
      simp [Forest.context,rooted,declareRoot_new,flatTag] at h
      exact Or.inr ⟨rfl,by omega⟩
    · have absent : (T.forest.declareRoot ty scope).lookup owner = none := by
        simp only [Forest.lookup]
        have : (T.forest.declareRoot ty scope).objects[owner]? = none :=
          List.getElem?_eq_none (by rw [declareRoot_length]; omega)
        simp [this]
      have ro : (T.forest.declareRoot ty scope).rootOwner owner = none := by
        rw [rootOwner_eq,absent]; rfl
      simp [Forest.context,ro] at h

theorem declare_live (s next : Proofs.CppNestedVectorStore.State) (ty : Ty) (scope : Nat)
    (ran : s.declareVector ty scope = some next) : next.liveSpace = s.liveSpace+1 := by
  obtain ⟨valid,_,_⟩ := declareVector_inv s ty scope next ran
  obtain ⟨lengths,_,_⟩ := wellFormed_parts s valid
  have forestEq := declareVector_forest s ty scope next ran
  have objLen := declareVector_objects_length s ty scope next ran
  have oldSpace : ∀ o, o < s.storage.objects.length → next.nodeSpace o = s.nodeSpace o := by
    intro o inside
    simp only [State.nodeSpace]
    rw [forestEq,declareRoot_old s.forest ty scope o (by omega),
      declareVector_storage_old s ty scope o next ran inside]
  have newSpace : next.nodeSpace s.storage.objects.length = 1 := by
    simp only [State.nodeSpace]
    have rl := declareRoot_new s.forest ty scope
    rw [lengths] at rl
    rw [forestEq,rl,declareVector_storage_new s ty scope next ran]
    simp [flatBuffer,flatTag]
  unfold State.liveSpace
  rw [objLen,List.range_succ,List.map_append,List.sum_append]
  have sumOld : ((List.range s.storage.objects.length).map next.nodeSpace).sum = s.liveSpace := by
    unfold State.liveSpace
    congr 1
    apply List.map_congr_left
    intro o member
    exact oldSpace o (List.mem_range.mp member)
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  rw [sumOld,newSpace]
  unfold State.liveSpace
  omega

abbrev pE : NExpr := .divrem u64 false (.variable u64 0) (.variable u64 1)
abbrev declP : NStmt := .declare u64 false pE

theorem pE_value (env : Nat → Ty → Option Int) (n K : Nat) (h0 : env 0 u64 = some (n : Int))
    (h1 : env 1 u64 = some (K : Int)) (hK : 0 < K) (hn : n < 18446744073709551616) :
    pE.denote env = some ((n / K : Nat) : Int) := by
  rw [den_divrem,den_variable,den_variable,h0,h1]
  simp only [Option.bind_some]
  exact div_value n K hK hn

theorem pE_scalar : pE.scalarOnly = true := by simp [pE,NExpr.scalarOnly]

-- `const uint64_t p = n / ok;`
theorem decl_p {P : List Cell} {B sc n K : Nat} {L0 T0 N scq SPB TPB W : Nat} (S : NState)
    (qs : QS S P B sc (cellsQ3 n K (K-1)) (bindsQ3 P.length) slotsQ3) (fa : FA S.frame L0 T0 scq N)
    (cq : Cq SPB TPB W S) (hB : B ≤ P.length) (spb : P.length+12-B+40 ≤ SPB)
    (hK : 0 < K) (hKs : K ≤ 4294967296) (hn : n < 18446744073709551616) :
    ∃ t, declP.run S = some ⟨t,none,false⟩ ∧ t.frame = S.frame ∧
      QS t P B sc (cellsQ4 n K (K-1) (n/K)) (bindsQ4 P.length) slotsQ4 ∧ Cq SPB TPB (W+4) t := by
  have env3 := envQ3 qs hn (by omega) (by omega)
  have liveS0 : liveS S = P.length+3-B+3 := by rw [qs.live_eq]; simp [cellsQ3,bindsQ3]
  have pn : n / K < 18446744073709551616 := by have := Nat.div_le_self n K; omega
  obtain ⟨t,run,fr,qsT,cqT⟩ := decl_step S pE u64 false ((n / K : Nat) : Int) ((n / K : Nat) : Int) qs cq
    (by simp [pE,NExpr.nodes]; omega) pE_scalar (pE_value _ n K env3.1 env3.2.1 hK hn)
    (Ty.convert_of_valid _ _ (u64_nat _ pn))
  exact ⟨t,run,fr,QS.to4 qsT,cqT.mono (by simp [pE,NExpr.nodes])⟩

-- Frame facts once the result vector's root exists.
structure FB (fr : Frame) (R sc L0 T0 : Nat) (b : Buffer Value) : Prop where
  valid : fr.state.wellFormed = true
  lengths : fr.rootWritable.length = fr.state.forest.objects.length
  tag : fr.state.forest.lookup R = some (flatTag u64 sc)
  found : fr.state.storage.lookup R = some b
  flag : fr.rootWritable[R]? = some true
  bindings : fr.bindings = [flatBinding R u64 sc]
  ctx : ∀ owner c, fr.state.forest.context owner = some c → c < sc ∨ (c = sc ∧ owner = R)
  live : fr.state.liveSpace = L0 + 1 + b.capacity
  work : fr.state.storage.work = T0
  limit : b.limit = CppVectorBindings.sizeLimit u64
  owner : b.owner = R
  count : fr.state.storage.objects.length = R + 1

def slotsQ6 : List Location := slotsQ4 ++ [.vector 0]

theorem declVec_phase {P : List Cell} {B sc n K lo p : Nat} {L0 T0 N SPB TPB W : Nat} (S : NState)
    (qs : QS S P B sc (cellsQ4 n K lo p) (bindsQ4 P.length) slotsQ4) (fa : FA S.frame L0 T0 sc N)
    (cq : Cq SPB TPB W S) (hfb : S.frame.bindings = []) (hB : B ≤ P.length)
    (spb : P.length+12-B+40 ≤ SPB) (hspace : L0 + 1 ≤ TPB) :
    ∃ t, (NStmt.declareVector u64 true).run S = some ⟨t,none,false⟩ ∧
      QS t P B sc (cellsQ4 n K lo p) (bindsQ4 P.length) slotsQ6 ∧
      FB t.frame S.frame.state.storage.objects.length sc L0 (T0+1)
        (flatBuffer u64 S.frame.state.storage.objects.length) ∧ Cq SPB TPB (W+1) t := by
  have eS : (fx SPB TPB).SPB = SPB := rfl
  have eT : (fx SPB TPB).TPB = TPB := rfl
  have supported : CppVectorBindings.supported u64 := by simp [CppVectorBindings.supported,u64]
  obtain ⟨t,next,declared,run,tf,sl,sc',me,bi,ba,wk,sp,pk⟩ := declare_vec_stmt S u64 supported fa.valid fa.lengths
  have liveS0 : liveS S = P.length+4-B+4 := by rw [qs.live_eq]; simp [cellsQ4,cellsQ3,bindsQ4,bindsQ3]
  obtain ⟨lengthsEq,_,_⟩ := wellFormed_parts S.frame.state fa.valid
  have forestEq := declareVector_forest S.frame.state u64 S.scope next declared
  have nextValid := declareVector_wellFormed S.frame.state u64 S.scope next declared
  have objLen := declareVector_objects_length S.frame.state u64 S.scope next declared
  have rwLen : S.frame.rootWritable.length = S.frame.state.storage.objects.length := by
    have := fa.lengths; omega
  have scopeEq : S.scope = sc := qs.scope
  have tfs : t.frame.state = next := by rw [tf]
  have tfr : t.frame.rootWritable = S.frame.rootWritable ++ [true] := by rw [tf]
  have tfb : t.frame.bindings = [flatBinding S.frame.state.storage.objects.length u64 S.scope] := by
    rw [tf]; simp [hfb]
  have liveN := declare_live S.frame.state next u64 S.scope declared
  have nextWork : next.storage.work = S.frame.state.storage.work+1 := by
    obtain ⟨_,_,rfl⟩ := declareVector_inv S.frame.state u64 S.scope next declared
    rfl
  have nextPeak : next.storage.peak = max S.frame.state.storage.peak
      (S.frame.state.liveSpace+1-S.frame.state.storage.baseSpace) := by
    obtain ⟨_,_,rfl⟩ := declareVector_inv S.frame.state u64 S.scope next declared
    rfl
  refine ⟨t,run,⟨?_,?_,?_,?_,?_⟩,⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_⟩
  · rw [sl,hfb,qs.slots]; simp [slotsQ6]
  · rw [me]; exact qs.memory
  · rw [bi]; exact qs.bindings
  · rw [ba]; exact qs.base
  · rw [sc']; exact qs.scope
  · rw [tfs]; exact nextValid
  · rw [tfr,tfs,forestEq,declareRoot_length]; simp [fa.lengths]
  · rw [tfs,forestEq,← lengthsEq,declareRoot_new,scopeEq]
  · rw [tfs]; exact declareVector_storage_new S.frame.state u64 S.scope next declared
  · rw [tfr]
    simp [List.getElem?_append_right,rwLen]
  · rw [tfb,scopeEq]
  · intro owner c h
    rw [tfs] at h
    rcases declare_ctx S.frame.state next u64 S.scope declared owner c h with old | ⟨ho,hc⟩
    · exact Or.inl (fa.strict owner c old)
    · exact Or.inr ⟨by omega,ho.trans lengthsEq⟩
  · rw [tfs,liveN,fa.live]; simp [flatBuffer]
  · rw [tfs,nextWork,fa.work]
  · rfl
  · rfl
  · rw [tfs]; omega
  · refine ⟨?_,?_,?_,?_⟩
    · have := cq.work; rw [wk]; show S.scalars.work + 1 ≤ W + 1; omega
    · have := cq.scalarPeak; rw [sp]; show max S.scalars.peak (liveS S) ≤ SPB; omega
    · have := cq.storagePeak
      rw [tfs,nextPeak]
      show max S.frame.state.storage.peak (S.frame.state.liveSpace+1-S.frame.state.storage.baseSpace) ≤ TPB
      have := fa.live
      omega
    · have a := cq.outerPeak
      have b : t.scalars.peak ≤ SPB := by have := cq.scalarPeak; rw [sp]; show max S.scalars.peak (liveS S) ≤ SPB; omega
      have c : next.storage.peak ≤ TPB := by
        have := cq.storagePeak; have := fa.live
        rw [nextPeak]
        show max S.frame.state.storage.peak (S.frame.state.liveSpace+1-S.frame.state.storage.baseSpace) ≤ TPB
        omega
      rw [pk]
      show max S.peak (t.scalars.peak + next.storage.peak) ≤ SPB + TPB
      omega

theorem nodeSpace_flat (T : Proofs.CppNestedVectorStore.State) (R sc : Nat) (b : Buffer Value)
    (tag : T.forest.lookup R = some (flatTag u64 sc)) (found : T.storage.lookup R = some b) :
    T.nodeSpace R = b.capacity + 1 := by
  simp [State.nodeSpace,tag,found,flatTag]

-- Replacing the root's buffer by another valid buffer.
theorem FB.update {fr : Frame} {R sc L0 T0 : Nat} {b : Buffer Value} (fb : FB fr R sc L0 T0 b)
    (res : CppVector.Result Value Unit) (owns : res.buffer.owner = R)
    (valid' : res.buffer.Valid (accepts (.integer u64)))
    (limit' : res.buffer.limit = CppVectorBindings.sizeLimit u64) :
    FB (fr.updated R b res) R sc L0 (T0+res.work) res.buffer := by
  have bound : R < fr.state.storage.objects.length := CppVectorStore.lookup_bound _ R b fb.found
  have lengthsEq : (fr.updated R b res).state.storage.objects.length = fr.state.storage.objects.length := by
    simp [Frame.updated]
  have forestEq : (fr.updated R b res).state.forest = fr.state.forest := rfl
  have other : ∀ o, o ≠ R → (fr.updated R b res).state.storage.lookup o = fr.state.storage.lookup o :=
    fun o ho => CppNestedOps.updated_lookup_other fr R o b res (by omega)
  have self := CppNestedOps.updated_lookup_self fr R b res bound
  have live := liveSpace_update fr.state (fr.updated R b res).state R bound lengthsEq forestEq other
  have n0 := nodeSpace_flat fr.state R sc b fb.tag fb.found
  have n1 := nodeSpace_flat (fr.updated R b res).state R sc res.buffer (by rw [forestEq]; exact fb.tag) self
  refine ⟨?_,?_,?_,self,?_,?_,?_,?_,?_,limit',owns,?_⟩
  · exact updated_wellFormed fr R b (flatTag u64 sc) res fb.valid fb.tag bound owns
      (by simp [payloadOK,flatTag,valid'])
  · simpa [Frame.updated] using fb.lengths
  · exact fb.tag
  · simpa [Frame.updated] using fb.flag
  · simpa [Frame.updated] using fb.bindings
  · intro owner c h
    exact fb.ctx owner c h
  · rw [n0,n1] at live
    have := fb.live
    omega
  · simp [Frame.updated,fb.work]
  · rw [lengthsEq]; exact fb.count

abbrev rE : NExpr := .binary u64 .sub (.binary u64 .add (.variable u64 3) (.variable u64 1)) lit1
abbrev reserveStmt : NStmt := .reserve (.local 4) u64 rE

theorem rE_scalar : rE.scalarOnly = true := by simp [rE,lit1,NExpr.scalarOnly]

theorem rE_value (env : Nat → Ty → Option Int) (p K : Nat) (h3 : env 3 u64 = some (p : Int))
    (h1 : env 1 u64 = some (K : Int)) (hK : 1 ≤ K) (small : p + K < 18446744073709551616) :
    rE.denote env = some ((p + K - 1 : Nat) : Int) := by
  have va := u64_add p K small
  have ca : u64.convert (binaryValue .add (p : Int) (K : Int)) = some ((p : Int) + (K : Int)) :=
    Ty.convert_of_valid _ _ va
  have e1 : ((p + K : Nat) : Int) = (p : Int) + (K : Int) := by omega
  have vs : u64.valid (((p : Int) + (K : Int)) - 1) = true := by
    have := u64_nat (p + K - 1) (by omega)
    have e : ((p + K - 1 : Nat) : Int) = ((p : Int) + (K : Int)) - 1 := by omega
    rw [e] at this
    exact this
  have cs : u64.convert (binaryValue .sub ((p : Int) + (K : Int)) 1) = some (((p : Int) + (K : Int)) - 1) :=
    Ty.convert_of_valid _ _ vs
  unfold rE
  simp only [den_binary,den_variable,lit1_value,h3,h1,Option.bind_some]
  rw [ca,Option.bind_some,cs]
  have e : ((p + K - 1 : Nat) : Int) = ((p : Int) + (K : Int)) - 1 := by omega
  rw [e]

theorem FB.bufferValid {fr : Frame} {R sc L0 T0 : Nat} {b : Buffer Value} (fb : FB fr R sc L0 T0 b) :
    b.Valid (accepts (.integer u64)) := by
  have object := object_runs fr R (.integer u64) b (flatTag u64 sc) fb.valid fb.found fb.tag rfl
  obtain ⟨_,_,valid,_,_⟩ := buffer_facts fr R u64 b _ object
  exact valid

theorem envQ6 {S : NState} {P : List Cell} {B sc n hi lo k : Nat}
    (qs : QS S P B sc (cellsQ4 n hi lo k) (bindsQ4 P.length) slotsQ6)
    (hn : n < 18446744073709551616) (hhi : hi < 18446744073709551616) (hlo : lo < 18446744073709551616)
    (hk : k < 18446744073709551616) :
    envOf S 0 u64 = some (n : Int) ∧ envOf S 1 u64 = some (hi : Int) ∧ envOf S 2 u64 = some (lo : Int) ∧
      envOf S 3 u64 = some (k : Int) :=
  ⟨envOf_at S 0 0 ⟨P.length,true⟩ u64 n (by simp [qs.slots,slotsQ6,slotsQ4,slotsQ3]) (by simp [qs.bindings,bindsQ4,bindsQ3])
      (by simp [qs.memory,cellsQ4,cellsQ3,qcell]) (u64_nat n hn),
   envOf_at S 1 1 ⟨P.length+1,true⟩ u64 hi (by simp [qs.slots,slotsQ6,slotsQ4,slotsQ3]) (by simp [qs.bindings,bindsQ4,bindsQ3])
      (by simp [qs.memory,cellsQ4,cellsQ3,qcell]) (u64_nat hi hhi),
   envOf_at S 2 2 ⟨P.length+2,true⟩ u64 lo (by simp [qs.slots,slotsQ6,slotsQ4,slotsQ3]) (by simp [qs.bindings,bindsQ4,bindsQ3])
      (by simp [qs.memory,cellsQ4,cellsQ3,qcell]) (u64_nat lo hlo),
   envOf_at S 3 3 ⟨P.length+3,false⟩ u64 k (by simp [qs.slots,slotsQ6,slotsQ4,slotsQ3]) (by simp [qs.bindings,bindsQ4,bindsQ3])
      (by simp [qs.memory,cellsQ4,cellsQ3,qcell]) (u64_nat k hk)⟩

theorem reserve_phase {P : List Cell} {B sc n K lo p R L0 T0 SPB TPB W : Nat} (S : NState) (b0 : Buffer Value)
    (qs : QS S P B sc (cellsQ4 n K lo p) (bindsQ4 P.length) slotsQ6) (fb : FB S.frame R sc L0 T0 b0)
    (items : b0.items = []) (cap0 : b0.capacity = 0) (cq : Cq SPB TPB W S) (hB : B ≤ P.length)
    (spb : P.length+12-B+40 ≤ SPB) (hK : 1 ≤ K) (hKs : K ≤ 4294967296) (hp : p ≤ 4294967297) (hlo : lo < K)
    (hn : n < 18446744073709551616) (hspace : L0 + (p+K-1) + 3 ≤ TPB) :
    ∃ t b1, reserveStmt.run S = some ⟨t,none,false⟩ ∧
      QS t P B sc (cellsQ4 n K lo p) (bindsQ4 P.length) slotsQ6 ∧
      FB t.frame R sc L0 (T0+1) b1 ∧ b1.items = [] ∧ b1.capacity = p+K-1 ∧ Cq SPB TPB (W+10) t := by
  have eS : (fx SPB TPB).SPB = SPB := rfl
  have eT : (fx SPB TPB).TPB = TPB := rfl
  have liveS0 : liveS S = P.length+4-B+4 := by rw [qs.live_eq]; simp [cellsQ4,cellsQ3,bindsQ4,bindsQ3]
  have env4 := envQ6 qs hn (by omega) (by omega) (by omega)
  have value := rE_value (envOf S) p K env4.2.2.2 env4.2.1 hK (by omega)
  have hslot : S.vectorSlot 4 = some 0 := by simp [NState.vectorSlot,qs.slots,slotsQ6,slotsQ4,slotsQ3]
  have valid0 := fb.bufferValid
  have limit : p + K - 1 ≤ b0.limit := by
    rw [fb.limit]; simp [CppVectorBindings.sizeLimit,u64]; omega
  obtain ⟨t,result,run,tf,cases,sl,sc',me,bi,ba,wl,wu,pl,pu,ql,qu⟩ := reserve_flat_stmt S 4 0 rE (p+K-1) R sc u64 b0
    rE_scalar value hslot (by rw [fb.bindings]; rfl) fb.valid fb.tag fb.found fb.lengths fb.flag limit
  have resultInfo : result.buffer.items = [] ∧ result.buffer.capacity = p+K-1 ∧ result.buffer.owner = R ∧
      result.buffer.Valid (accepts (.integer u64)) ∧ result.buffer.limit = CppVectorBindings.sizeLimit u64 ∧
      result.work = 1 ∧ result.peak ≤ p+K-1+2 := by
    rcases cases with ⟨grow,rfl⟩ | ⟨fits,rfl⟩
    · refine ⟨by simpa using items,rfl,fb.owner,CppVector.reserve_preserves_valid b0 _ _ valid0 limit grow,fb.limit,?_,?_⟩
      · simp [items]
      · simp [cap0]
    · refine ⟨items,by show b0.capacity = p+K-1; omega,fb.owner,valid0,fb.limit,rfl,?_⟩
      simp [cap0]
  obtain ⟨ri,rc,ro,rv,rl,rw',rp⟩ := resultInfo
  have fb' := fb.update result ro rv rl
  have tfs : t.frame = S.frame.updated R b0 result := tf
  have fbT : FB t.frame R sc L0 (T0+1) result.buffer := by rw [tfs]; simpa [rw'] using fb'
  have stPeak : t.frame.state.storage.peak ≤ TPB := by
    rw [tfs]
    have h1 := cq.storagePeak
    have h2 := fb.live
    have h3 : (S.frame.updated R b0 result).state.storage.peak = max S.frame.state.storage.peak
        (S.frame.state.liveSpace + (result.peak - (b0.capacity+1)) - S.frame.state.storage.baseSpace) := rfl
    rw [h3]
    omega
  have nodes : rE.nodes = 6 := by simp [rE,lit1,NExpr.nodes]
  have spP : t.scalars.peak ≤ SPB := by
    have := cq.scalarPeak
    rw [nodes] at pu
    omega
  refine ⟨t,result.buffer,run,⟨?_,?_,?_,?_,?_⟩,fbT,ri,rc,?_⟩
  · rw [sl]; exact qs.slots
  · rw [me]; exact qs.memory
  · rw [bi]; exact qs.bindings
  · rw [ba]; exact qs.base
  · rw [sc']; exact qs.scope
  · refine ⟨?_,spP,stPeak,?_⟩
    · have := cq.work; rw [nodes] at wu; omega
    · have := cq.outerPeak
      omega

theorem FB.noop {fr fr' : Frame} {R sc L0 T0 : Nat} {b : Buffer Value} (fb : FB fr R sc L0 T0 b)
    (hs : fr'.state = (noopRetired fr).state) (hrw : fr'.rootWritable = fr.rootWritable)
    (hb : fr'.bindings = fr.bindings) : FB fr' R sc L0 T0 b := by
  have same : SameObjects fr.state fr'.state := by rw [hs]; exact noopRetired_same fr
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,fb.limit,fb.owner,?_⟩
  · rw [same.wellFormed]; exact fb.valid
  · rw [hrw,same.1]; exact fb.lengths
  · rw [same.1]; exact fb.tag
  · rw [same.lookup]; exact fb.found
  · rw [hrw]; exact fb.flag
  · rw [hb]; exact fb.bindings
  · intro owner c h
    rw [same.1] at h
    exact fb.ctx owner c h
  · rw [same.liveSpace]; exact fb.live
  · rw [hs]; exact fb.work
  · rw [same.2.1]; exact fb.count

theorem envOf_scopeUp (S : NState) : envOf (scopeUp S) = envOf S := rfl

abbrev appendScope0 (e : NExpr) : Command :=
  .scope (.sequence (.primitive (.append (.local 4) u64 e)) (.primitive .skip))

theorem app_scope0 {P : List Cell} {B sq sc : Nat} {cells : List Cell} {binds : List CppState.Binding}
    {slots : List Location} {R L0 T0 SPB TPB W : Nat} (S : NState) (b : Buffer Value) (e : NExpr) (x : Int)
    (hsq : sc ≤ sq) (qs : QS S P B sq cells binds slots) (fb : FB S.frame R sc L0 T0 b) (cq : Cq SPB TPB W S)
    (hslot : slots[4]? = some (.vector 0)) (eScalar : e.scalarOnly = true)
    (eValue : e.denote (envOf S) = some x) (room : b.items.length < b.capacity) (accepted : u64.valid x = true)
    (capS : liveS S + e.nodes + 4 ≤ SPB) (hspace : L0 + b.capacity + 3 ≤ TPB) :
    RunsTo (appendScope0 e) S fun step => step.returned = none ∧ step.breaking = false ∧
      ∃ b', b'.items = b.items ++ [Value.integer x] ∧ b'.capacity = b.capacity ∧
        QS step.state P B sq cells binds slots ∧ FB step.state.frame R sc L0 (T0+2) b' ∧
        Cq SPB TPB (W+e.nodes+6) step.state := by
  have eS : (fx SPB TPB).SPB = SPB := rfl
  have eT : (fx SPB TPB).TPB = TPB := rfl
  have qs' : QS (scopeUp S) P B (sq+1) cells binds slots := qs.enter
  have cq' : Cq SPB TPB W (scopeUp S) := cq.enter
  have hv : (scopeUp S).vectorSlot 4 = some 0 := by simp [NState.vectorSlot,qs'.slots,hslot]
  have fb' : FB (scopeUp S).frame R sc L0 T0 b := fb
  have bufValid := fb.bufferValid
  obtain ⟨t,run,tf,tsl,tsc,tme,tbi,tba,wl,wu,pl,pu,ql,qu⟩ := append_flat_stmt (scopeUp S) 4 0 e x R sc u64 b
    eScalar (by rw [envOf_scopeUp]; exact eValue) hv (by rw [fb'.bindings]; rfl) fb'.valid fb'.tag fb'.found
    fb'.lengths fb'.flag room accepted
  have valid' : (appRes b x).buffer.Valid (accepts (.integer u64)) :=
    CppVector.append_preserves_valid b _ (.integer x) bufValid (by simpa [accepts] using accepted) room
  have fbT : FB t.frame R sc L0 (T0+(appRes b x).work) (appRes b x).buffer := by
    rw [tf]; exact fb'.update (appRes b x) fb.owner valid' fb.limit
  have liveT : t.frame.state.liveSpace = L0 + 1 + b.capacity := by rw [fbT.live]; simp [appRes]
  have stT : t.frame.state.storage.peak ≤ TPB := by
    rw [tf]
    have h1 := cq.storagePeak
    have h2 := fb.live
    have h3 : ((scopeUp S).frame.updated R b (appRes b x)).state.storage.peak = max S.frame.state.storage.peak
        (S.frame.state.liveSpace + ((appRes b x).peak - (b.capacity+1)) - S.frame.state.storage.baseSpace) := rfl
    rw [h3]
    simp only [appRes]
    omega
  have wu' : t.scalars.work ≤ S.scalars.work + e.nodes + 3 := wu
  have pu' : t.scalars.peak ≤ max S.scalars.peak (liveS S + e.nodes + 4) := pu
  have qu' : t.peak ≤ max S.peak (t.scalars.peak + t.frame.state.storage.peak) := qu
  have spT : t.scalars.peak ≤ SPB := by have := cq.scalarPeak; omega
  have cqT : Cq SPB TPB (W+e.nodes+3) t := by
    refine ⟨?_,spT,stT,?_⟩
    · have := cq.work; show t.scalars.work ≤ W+e.nodes+3; omega
    · have := cq.outerPeak
      show t.peak ≤ SPB + TPB
      omega
  apply RunsTo.scopeSimple
  apply RunsTo.seq
  apply RunsTo.primitive run
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.skip
  refine ⟨rfl,rfl,?_⟩
  obtain ⟨r,leaveEq,qsR,rs,rrw,rb,cqR⟩ := leave_core (outer := S) (inner := t) (extra := []) (binds' := binds)
    (slots' := slots) qs (by
      refine ⟨?_,?_,?_,?_,?_⟩
      · rw [tsl]; exact qs'.slots
      · rw [tme,List.append_nil]; exact qs'.memory
      · rw [tbi]; exact qs'.bindings
      · rw [tba]; exact qs'.base
      · rw [tsc]; exact qs'.scope) (by simp) fbT.valid
    (by
      intro owner h
      rcases fbT.ctx owner (sq+1) h with lt | ⟨eq,_⟩ <;> omega)
    (by rw [liveT]; omega) cq cqT (by omega)
  have fbR : FB r.frame R sc L0 (T0+2) (appRes b x).buffer := by
    refine fbT.noop (fr' := r.frame) (by rw [rs, ]) rrw ?_
    rw [rb, fbT.bindings, fb.bindings]; rfl
  refine ⟨r,leaveEq,rfl,rfl,(appRes b x).buffer,rfl,rfl,qsR,fbR,cqR.mono (by omega)⟩

def cells5 (n K lo p i : Nat) : List Cell := cellsQ4 n K lo p ++ [qcell i]
def binds5 (pl : Nat) : List CppState.Binding := bindsQ4 pl ++ [⟨pl+4,true⟩]
def slots7 : List Location := slotsQ6 ++ [.scalar 4]

theorem QS.to5 {S : NState} {P : List Cell} {B sc n K lo p i : Nat}
    (qs : QS S P B sc (cellsQ4 n K lo p ++ [⟨u64,(i : Int)⟩])
      (bindsQ4 P.length ++ [⟨P.length+(cellsQ4 n K lo p).length,true⟩])
      (slotsQ6 ++ [.scalar (bindsQ4 P.length).length])) :
    QS S P B sc (cells5 n K lo p i) (binds5 P.length) slots7 := by
  have a : P.length+(cellsQ4 n K lo p).length = P.length+4 := by simp [cellsQ4,cellsQ3]
  have b : (bindsQ4 P.length).length = 4 := by simp [bindsQ4,bindsQ3]
  rw [a] at qs
  rw [b] at qs
  exact qs

theorem envQ7 {S : NState} {P : List Cell} {B sc n K lo p i : Nat}
    (qs : QS S P B sc (cells5 n K lo p i) (binds5 P.length) slots7)
    (hn : n < 18446744073709551616) (hK : K < 18446744073709551616) (hp : p < 18446744073709551616)
    (hi : i < 18446744073709551616) :
    envOf S 0 u64 = some (n : Int) ∧ envOf S 1 u64 = some (K : Int) ∧ envOf S 3 u64 = some (p : Int) ∧
      envOf S 5 u64 = some (i : Int) := by
  refine ⟨envOf_at S 0 0 ⟨P.length,true⟩ u64 n (by simp [qs.slots,slots7,slotsQ6,slotsQ4,slotsQ3])
      (by simp [qs.bindings,binds5,bindsQ4,bindsQ3]) (by simp [qs.memory,cells5,cellsQ4,cellsQ3,qcell]) (u64_nat n hn),
    envOf_at S 1 1 ⟨P.length+1,true⟩ u64 K (by simp [qs.slots,slots7,slotsQ6,slotsQ4,slotsQ3])
      (by simp [qs.bindings,binds5,bindsQ4,bindsQ3]) (by simp [qs.memory,cells5,cellsQ4,cellsQ3,qcell]) (u64_nat K hK),
    envOf_at S 3 3 ⟨P.length+3,false⟩ u64 p (by simp [qs.slots,slots7,slotsQ6,slotsQ4,slotsQ3])
      (by simp [qs.bindings,binds5,bindsQ4,bindsQ3]) (by simp [qs.memory,cells5,cellsQ4,cellsQ3,qcell]) (u64_nat p hp),
    envOf_at S 5 4 ⟨P.length+4,true⟩ u64 i (by simp [qs.slots,slots7,slotsQ6,slotsQ4,slotsQ3])
      (by simp [qs.bindings,binds5,bindsQ4,bindsQ3]) (by simp [qs.memory,cells5,cellsQ4,cellsQ3,qcell]) (u64_nat i hi)⟩

theorem cells5_set (P : List Cell) (n K lo p i i' : Nat) :
    (P ++ cells5 n K lo p i).set (P.length+4) ⟨u64,(i' : Int)⟩ = P ++ cells5 n K lo p i' := by
  simp [cells5,cellsQ4,cellsQ3,qcell,List.set_append_right]

abbrev c1 : NExpr := .binary bl .le (.variable u64 5) (.variable u64 3)
abbrev inc1 : NExpr := .binary u64 .add (.variable u64 5) (.literal u64 1)
abbrev dec1 : NExpr := .binary u64 .sub (.variable u64 5) (.literal u64 1)
abbrev c2 : NExpr := .binary bl .ge (.variable u64 5) lit1
abbrev q2 : NExpr := .divrem u64 false (.variable u64 0) (.variable u64 5)

theorem blval (b : Bool) (c : Prop) [Decidable c] :
    bl.convert (if c then 1 else 0) = some (if c then 1 else 0) := by
  by_cases h : c
  · simp only [h,if_true]; exact Ty.convert_of_valid bl 1 (by simp [Ty.valid])
  · simp only [h,if_false]; exact Ty.convert_of_valid bl 0 (by simp [Ty.valid])

theorem c1_value (env : Nat → Ty → Option Int) (i p : Nat) (h5 : env 5 u64 = some (i : Int))
    (h3 : env 3 u64 = some (p : Int)) : c1.denote env = some (if i ≤ p then 1 else 0) := by
  unfold c1
  simp only [den_binary,den_variable,h5,h3,Option.bind_some,binaryValue]
  have : ((i : Int) ≤ (p : Int)) ↔ i ≤ p := by omega
  by_cases h : i ≤ p
  · have h' : (i : Int) ≤ (p : Int) := by omega
    simp only [h',h,if_true]; exact Ty.convert_of_valid bl 1 (by simp [Ty.valid])
  · have h' : ¬ (i : Int) ≤ (p : Int) := by omega
    simp only [h',h,if_false]; exact Ty.convert_of_valid bl 0 (by simp [Ty.valid])

theorem c2_value (env : Nat → Ty → Option Int) (i : Nat) (h5 : env 5 u64 = some (i : Int)) :
    c2.denote env = some (if 1 ≤ i then 1 else 0) := by
  unfold c2
  simp only [den_binary,den_variable,h5,lit1_value,Option.bind_some,binaryValue]
  by_cases h : 1 ≤ i
  · have h' : (i : Int) ≥ 1 := by omega
    simp only [h',h,if_true]; exact Ty.convert_of_valid bl 1 (by simp [Ty.valid])
  · have h' : ¬ (i : Int) ≥ 1 := by omega
    simp only [h',h,if_false]; exact Ty.convert_of_valid bl 0 (by simp [Ty.valid])

theorem lit64_value (env : Nat → Ty → Option Int) : (NExpr.literal u64 1).denote env = some 1 := by
  have b : u64.valid 1 = true := by simp [Ty.valid]
  simp [NExpr.denote,b]

theorem inc1_value (env : Nat → Ty → Option Int) (i : Nat) (h5 : env 5 u64 = some (i : Int))
    (small : i + 1 < 18446744073709551616) : inc1.denote env = some ((i + 1 : Nat) : Int) := by
  have v := u64_add i 1 small
  have e : ((i + 1 : Nat) : Int) = (i : Int) + ((1 : Nat) : Int) := by omega
  unfold inc1
  simp only [den_binary,den_variable,h5,lit64_value,Option.bind_some,binaryValue]
  rw [e]
  have : ((1 : Nat) : Int) = 1 := rfl
  rw [this] at v ⊢
  exact Ty.convert_of_valid _ _ v

theorem dec1_value (env : Nat → Ty → Option Int) (i : Nat) (h5 : env 5 u64 = some (i : Int))
    (pos : 1 ≤ i) (small : i < 18446744073709551616) : dec1.denote env = some ((i - 1 : Nat) : Int) := by
  have v : u64.valid ((i : Int) - 1) = true := by
    have := u64_nat (i - 1) (by omega)
    have e : ((i - 1 : Nat) : Int) = (i : Int) - 1 := by omega
    rw [e] at this
    exact this
  have e : ((i - 1 : Nat) : Int) = (i : Int) - 1 := by omega
  unfold dec1
  simp only [den_binary,den_variable,h5,lit64_value,Option.bind_some,binaryValue]
  rw [e]
  exact Ty.convert_of_valid _ _ v

theorem q2_value (env : Nat → Ty → Option Int) (n i : Nat) (h0 : env 0 u64 = some (n : Int))
    (h5 : env 5 u64 = some (i : Int)) (pos : 1 ≤ i) (hn : n < 18446744073709551616) :
    q2.denote env = some ((n / i : Nat) : Int) := by
  unfold q2
  rw [den_divrem,den_variable,den_variable,h0,h5]
  simp only [Option.bind_some]
  exact div_value n i pos hn

def vals (l : List Nat) : List Value := l.map fun v : Nat => Value.integer (v : Int)

theorem vals_append (a b : List Nat) : vals (a ++ b) = vals a ++ vals b := by simp [vals]
theorem vals_length (a : List Nat) : (vals a).length = a.length := by simp [vals]

abbrev body1 : Command := .sequence (appendScope0 (.variable u64 5))
  (.sequence (.primitive (.assign 5 u64 inc1)) (.primitive .skip))
abbrev while1 : Command := .whileLoop c1 body1

def L1Inv (P : List Cell) (B sq sc n K lo p R L0 T0 SPB TPB W : Nat) (g : Nat) (t : NState) : Prop :=
  ∃ i b, g = p+1-i ∧ 1 ≤ i ∧ i ≤ p+1 ∧ QS t P B sq (cells5 n K lo p i) (binds5 P.length) slots7 ∧
    b.items = vals (firstPart (i-1)) ∧ b.capacity = p+K-1 ∧
    FB t.frame R sc L0 (T0+2*(i-1)) b ∧ Cq SPB TPB (W+(i-1)*40) t

theorem loop1_run {P : List Cell} {B sq sc n K lo p R L0 T0 SPB TPB W : Nat} (S : NState) (i0 : Nat) (hsq : sc ≤ sq)
    (inv : L1Inv P B sq sc n K lo p R L0 T0 SPB TPB W (p+1-i0) S) (hB : B ≤ P.length)
    (spb : P.length+12-B+40 ≤ SPB) (hK : 1 ≤ K) (hKs : K ≤ 4294967296) (hp : p ≤ 4294967297)
    (hn : n < 18446744073709551616) (hspace : L0 + (p+K-1) + 3 ≤ TPB) :
    RunsTo while1 S fun step => step.returned = none ∧ step.breaking = false ∧
      ∃ b, QS step.state P B sq (cells5 n K lo p (p+1)) (binds5 P.length) slots7 ∧
        b.items = vals (firstPart p) ∧ b.capacity = p+K-1 ∧ FB step.state.frame R sc L0 (T0+2*p) b ∧
        Cq SPB TPB (W+p*40+8) step.state := by
  have eS : (fx SPB TPB).SPB = SPB := rfl
  have eT : (fx SPB TPB).TPB = TPB := rfl
  refine RunsTo.whileGhost (L1Inv P B sq sc n K lo p R L0 T0 SPB TPB W) _ ?_ (p+1) (p+1-i0) S (by omega) inv
  intro g t ⟨i,b,hg,hi1,hi2,qs,items,cap,fb,cq⟩
  have liveT : liveS t = P.length+5-B+5 := by rw [qs.live_eq]; simp [cells5,cellsQ4,cellsQ3,binds5,bindsQ4,bindsQ3]
  have env7 := envQ7 qs hn (by omega) (by omega) (by omega)
  have cv := c1_value (envOf t) i p env7.2.2.2 env7.2.2.1
  obtain ⟨u,hu,good⟩ := scalar_eval c1 t _ (by simp [c1,NExpr.scalarOnly]) cv
  have self := release_self good.1.1
  have liveU : liveS u = liveS t := liveS_core good.1
  have qsU : QS (u.charge 1 0) P B sq (cells5 n K lo p i) (binds5 P.length) slots7 :=
    qs.core (good.1.trans (core_charge u 1 0))
  have fbU : FB (u.charge 1 0).frame R sc L0 (T0+2*(i-1)) b := by simpa using (good.1.1 ▸ fb)
  have cqU : Cq SPB TPB (W+(i-1)*40+4) (u.charge 1 0) := by
    have capB : liveS t + c1.nodes ≤ SPB := by simp [c1,NExpr.nodes]; omega
    have c1' := cq.good good capB
    have capC : liveS u + 0 ≤ SPB := by omega
    have c2' := c1'.good (Good.charge u 1 0) capC
    exact c2'.mono (by simp [c1,NExpr.nodes])
  refine ⟨u,_,hu,?_,?_⟩
  · intro zero
    have notLe : ¬ i ≤ p := by intro h; simp [h] at zero
    have eq : i = p+1 := by omega
    subst eq
    rw [self]
    refine ⟨rfl,rfl,b,qsU,?_,cap,?_,?_⟩
    · simpa using items
    · simpa using fbU
    · have : (p+1-1)*40 = p*40 := by simp
      rw [this] at cqU
      exact cqU.mono (by omega)
  · intro nonzero
    have le : i ≤ p := by
      by_cases h : i ≤ p
      · exact h
      · simp [h] at nonzero
    rw [self]
    have room : b.items.length < b.capacity := by rw [items,vals_length,firstPart_length,cap]; omega
    have eval5 := (envQ7 qsU hn (by omega) (by omega) (by omega))
    have app := app_scope0 (u.charge 1 0) b (.variable u64 5) (i : Int) hsq qsU fbU cqU (by simp [slots7,slotsQ6,slotsQ4,slotsQ3])
      (var_scalar _ _) (by rw [den_variable]; exact eval5.2.2.2) room (u64_nat i (by omega))
      (by have : liveS (u.charge 1 0) = liveS t := (liveS_core (good.1.trans (core_charge u 1 0))); simp [NExpr.nodes]; omega)
      (by omega)
    apply RunsTo.seq
    refine app.mono ?_
    intro step ⟨nr,nb,b',items',cap',qsE,fbE,cqE⟩
    refine ⟨nr,nb,?_⟩
    have eval5' := envQ7 qsE hn (by omega) (by omega) (by omega)
    obtain ⟨t2,run2,fr2,qs2,cq2⟩ := assign_step step.state inc1 5 4 u64 ((i+1 : Nat) : Int) ((i+1 : Nat) : Int)
      ⟨P.length+4,true⟩ (qcell i) qsE cqE
      (by have : liveS step.state = liveS t := by rw [qsE.live_eq,qs.live_eq]
          simp [inc1,NExpr.nodes]; omega)
      (by simp [inc1,NExpr.scalarOnly]) (inc1_value _ i eval5'.2.2.2 (by omega))
      (Ty.convert_of_valid _ _ (u64_nat _ (by omega)))
      (by simp [slots7,slotsQ6,slotsQ4,slotsQ3]) (by simp [binds5,bindsQ4,bindsQ3])
      (by simp [cells5,cellsQ4,cellsQ3,qcell]) rfl (u64_nat i (by omega)) rfl (cells5_set P n K lo p i (i+1))
    apply RunsTo.seqSkip
    apply RunsTo.primitive run2
    refine ⟨rfl,rfl,rfl,rfl,p+1-(i+1),by omega,i+1,b',by omega,by omega,by omega,qs2,?_,cap'.trans cap,?_,?_⟩
    · have e1 : i + 1 - 1 = (i-1)+1 := by omega
      rw [e1,firstPart_succ,vals_append,items',items]
      have e2 : (i-1)+1 = i := by omega
      simp [vals,e2]
    · have e : T0 + 2*(i+1-1) = T0+2*(i-1)+2 := by omega
      rw [fr2,e]; exact fbE
    · refine cq2.mono ?_
      simp [inc1,NExpr.nodes]
      have : (i+1-1)*40 = (i-1)*40 + 40 := by omega
      omega

abbrev declI1 : NStmt := .declare u64 true lit1
abbrev loop1Cmd : Command := .scope (.sequence (.primitive declI1) (.sequence while1 (.primitive .skip)))

theorem lit1_scalar : lit1.scalarOnly = true := by simp [lit1,NExpr.scalarOnly]

theorem loop1_phase {P : List Cell} {B sc n K lo p R L0 T0 SPB TPB W : Nat} (S : NState) (b0 : Buffer Value)
    (qs : QS S P B sc (cellsQ4 n K lo p) (bindsQ4 P.length) slotsQ6) (fb : FB S.frame R sc L0 T0 b0)
    (items : b0.items = []) (cap0 : b0.capacity = p+K-1) (cq : Cq SPB TPB W S) (hB : B ≤ P.length)
    (spb : P.length+12-B+40 ≤ SPB) (hK : 1 ≤ K) (hKs : K ≤ 4294967296) (hp : p ≤ 4294967297)
    (hn : n < 18446744073709551616) (hspace : L0 + (p+K-1) + 3 ≤ TPB) :
    RunsTo loop1Cmd S fun step => step.returned = none ∧ step.breaking = false ∧
      ∃ b, QS step.state P B sc (cellsQ4 n K lo p) (bindsQ4 P.length) slotsQ6 ∧
        b.items = vals (firstPart p) ∧ b.capacity = p+K-1 ∧ FB step.state.frame R sc L0 (T0+2*p) b ∧
        Cq SPB TPB (W+p*40+20) step.state := by
  have eS : (fx SPB TPB).SPB = SPB := rfl
  have eT : (fx SPB TPB).TPB = TPB := rfl
  have liveS0 : liveS S = P.length+4-B+4 := by rw [qs.live_eq]; simp [cellsQ4,cellsQ3,bindsQ4,bindsQ3]
  have qs' : QS (scopeUp S) P B (sc+1) (cellsQ4 n K lo p) (bindsQ4 P.length) slotsQ6 := qs.enter
  have cq' : Cq SPB TPB W (scopeUp S) := cq.enter
  obtain ⟨t,run,fr,qsT0,cqT⟩ := decl_step (scopeUp S) lit1 u64 true ((1 : Nat) : Int) ((1 : Nat) : Int) qs' cq'
    (by simp [lit1,NExpr.nodes]; have : liveS (scopeUp S) = liveS S := rfl; omega) lit1_scalar
    (by have := lit1_value (envOf (scopeUp S)); simpa using this)
    (Ty.convert_of_valid _ _ (u64_nat 1 (by omega)))
  have qsT : QS t P B (sc+1) (cells5 n K lo p 1) (binds5 P.length) slots7 := QS.to5 qsT0
  have fbT : FB t.frame R sc L0 T0 b0 := by rw [fr]; exact fb
  apply RunsTo.scopeSimple
  apply RunsTo.seq
  apply RunsTo.primitive run
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.seqSkip
  have loop := loop1_run (sq := sc+1) (sc := sc) (W := W+lit1.nodes+1) t 1 (by omega) ⟨1,b0,by omega,Nat.le_refl _,by omega,qsT,by simp [items,firstPart,vals],cap0,
    by simpa using fbT,by simpa using cqT⟩ hB spb hK hKs hp hn hspace
  refine loop.mono ?_
  intro step ⟨nr,nb,b,qsE,itemsE,capE,fbE,cqE⟩
  refine ⟨nr,nb,?_⟩
  obtain ⟨r,leaveEq,qsR,rs,rrw,rb,cqR⟩ := leave_core (outer := S) (inner := step.state) (extra := [qcell (p+1)])
    (binds' := binds5 P.length) (slots' := slots7) qs qsE (by simp [cellsQ4,cellsQ3,qcell]) fbE.valid
    (by
      intro owner h
      rcases fbE.ctx owner (sc+1) h with lt | ⟨eq,_⟩ <;> omega)
    (by rw [fbE.live,capE]; omega) cq cqE (by omega)
  have fbR : FB r.frame R sc L0 (T0+2*p) b := by
    refine fbE.noop (fr' := r.frame) rs rrw ?_
    rw [rb, fbE.bindings, fb.bindings]; rfl
  exact ⟨rfl,rfl,r,leaveEq,rfl,rfl,b,qsR,itemsE,capE,fbR,cqR.mono (by simp [lit1,NExpr.nodes] <;> omega)⟩

abbrev body2 : Command := .sequence (appendScope0 q2)
  (.sequence (.primitive (.assign 5 u64 dec1)) (.primitive .skip))
abbrev while2 : Command := .whileLoop c2 body2
abbrev declI2 : NStmt := .declare u64 true (.binary u64 .sub (.variable u64 1) lit1)
abbrev loop2Cmd : Command := .scope (.sequence (.primitive declI2) (.sequence while2 (.primitive .skip)))

def L2Inv (P : List Cell) (B sq sc n K lo p R L0 T0 SPB TPB W : Nat) (g : Nat) (t : NState) : Prop :=
  ∃ i b, g = i ∧ i ≤ K-1 ∧ QS t P B sq (cells5 n K lo p i) (binds5 P.length) slots7 ∧
    b.items = vals (firstPart p ++ (secondPart n K).take (K-1-i)) ∧ b.capacity = p+K-1 ∧
    FB t.frame R sc L0 (T0+2*(K-1-i)) b ∧ Cq SPB TPB (W+(K-1-i)*40) t

theorem loop2_run {P : List Cell} {B sq sc n K lo p R L0 T0 SPB TPB W : Nat} (S : NState) (i0 : Nat) (hsq : sc ≤ sq)
    (inv : L2Inv P B sq sc n K lo p R L0 T0 SPB TPB W i0 S) (hB : B ≤ P.length)
    (spb : P.length+12-B+40 ≤ SPB) (hK : 1 ≤ K) (hKs : K ≤ 4294967296) (hp : p ≤ 4294967297)
    (hn : n < 18446744073709551616) (hspace : L0 + (p+K-1) + 3 ≤ TPB) (hpq : p = n / K) :
    RunsTo while2 S fun step => step.returned = none ∧ step.breaking = false ∧
      ∃ b, QS step.state P B sq (cells5 n K lo p 0) (binds5 P.length) slots7 ∧
        b.items = vals (qlist n K) ∧ b.capacity = p+K-1 ∧ FB step.state.frame R sc L0 (T0+2*(K-1)) b ∧
        Cq SPB TPB (W+(K-1)*40+8) step.state := by
  have eS : (fx SPB TPB).SPB = SPB := rfl
  have eT : (fx SPB TPB).TPB = TPB := rfl
  refine RunsTo.whileGhost (L2Inv P B sq sc n K lo p R L0 T0 SPB TPB W) _ ?_ i0 i0 S (Nat.le_refl _) inv
  intro g t ⟨i,b,hg,hi,qs,items,cap,fb,cq⟩
  have liveT : liveS t = P.length+5-B+5 := by rw [qs.live_eq]; simp [cells5,cellsQ4,cellsQ3,binds5,bindsQ4,bindsQ3]
  have env7 := envQ7 qs hn (by omega) (by omega) (by omega)
  have cv := c2_value (envOf t) i env7.2.2.2
  obtain ⟨u,hu,good⟩ := scalar_eval c2 t _ (by simp [c2,lit1,NExpr.scalarOnly]) cv
  have self := release_self good.1.1
  have liveU : liveS u = liveS t := liveS_core good.1
  have qsU : QS (u.charge 1 0) P B sq (cells5 n K lo p i) (binds5 P.length) slots7 :=
    qs.core (good.1.trans (core_charge u 1 0))
  have fbU : FB (u.charge 1 0).frame R sc L0 (T0+2*(K-1-i)) b := by simpa using (good.1.1 ▸ fb)
  have cqU : Cq SPB TPB (W+(K-1-i)*40+6) (u.charge 1 0) := by
    have capB : liveS t + c2.nodes ≤ SPB := by simp [c2,lit1,NExpr.nodes]; omega
    have c1' := cq.good good capB
    have capC : liveS u + 0 ≤ SPB := by omega
    have c2' := c1'.good (Good.charge u 1 0) capC
    exact c2'.mono (by simp [c2,lit1,NExpr.nodes])
  refine ⟨u,_,hu,?_,?_⟩
  · intro zero
    have notGe : ¬ 1 ≤ i := by intro h; simp [h] at zero
    have eq : i = 0 := by omega
    subst eq
    rw [self]
    refine ⟨rfl,rfl,b,qsU,?_,cap,?_,?_⟩
    · rw [items]; simp [qlist,secondPart_take_all,hpq]
    · simpa using fbU
    · exact cqU.mono (by omega)
  · intro nonzero
    have pos : 1 ≤ i := by
      by_cases h : 1 ≤ i
      · exact h
      · simp [h] at nonzero
    rw [self]
    have room : b.items.length < b.capacity := by
      rw [items,vals_length,cap]; simp [firstPart_length,secondPart]; omega
    have eval5 := (envQ7 qsU hn (by omega) (by omega) (by omega))
    have app := app_scope0 (u.charge 1 0) b q2 ((n / i : Nat) : Int) hsq qsU fbU cqU
      (by simp [slots7,slotsQ6,slotsQ4,slotsQ3])
      (by simp [q2,NExpr.scalarOnly]) (q2_value _ n i eval5.1 eval5.2.2.2 pos hn) room
      (u64_nat _ (by have := Nat.div_le_self n i; omega))
      (by have : liveS (u.charge 1 0) = liveS t := (liveS_core (good.1.trans (core_charge u 1 0))); simp [q2,NExpr.nodes]; omega)
      (by omega)
    apply RunsTo.seq
    refine app.mono ?_
    intro step ⟨nr,nb,b',items',cap',qsE,fbE,cqE⟩
    refine ⟨nr,nb,?_⟩
    have eval5' := envQ7 qsE hn (by omega) (by omega) (by omega)
    obtain ⟨t2,run2,fr2,qs2,cq2⟩ := assign_step step.state dec1 5 4 u64 ((i-1 : Nat) : Int) ((i-1 : Nat) : Int)
      ⟨P.length+4,true⟩ (qcell i) qsE cqE
      (by have : liveS step.state = liveS t := by rw [qsE.live_eq,qs.live_eq]
          simp [dec1,NExpr.nodes]; omega)
      (by simp [dec1,NExpr.scalarOnly]) (dec1_value _ i eval5'.2.2.2 pos (by omega))
      (Ty.convert_of_valid _ _ (u64_nat _ (by omega)))
      (by simp [slots7,slotsQ6,slotsQ4,slotsQ3]) (by simp [binds5,bindsQ4,bindsQ3])
      (by simp [cells5,cellsQ4,cellsQ3,qcell]) rfl (u64_nat i (by omega)) rfl (cells5_set P n K lo p i (i-1))
    apply RunsTo.seqSkip
    apply RunsTo.primitive run2
    refine ⟨rfl,rfl,rfl,rfl,i-1,by omega,i-1,b',by omega,by omega,qs2,?_,cap'.trans cap,?_,?_⟩
    · have t1 : K-1-i < K-1 := by omega
      have e1 : K-1-(i-1) = (K-1-i)+1 := by omega
      rw [e1,secondPart_take_succ n K (K-1-i) t1,← List.append_assoc,vals_append,items',items]
      have e3 : K-1-(K-1-i) = i := by omega
      simp [vals,e3]
    · have e : T0 + 2*(K-1-(i-1)) = T0+2*(K-1-i)+2 := by omega
      rw [fr2,e]; exact fbE
    · refine cq2.mono ?_
      simp [dec1,q2,NExpr.nodes]
      have : (K-1-(i-1))*40 = (K-1-i)*40 + 40 := by omega
      omega

theorem km1_value (env : Nat → Ty → Option Int) (K : Nat) (h1 : env 1 u64 = some (K : Int)) (hK : 1 ≤ K)
    (small : K < 18446744073709551616) :
    (NExpr.binary u64 .sub (.variable u64 1) lit1).denote env = some ((K - 1 : Nat) : Int) := by
  have v : u64.valid ((K : Int) - 1) = true := by
    have := u64_nat (K - 1) (by omega)
    have e : ((K - 1 : Nat) : Int) = (K : Int) - 1 := by omega
    rw [e] at this
    exact this
  have e : ((K - 1 : Nat) : Int) = (K : Int) - 1 := by omega
  simp only [den_binary,den_variable,h1,lit1_value,Option.bind_some,binaryValue]
  rw [e]
  exact Ty.convert_of_valid _ _ v

theorem loop2_phase {P : List Cell} {B sc n K lo p R L0 T0 SPB TPB W : Nat} (S : NState) (b0 : Buffer Value)
    (qs : QS S P B sc (cellsQ4 n K lo p) (bindsQ4 P.length) slotsQ6) (fb : FB S.frame R sc L0 T0 b0)
    (items : b0.items = vals (firstPart p)) (cap0 : b0.capacity = p+K-1) (cq : Cq SPB TPB W S)
    (hB : B ≤ P.length) (spb : P.length+12-B+40 ≤ SPB) (hK : 1 ≤ K) (hKs : K ≤ 4294967296)
    (hp : p ≤ 4294967297) (hlo : lo < K) (hn : n < 18446744073709551616) (hspace : L0 + (p+K-1) + 3 ≤ TPB)
    (hpq : p = n / K) :
    RunsTo loop2Cmd S fun step => step.returned = none ∧ step.breaking = false ∧
      ∃ b, QS step.state P B sc (cellsQ4 n K lo p) (bindsQ4 P.length) slotsQ6 ∧
        b.items = vals (qlist n K) ∧ b.capacity = p+K-1 ∧ FB step.state.frame R sc L0 (T0+2*(K-1)) b ∧
        Cq SPB TPB (W+(K-1)*40+20) step.state := by
  have eS : (fx SPB TPB).SPB = SPB := rfl
  have eT : (fx SPB TPB).TPB = TPB := rfl
  have liveS0 : liveS S = P.length+4-B+4 := by rw [qs.live_eq]; simp [cellsQ4,cellsQ3,bindsQ4,bindsQ3]
  have qs' : QS (scopeUp S) P B (sc+1) (cellsQ4 n K lo p) (bindsQ4 P.length) slotsQ6 := qs.enter
  have cq' : Cq SPB TPB W (scopeUp S) := cq.enter
  have env6 := envQ6 qs' hn (by omega) (by omega) (by omega)
  obtain ⟨t,run,fr,qsT0,cqT⟩ := decl_step (scopeUp S) (.binary u64 .sub (.variable u64 1) lit1) u64 true
    ((K - 1 : Nat) : Int) ((K - 1 : Nat) : Int) qs' cq'
    (by simp [lit1,NExpr.nodes]; have : liveS (scopeUp S) = liveS S := rfl; omega)
    (by simp [lit1,NExpr.scalarOnly]) (km1_value _ K env6.2.1 hK (by omega))
    (Ty.convert_of_valid _ _ (u64_nat _ (by omega)))
  have qsT : QS t P B (sc+1) (cells5 n K lo p (K-1)) (binds5 P.length) slots7 := QS.to5 qsT0
  have fbT : FB t.frame R sc L0 T0 b0 := by rw [fr]; exact fb
  apply RunsTo.scopeSimple
  apply RunsTo.seq
  apply RunsTo.primitive run
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.seqSkip
  have loop := loop2_run (sq := sc+1) (sc := sc) (W := W+(NExpr.binary u64 .sub (.variable u64 1) lit1).nodes+1)
    t (K-1) (by omega)
    ⟨K-1,b0,rfl,Nat.le_refl _,qsT,by simp [items],cap0,by simpa using fbT,by simpa using cqT⟩ hB spb hK hKs hp hn hspace hpq
  refine loop.mono ?_
  intro step ⟨nr,nb,b,qsE,itemsE,capE,fbE,cqE⟩
  refine ⟨nr,nb,?_⟩
  obtain ⟨r,leaveEq,qsR,rs,rrw,rb,cqR⟩ := leave_core (outer := S) (inner := step.state) (extra := [qcell 0])
    (binds' := binds5 P.length) (slots' := slots7) qs qsE (by simp [cellsQ4,cellsQ3,qcell]) fbE.valid
    (by
      intro owner h
      rcases fbE.ctx owner (sc+1) h with lt | ⟨eq,_⟩ <;> omega)
    (by rw [fbE.live,capE]; omega) cq cqE (by omega)
  have fbR : FB r.frame R sc L0 (T0+2*(K-1)) b := by
    refine fbE.noop (fr' := r.frame) rs rrw ?_
    rw [rb, fbE.bindings, fb.bindings]; rfl
  exact ⟨rfl,rfl,r,leaveEq,rfl,rfl,b,qsR,itemsE,capE,fbR,cqR.mono (by simp [lit1,NExpr.nodes] <;> omega)⟩

abbrev okE : NExpr := .cast u64 (.literal u64 4294967296)
abbrev ngE : NExpr := .cast u64 (.literal i32 0)
abbrev declOk : NStmt := .declare u64 true okE
abbrev declNg : NStmt := .declare u64 true ngE
abbrev retStmt : NStmt := .retVector 4

abbrev qbody : Command :=
  .sequence (.primitive declOk) (.sequence (.primitive declNg) (.sequence bsWhile
    (.sequence (.primitive declP) (.sequence (.primitive (.declareVector u64 true))
      (.sequence (.primitive reserveStmt) (.sequence loop1Cmd (.sequence loop2Cmd
        (.sequence (.primitive retStmt) (.primitive .skip)))))))))

theorem okE_value (env : Nat → Ty → Option Int) : okE.denote env = some 4294967296 := by
  have a : u64.valid 4294967296 = true := by simp [Ty.valid]
  simp [NExpr.denote,a,Ty.convert_of_valid _ _ a]

theorem ngE_value (env : Nat → Ty → Option Int) : ngE.denote env = some 0 := by
  have a : i32.valid 0 = true := by simp [Ty.valid]
  have b : u64.valid 0 = true := by simp [Ty.valid]
  simp [NExpr.denote,a,Ty.convert_of_valid _ _ b]

-- Existence and uniqueness of the search result.
theorem exists_K (n : Nat) (hn : n < 18446744073709551616) :
    ∃ K, 1 ≤ K ∧ K ≤ 4294967296 ∧ n ≤ K*(K+1) ∧ (K = 1 ∨ (K-1)*K < n) := by
  have base : n ≤ 4294967296*(4294967296+1) := by omega
  have key : ∀ k, 1 ≤ k → k ≤ 4294967296 → n ≤ k*(k+1) →
      ∃ K, 1 ≤ K ∧ K ≤ k ∧ n ≤ K*(K+1) ∧ (K = 1 ∨ (K-1)*K < n) := by
    intro k
    induction k with
    | zero => intro h; omega
    | succ k ih =>
      intro h1 h2 h3
      by_cases le : n ≤ k*(k+1)
      · by_cases kz : k = 0
        · subst kz; exact ⟨1,by omega,by omega,h3,Or.inl rfl⟩
        · obtain ⟨K,a,b,c,d⟩ := ih (by omega) (by omega) le
          exact ⟨K,a,by omega,c,d⟩
      · exact ⟨k+1,by omega,Nat.le_refl _,h3,Or.inr (by simp; omega)⟩
  obtain ⟨K,a,b,c,d⟩ := key 4294967296 (by omega) (Nat.le_refl _) base
  exact ⟨K,a,b,c,d⟩

theorem K_unique (n K1 K2 : Nat) (h1 : 1 ≤ K1) (h2 : 1 ≤ K2) (a1 : n ≤ K1*(K1+1))
    (m1 : K1 = 1 ∨ (K1-1)*K1 < n) (a2 : n ≤ K2*(K2+1)) (m2 : K2 = 1 ∨ (K2-1)*K2 < n) : K1 = K2 := by
  by_cases lt : K1 < K2
  · exfalso
    rcases m2 with rfl | m2
    · omega
    · have : K1*(K1+1) ≤ (K2-1)*K2 := Nat.mul_le_mul (by omega) (by omega)
      omega
  · by_cases gt : K2 < K1
    · exfalso
      rcases m1 with rfl | m1
      · omega
      · have : K2*(K2+1) ≤ (K1-1)*K1 := Nat.mul_le_mul (by omega) (by omega)
        omega
    · omega

theorem qbody_run {P : List Cell} {B sc n K L0 T0 N SPB TPB W : Nat} (S : NState)
    (qs : QS S P B sc [qcell n] [⟨P.length,true⟩] [.scalar 0]) (fa : FA S.frame L0 T0 sc N)
    (hfb : S.frame.bindings = []) (cq : Cq SPB TPB W S) (hB : B ≤ P.length) (spb : P.length+12-B+40 ≤ SPB)
    (hn : n < 18446744073709551616) (hK1 : 1 ≤ K) (hKs : K ≤ 4294967296) (hKn : n ≤ K*(K+1))
    (hKm : K = 1 ∨ (K-1)*K < n) (hspace : L0 + (n/K+K-1) + 3 ≤ TPB) :
    RunsTo qbody S fun step => step.returned = some (.vector S.frame.state.storage.objects.length (.integer u64)) ∧
      step.breaking = false ∧ ∃ t b, step.state = t.charge 1 0 ∧
        QS t P B sc (cellsQ4 n K (K-1) (n/K)) (bindsQ4 P.length) slotsQ6 ∧
        FB t.frame S.frame.state.storage.objects.length sc L0 (T0+1+1+2*(n/K)+2*(K-1)) b ∧
        b.items = vals (qlist n K) ∧ b.capacity = n/K+K-1 ∧ Cq SPB TPB (W+40*(n/K+K-1)+2400) t := by
  have eS : (fx SPB TPB).SPB = SPB := rfl
  have eT : (fx SPB TPB).TPB = TPB := rfl
  have liveS0 : liveS S = P.length+1-B+1 := by rw [qs.live_eq]; simp
  -- ok = 2^32
  obtain ⟨s1,run1,fr1,qs1,cq1⟩ := decl_step S okE u64 true 4294967296 4294967296 qs cq
    (by simp [okE,NExpr.nodes]; omega) (by simp [okE,NExpr.scalarOnly]) (okE_value _)
    (Ty.convert_of_valid _ _ (by simp [Ty.valid]))
  obtain ⟨s2,run2,fr2,qs2,cq2⟩ := decl_step s1 ngE u64 true 0 0 qs1 cq1
    (by have : liveS s1 = P.length+2-B+2 := by rw [qs1.live_eq]; simp
        simp [ngE,NExpr.nodes]; omega) (by simp [ngE,NExpr.scalarOnly]) (ngE_value _)
    (Ty.convert_of_valid _ _ (by simp [Ty.valid]))
  have qs3 : QS s2 P B sc (cellsQ3 n 4294967296 0) (bindsQ3 P.length) slotsQ3 := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · rw [qs2.slots]; simp [slotsQ3]
    · rw [qs2.memory]; simp [cellsQ3,qcell]
    · rw [qs2.bindings]; simp [bindsQ3]
    · exact qs2.base
    · exact qs2.scope
  have fa2 : FA s2.frame L0 T0 sc N := fa.of_eq (fr2.trans fr1)
  have hL : L0 ≤ TPB := by omega
  apply RunsTo.seq
  apply RunsTo.primitive run1
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.seq
  apply RunsTo.primitive run2
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.seq
  have bsOut := bs_loop (W0 := W+okE.nodes+1+ngE.nodes+1) s2 32
    ⟨Nat.le_refl _,4294967296,0,by simp,by omega,Nat.le_refl _,by omega,Or.inl rfl,qs3,fa2,by simpa using cq2⟩
    hB spb (Nat.le_refl _) hL hn
  refine bsOut.mono ?_
  intro st ⟨nr,nb,hi,lo,hlo,hhi,hnn,hlow,qs4,fa4,cq4⟩
  refine ⟨nr,nb,?_⟩
  have props : 1 ≤ hi ∧ (hi = 1 ∨ (hi-1)*hi < n) := by
    refine ⟨by omega,?_⟩
    rcases hlow with z | z
    · left; omega
    · right; subst hlo; simpa using z
  have eqK : hi = K := K_unique n hi K props.1 hK1 hnn props.2 hKn hKm
  subst eqK
  have lo' : lo = hi - 1 := by omega
  subst lo'
  have hp : n / hi ≤ 4294967297 := by
    have := Nat.div_le_of_le_mul hnn
    omega
  obtain ⟨s4,run4,fr4,qs5,cq5⟩ := decl_p st.state qs4 fa4 cq4 hB spb props.1 hKs hn
  have fa5 : FA s4.frame L0 T0 sc N := fa4.of_eq fr4
  apply RunsTo.seq
  apply RunsTo.primitive run4
  refine ⟨rfl,rfl,?_⟩
  obtain ⟨s5,run5,qs6,fb6,cq6⟩ := declVec_phase s4 qs5 fa5 cq5 fa5.bindings hB spb (by omega)
  rw [fa5.count] at fb6
  apply RunsTo.seq
  apply RunsTo.primitive run5
  refine ⟨rfl,rfl,?_⟩
  obtain ⟨s6,b1,run6,qs7,fb7,items7,cap7,cq7⟩ := reserve_phase s5 _ qs6 fb6 rfl rfl cq6 hB spb props.1 hKs hp
    (by omega) hn hspace
  apply RunsTo.seq
  apply RunsTo.primitive run6
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.seq
  have l1 := loop1_phase s6 b1 qs7 fb7 items7 cap7 cq7 hB spb props.1 hKs hp hn hspace
  refine l1.mono ?_
  intro st1 ⟨nr1,nb1,b2,qs8,items8,cap8,fb8,cq8⟩
  refine ⟨nr1,nb1,?_⟩
  apply RunsTo.seq
  have l2 := loop2_phase st1.state b2 qs8 fb8 items8 cap8 cq8 hB spb props.1 hKs hp (by omega) hn hspace rfl
  refine l2.mono ?_
  intro st2 ⟨nr2,nb2,b3,qs9,items9,cap9,fb9,cq9⟩
  refine ⟨nr2,nb2,?_⟩
  have hv : st2.state.vectorSlot 4 = some 0 := by simp [NState.vectorSlot,qs9.slots,slotsQ6,slotsQ4,slotsQ3]
  have run : retStmt.run st2.state = some ⟨st2.state.charge 1 0,some (.vector N (.integer u64)),false⟩ := by
    simp [NStmt.run,hv,fb9.bindings,flatBinding]
  apply RunsTo.sequence
  apply RunsTo.primitive run
  refine Or.inl ⟨Or.inl rfl,?_⟩
  refine ⟨by rw [fa.count],rfl,st2.state,b3,rfl,qs9,?_,items9,cap9,?_⟩
  · rw [fa.count]; exact fb9
  · refine cq9.mono ?_
    simp [okE,ngE,lit1,NExpr.nodes]
    omega

end Proofs.QuotientBuild
