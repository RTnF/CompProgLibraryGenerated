import Proofs.UfPathAmortized
import Proofs.UfConstructionWork

namespace Proofs.UfMethodAmortized
open Proofs.UfPathAmortized Proofs.UfClassInvariant Proofs.UfRootCall Proofs.UfFindCall Proofs.UfCompression
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.UfReceiverState
open Proofs.DoublingNested (i32)

theorem size_work_trace (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Represents s layout ps count rank) {a root : Nat} {nodes : List Nat}
    (trace : Trace ps a root nodes) :
    ∃ fuel out vec,
      Proofs.UnionFindCandidateInstance.UnionFind_size.callFuel fuel s
        (arguments layout ++ [.value (.literal i32 a)]) = .finished (out,.scalar ((component ps a).length : Int)) ∧
      Compressed ps vec a root ∧ Represents out layout vec count rank ∧
      out.work ≤ s.work+91*nodes.length+162 := by
  obtain ⟨buf,cb,nb,inv⟩ := represented
  have inside := trace.inside
  have av := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by have h := inv.math.length; omega)
  obtain ⟨init,fuel,out,r,w,vec,prep,ran,found,negative,compressed,forest,weights,post,ready,cells⟩ :=
    Proofs.UfSizeReady.size_call_ready s inv.ok cb count inv.countCell inv.writable ps (depth inv.math) (depth_forest inv.math) inv.math.weights
      inv.items inv.math.length inv.bufferValid inv.limit inv.owner (nExpr layout) (.literal i32 a) a
      rfl rfl rfl rfl inv.n_value (literal_value a av s) inside
  have same := root_unique compressed.reach trace.reaches compressed.root trace.root
  subst r
  have result := inv.math.size_value found negative
  rw [← component_eq_members ps a root compressed.reach ⟨w,found,negative⟩] at result
  rw [result] at ran
  have preserved := inv.readonly_transition out vec (inv.math.compressed compressed) compressed.length ready cells
  have scalarWork := post.scalarWork
  change out.scalars.work ≤ s.scalars.work+2+(90*depth inv.math a+160) at scalarWork
  have storageWork := post.storageWork
  simp only [depth_of_trace inv.math trace] at scalarWork storageWork
  refine ⟨fuel,out,vec,ran,compressed,preserved,?_⟩
  unfold NState.work
  omega



open Proofs.UfPotential Proofs.UfForestPotential Proofs.UfHistoricalRank

theorem size_amortized (s : NState) (layout : Layout) (ps : List Int) (count : Int)
    (rank rho : Nat → Nat) (represented : Represents s layout ps count rank)
    (history : History ps rho) (a : Nat) (inside : a < ps.length) :
    ∃ fuel out, ∃ root : Nat, ∃ vec,
      Proofs.UnionFindCandidateInstance.UnionFind_size.callFuel fuel s
        (arguments layout ++ [.value (.literal i32 a)]) =
          .finished (out,.scalar ((component ps a).length : Int)) ∧
      Compressed ps vec a root ∧ Represents out layout vec count rank ∧ History vec rho ∧
      out.work+91*forestPotential vec rho ≤
        s.work+91*forestPotential ps rho+344*(alpha ps.length+1) := by
  have valid : Valid ps count rank := by
    obtain ⟨buf,cb,nb,inv⟩ := represented
    exact inv.math
  obtain ⟨root,nodes,trace⟩ := trace_exists valid a inside
  obtain ⟨fuel,out,vec,ran,compressed,post,work⟩ := size_work_trace s layout ps count rank represented trace
  have potential := trace.forest_budget valid history compressed
  refine ⟨fuel,out,root,vec,ran,compressed,post,history_compressed history compressed,?_⟩
  omega

theorem Trace.length_le_rank {ps : List Int} {rank : Nat → Nat} {i root : Nat} {nodes : List Nat}
    (trace : Trace ps i root nodes) (forest : Forest ps rank) : nodes.length ≤ rank i := by
  induction trace with
  | done root value found negative => simp
  | step i p root nodes parent tail ih =>
    have edge := forest.decrease i (p : Int) parent (by omega)
    simp only [Int.toNat_natCast] at edge
    simp only [List.length_cons]
    omega

theorem depth_le_rank {ps : List Int} {groups : Int} {rank : Nat → Nat}
    (valid : Valid ps groups rank) (i : Nat) (inside : i < ps.length) : depth valid i ≤ rank i := by
  obtain ⟨root,nodes,trace⟩ := trace_exists valid i inside
  rw [depth_of_trace valid trace]
  exact Trace.length_le_rank trace valid.forest

open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecWrite
open Proofs.VecKitW Proofs.PowModStep Proofs.DoublingNested Proofs.PrefixSumsCall
open Proofs.UfRootCall Proofs.UfFindCall Proofs.UfCompression Proofs.UfInlineRoot Proofs.VecCapture
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore
open Proofs.CppNestedVectorBindings Proofs.CppNestedCall Proofs.CppNestedSim Proofs.CppNestedEval
open Proofs.CppNestedStmt
open Proofs.IntSim Proofs.CppNestedFacts
open Proofs.CppNestedRows
open Proofs.VecKit
open Proofs.QuotientFrame Proofs.DoublingCall Proofs.ScalarCall Proofs.ExtremaCall Proofs.VecWriteCall


open Proofs.UfFieldsSame

theorem same_body_paths (P : List Cell) (counter : CppState.Binding) (vec : List Int)
    (rank : Nat → Nat) (count : Int) (valid : Valid vec count rank) (length : vec.length < 2147483648)
    (a b : Nat) (ha : a < vec.length) (hb : b < vec.length) (fuel : Nat)
    (fa : rank a+2 ≤ fuel) (fb : rank b+2 ≤ fuel) :
    ∃ (out : PRW) (r1 r2 : Nat) (middle : List Int) (nodes1 nodes2 : List Nat),
      pexecW i32 fuel Proofs.UnionFindCandidateInstance.UnionFind_same.body (fields P counter vec.length a b) vec = some out ∧
      out.ret = some (if r1=r2 then 1 else 0) ∧
      Compressed vec middle a r1 ∧ Compressed middle out.vec b r2 ∧ Forest out.vec rank ∧
      Reach vec a r1 ∧ Reach vec b r2 ∧ (∃ w, vec[r2]? = some w ∧ w < 0) ∧
      out.ps.mem.take P.length = P ∧ out.cost ≤ 90 * nodes1.length+90 * nodes2.length+180 ∧
      out.need ≤ P.length+80 ∧ out.wk ≤ nodes1.length+nodes2.length ∧
      Trace vec a r1 nodes1 ∧ Trace middle b r2 nodes2 := by
  let initial := fields P counter (vec.length : Int) a b
  have nvalid := Proofs.VectorSumCall.i32_valid (vec.length : Int) (by omega) (by omega)
  have avalid := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by omega)
  have bvalid := Proofs.VectorSumCall.i32_valid (b : Int) (by omega) (by omega)
  have nv := env_n P counter vec.length a b nvalid
  have av := env_a P counter vec.length a b avalid
  have bv := env_b P counter vec.length a b bvalid
  have ga := condition_value initial vec 2 3 vec.length a nv av (by omega) (by omega)
  have gb := condition_value initial vec 2 4 vec.length b nv bv (by omega) (by omega)
  have ca := (pexecW_prim i32 fuel (.check (condition 2 3)) initial vec).trans
    (pstmtW_check_ok i32 initial vec (condition 2 3) 1 ga (by decide))
  have cb := (pexecW_prim i32 fuel (.check (condition 2 4)) initial vec).trans
    (pstmtW_check_ok i32 initial vec (condition 2 4) 1 gb (by decide))
  obtain ⟨one,r1,run1,ret1,state1,compressed1,forest1,cost1,need1,work1,tail1⟩ :=
    inlined_correct initial vec (depth valid) (depth_forest valid) length 2 3 a nv av ha fuel
      (by have bound := depth_le_rank valid a ha; omega)
  have middleValid := valid.compressed compressed1
  obtain ⟨traceRoot1,nodes1,trace1⟩ := trace_exists valid a ha
  have same1 := root_unique compressed1.reach trace1.reaches compressed1.root trace1.root
  subst traceRoot1
  rw [depth_of_trace valid trace1] at cost1 work1
  have n1 : penv1 one.ps 2 i32 = some (one.vec.length : Int) := by
    rw [compressed1.length,state1]
    exact inline_env_old initial vec.length r1 vec.length 2 nv
  have b1 : penv1 one.ps 4 i32 = some (b : Int) := by
    rw [state1]
    exact inline_env_old initial vec.length r1 b 4 bv
  obtain ⟨two,r2,run2,ret2,state2,compressed2,forest2,cost2,need2,work2,tail2⟩ :=
    inlined_correct one.ps one.vec (depth middleValid) (depth_forest middleValid) (by rw [compressed1.length]; exact length) 2 4 b n1 b1
      (by rw [compressed1.length]; exact hb) fuel
      (by have bound := depth_le_rank middleValid b (by rw [compressed1.length]; exact hb); omega)
  obtain ⟨traceRoot2,nodes2,trace2⟩ := trace_exists middleValid b (by rw [compressed1.length]; exact hb)
  have same2 := root_unique compressed2.reach trace2.reaches compressed2.root trace2.root
  subst traceRoot2
  rw [depth_of_trace middleValid trace2] at cost2 work2
  have l0 : initial.bs.length = 4 := rfl
  have l1 : one.ps.bs.length = 8 := by rw [state1]; simp [inlineState,initial,fields]
  have r1inside : r1 < vec.length := by
    obtain ⟨w,found,_⟩ := compressed1.root
    exact (List.getElem?_eq_some_iff.mp found).1
  have r2inside : r2 < vec.length := by
    obtain ⟨w,found,_⟩ := compressed2.root
    have bound := (List.getElem?_eq_some_iff.mp found).1
    rw [compressed1.length] at bound
    exact bound
  have r1valid := Proofs.VectorSumCall.i32_valid (r1 : Int) (by omega) (by omega)
  have r2valid := Proofs.VectorSumCall.i32_valid (r2 : Int) (by omega) (by omega)
  have firstValue : penv1 one.ps 8 i32 = some (r1 : Int) := by
    rw [state1]
    simpa only [l0] using inline_env_result initial vec.length r1 r1valid
  have firstFinal : penv1 two.ps 8 i32 = some (r1 : Int) := by
    rw [state2]
    exact inline_env_old one.ps one.vec.length r2 r1 8 firstValue
  have secondFinal : penv1 two.ps 12 i32 = some (r2 : Int) := by
    rw [state2]
    simpa only [l1] using inline_env_result one.ps one.vec.length r2 r2valid
  have value : vdenL i32 two.vec (penv1 two.ps) resultExpr = some (if r1=r2 then 1 else 0) := by
    rw [Proofs.VectorFillCall.vdenL_scalar _ _ _ _ rfl]
    simp only [NExpr.denote,firstFinal,secondFinal,Option.bind_some]
    have comparison : binaryValue .eq (r1 : Int) (r2 : Int) = if r1=r2 then 1 else 0 := by
      by_cases equal : r1=r2
      · simp [binaryValue,equal]
      · have unequal : (r1 : Int) ≠ (r2 : Int) := by omega
        simp [binaryValue,equal,unequal]
    rw [comparison]
    by_cases eq : r1=r2 <;> simp [eq,Ty.convert]
  have rprim := (pexecW_prim i32 fuel (.ret resultExpr) two.ps two.vec).trans
    (pstmtW_ret_ok i32 two.ps two.vec resultExpr _ value)
  have returned := seqW_ret (b := Sk) rprim rfl
  have after2 := tail2 retCmd _ returned
  have after1 := tail1 (plug (inlined one.ps.bs.length 2 4) retCmd) _ after2
  have all := seqW_some ca rfl (seqW_some cb rfl after1)
  rw [l0,l1] at all
  change pexecW i32 fuel body initial vec = some _ at all
  rw [← body_eq] at all
  obtain ⟨w,found,negative⟩ := compressed2.root
  have oldRoot : vec[r2]? = some w := (negative_entry compressed1 w negative).mp found
  refine ⟨_,r1,r2,one.vec,nodes1,nodes2,all,rfl,compressed1,compressed2,
    (middleValid.compressed compressed2).forest,compressed1.reach,
    reach_backward compressed1 compressed2.reach,⟨w,oldRoot,negative⟩,?_,?_,?_,?_,trace1,trace2⟩
  · change two.ps.mem.take P.length = P
    rw [state2,state1]
    simp [inlineState,initial,fields,List.append_assoc]
  · have guardA : vwp (condition 2 3) = (7,7) := rfl
    have guardB : vwp (condition 2 4) = (7,7) := rfl
    have resultW : vwp resultExpr = (3,3) := rfl
    change (vwp (condition 2 3)).1+1+((vwp (condition 2 4)).1+1+
      (one.cost+(two.cost+((vwp resultExpr).1+1)))) ≤ _
    rw [guardA,guardB,resultW]; dsimp; omega
  · have guardA : vwp (condition 2 3) = (7,7) := rfl
    have guardB : vwp (condition 2 4) = (7,7) := rfl
    have resultW : vwp resultExpr = (3,3) := rfl
    change max (initial.mem.length+initial.bs.length+(vwp (condition 2 3)).2+2)
      (max (initial.mem.length+initial.bs.length+(vwp (condition 2 4)).2+2)
        (max one.need (max two.need (two.ps.mem.length+two.ps.bs.length+(vwp resultExpr).2+2)))) ≤ _
    have m1 : one.ps.mem.length = P.length+7 := by rw [state1]; simp [inlineState,initial,fields]
    have m2 : two.ps.mem.length = P.length+11 := by rw [state2]; simp [inlineState,m1]
    have l2 : two.ps.bs.length = 12 := by rw [state2]; simp [inlineState,l1]
    simp only [initial,fields,List.length_append,List.length_cons,List.length_nil] at need1
    rw [m1,l1] at need2
    simp [initial,fields,m2,l2,guardA,guardB,resultW]; omega
  · change 0+(0+(one.wk+(two.wk+0))) ≤ _
    omega



open Proofs.UfRootReady Proofs.VecWriteFrame

theorem same_call_ready_paths (caller : NState) {vslot vb V vsc cslot : Nat} {vbuf : Buffer Value}
    (ok : VOKWF caller vslot vb V vsc vbuf) (countBinding : CppState.Binding) (count : Int)
    (cell : caller.scalarCell cslot i32 = some (countBinding,⟨i32,count⟩)) (writable : countBinding.writable = true)
    (vec : List Int) (rank : Nat → Nat) (valid : Valid vec count rank)
    (items : vbuf.items = vec.map Value.integer) (length : vec.length < 2147483648)
    (bvalid : vbuf.Valid (accepts (.integer i32))) (limit : vbuf.limit = CppVectorBindings.sizeLimit i32)
    (owner : vbuf.owner = V)
    (en ea eb : NExpr) (a b : Nat) (ns : en.scalarOnly = true) (as_ : ea.scalarOnly = true) (bs_ : eb.scalarOnly = true)
    (nt : en.resultType = i32) (at_ : ea.resultType = i32) (bt_ : eb.resultType = i32)
    (nv : en.denote (envOf caller) = some (vec.length : Int))
    (av : ea.denote (envOf caller) = some (a : Int)) (bv : eb.denote (envOf caller) = some (b : Int))
    (ha : a < vec.length) (hb : b < vec.length) :
    ∃ Sinit fuel out, ∃ (r1 r2 : Nat) (middle final : List Int) (nodes1 nodes2 : List Nat),
      prepare caller Proofs.UnionFindCandidateInstance.UnionFind_same.parameters
        [.vectorReference vslot,.scalarReference cslot,.value en,.value ea,.value eb] = some Sinit ∧
      Proofs.UnionFindCandidateInstance.UnionFind_same.callFuel fuel caller
        [.vectorReference vslot,.scalarReference cslot,.value en,.value ea,.value eb] =
          .finished (out,.scalar (if r1=r2 then 1 else 0)) ∧
      Compressed vec middle a r1 ∧ Compressed middle final b r2 ∧ Forest final rank ∧
      (r1=r2 ↔ Proofs.UfFieldsSame.Connected vec a b) ∧
      ScalarPost3 caller Sinit out (en.nodes+ea.nodes+eb.nodes) (90 * nodes1.length+90 * nodes2.length+220)
        caller.scalars.memory (nodes1.length+nodes2.length) V final ∧
      (∃ buf, VOKWF out vslot vb V vsc buf ∧ buf.items = final.map Value.integer ∧
        buf.Valid (accepts (.integer i32)) ∧ buf.limit = CppVectorBindings.sizeLimit i32 ∧ buf.owner = V) ∧
      (∀ slot ty, out.scalarCell slot ty = caller.scalarCell slot ty) ∧
      Trace vec a r1 nodes1 ∧ Trace middle b r2 nodes2 := by
  have nvalid := Proofs.VectorSumCall.i32_valid (vec.length : Int) (by omega) (by omega)
  have avalid := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by omega)
  have bvalueValid := Proofs.VectorSumCall.i32_valid (b : Int) (by omega) (by omega)
  obtain ⟨q,qwork,Sinit,prep,slots,memory,bindings,base,scopeEq,frame,work0,peak0⟩ :=
    Proofs.UfFieldsSame.prepare_same caller ok countBinding count cell writable en ea eb vec.length a b ns as_ bs_ nt at_ bt_ nv av bv
      nvalid avalid bvalueValid
  let vc : VCtx := ⟨i32,true,true,V,vsc,vbuf,vec,items,fun _ => rfl,by omega,
    caller.frame.state.liveSpace,caller.frame.state.storage.work,caller.scope+1,
    caller.frame.state.storage.objects.length⟩
  have initial : FW vc vec vbuf 0 Sinit.frame := by
    rw [frame]
    refine ⟨ok.valid,ok.lengths,rfl,rfl,?_,rfl,rfl,ok.vtag,ok.vfound,ok.flag,items,bvalid,limit,owner,by omega⟩
    intro root scope found
    have := ok.strict root scope found
    show scope < caller.scope+1
    omega
  obtain ⟨res,r1,r2,middle,nodes1,nodes2,ran,ret,c1,c2,newForest,reach1,reach2,oldRoot2,saved,cost,need,writes,trace1,trace2⟩ :=
    same_body_paths (callerP caller) ⟨countBinding.address,true⟩ vec rank count valid length a b ha hb
      (max (rank a) (rank b)+2) (by omega) (by omega)
  have resultValid : Proofs.PrefixSumsCall.bT.valid (if r1=r2 then 1 else 0) = true := by
    by_cases eq : r1=r2 <;> simp [eq,Ty.valid]
  have prefixLength : (callerP caller).length = caller.scalars.memory.length+
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have unchanged : (callerP caller ++ [(⟨i32,(vec.length : Int)⟩ : Cell),⟨i32,(a : Int)⟩,⟨i32,(b : Int)⟩]).take
      caller.scalars.memory.length = caller.scalars.memory := UfRootCall.take_P caller _
  have preparedRun : pexecW i32 (max (rank a) (rank b)+2) Proofs.UnionFindCandidateInstance.UnionFind_same.body
      ⟨callerP caller ++ [⟨i32,(vec.length : Int)⟩,⟨i32,(a : Int)⟩,⟨i32,(b : Int)⟩],
        [⟨countBinding.address,true⟩,⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩]⟩
      vec = some res := ran
  obtain ⟨fuel,out,call,post,framePost⟩ := call_vecw_frame vc true (fun _ => ⟨rfl,rfl⟩) caller
    Proofs.UnionFindCandidateInstance.UnionFind_same [.vectorReference vslot,.scalarReference cslot,.value en,.value ea,.value eb]
    Sinit (callerP caller ++ [⟨i32,(vec.length : Int)⟩,⟨i32,(a : Int)⟩,⟨i32,(b : Int)⟩])
    [⟨countBinding.address,true⟩,⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩]
    prep (by rw [slots]; rfl) memory bindings base scopeEq (by rw [frame]) (by rw [frame])
    initial rfl rfl rfl rfl peak0 (by simp [prefixLength]; omega) (by rw [unchanged]) ok.base (by decide)
    (max (rank a) (rank b)+2) res preparedRun _ ret Proofs.PrefixSumsCall.bT rfl resultValid
    (by omega) (by simp) (en.nodes+ea.nodes+eb.nodes) (90 * nodes1.length+90 * nodes2.length+220) (by omega)
  have savedCaller : res.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    calc res.ps.mem.take caller.scalars.memory.length =
        (res.ps.mem.take (callerP caller).length).take caller.scalars.memory.length := by
          rw [List.take_take,Nat.min_eq_left (by omega)]
      _ = (callerP caller).take caller.scalars.memory.length := by rw [saved]
      _ = caller.scalars.memory := by simp only [callerP]; exact List.take_left' rfl
  rw [savedCaller] at post
  have ready := ready_of_frame caller out vc res.vec framePost post.slots post.bindings
    (by rw [post.scalarMemory]) post.valid vslot vb ok rfl rfl
  refine ⟨Sinit,fuel,out,r1,r2,middle,res.vec,nodes1,nodes2,prep,call,c1,c2,newForest,
    Proofs.UfFieldsSame.roots_connected vec a b r1 r2 reach1 reach2 c1.root oldRoot2,post.relax (le_refl _) (le_refl _) writes,ready,?_,trace1,trace2⟩

  intro slot ty
  simp only [NState.scalarCell,NState.scalarSlot,post.slots,post.scalarMemory,framePost.scalarBindings]




theorem same_work_paths (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Represents s layout ps count rank) (a b : Nat) (ha : a < ps.length) (hb : b < ps.length) :
    ∃ fuel out, ∃ (r1 r2 : Nat) (middle vec : List Int) (nodes1 nodes2 : List Nat),
      Proofs.UnionFindCandidateInstance.UnionFind_same.callFuel fuel s
        (arguments layout ++ [.value (.literal i32 a),.value (.literal i32 b)]) =
          .finished (out,.scalar (if r1=r2 then 1 else 0)) ∧
      Compressed ps middle a r1 ∧ Compressed middle vec b r2 ∧ Represents out layout vec count rank ∧
      (r1=r2 ↔ Proofs.UfFieldsSame.Connected ps a b) ∧ Trace ps a r1 nodes1 ∧ Trace middle b r2 nodes2 ∧
      out.work ≤ s.work+91*nodes1.length+91*nodes2.length+223 := by
  obtain ⟨buf,cb,nb,inv⟩ := represented
  have av := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by have h := inv.math.length; omega)
  have bv := Proofs.VectorSumCall.i32_valid (b : Int) (by omega) (by have h := inv.math.length; omega)
  obtain ⟨init,fuel,out,r1,r2,middle,vec,nodes1,nodes2,prep,ran,c1,c2,forest,connected,post,ready,cells,t1,t2⟩ :=
    same_call_ready_paths s inv.ok cb count inv.countCell inv.writable ps rank inv.math inv.items inv.math.length
      inv.bufferValid inv.limit inv.owner (nExpr layout) (.literal i32 a) (.literal i32 b) a b
      rfl rfl rfl rfl rfl rfl inv.n_value (literal_value a av s) (literal_value b bv s) ha hb
  have represented := inv.readonly_transition out vec ((inv.math.compressed c1).compressed c2)
    (c2.length.trans c1.length) ready cells
  have scalarWork := post.scalarWork
  change out.scalars.work ≤ s.scalars.work+3+(90*nodes1.length+90*nodes2.length+220) at scalarWork
  have storageWork := post.storageWork
  refine ⟨fuel,out,r1,r2,middle,vec,nodes1,nodes2,ran,c1,c2,represented,connected,t1,t2,?_⟩
  unfold NState.work
  omega

theorem same_amortized (s : NState) (layout : Layout) (ps : List Int) (count : Int)
    (rank rho : Nat → Nat) (represented : Represents s layout ps count rank)
    (history : History ps rho) (a b : Nat) (ha : a < ps.length) (hb : b < ps.length) :
    ∃ fuel out, ∃ (r1 r2 : Nat) (vec : List Int),
      Proofs.UnionFindCandidateInstance.UnionFind_same.callFuel fuel s
        (arguments layout ++ [.value (.literal i32 a),.value (.literal i32 b)]) =
          .finished (out,.scalar (if r1=r2 then 1 else 0)) ∧
      Represents out layout vec count rank ∧ History vec rho ∧ vec.length = ps.length ∧
      (r1=r2 ↔ Proofs.UfFieldsSame.Connected ps a b) ∧
      out.work+91*forestPotential vec rho ≤
        s.work+91*forestPotential ps rho+587*(alpha ps.length+1) := by
  have valid : Valid ps count rank := by
    obtain ⟨buf,cb,nb,inv⟩ := represented
    exact inv.math
  obtain ⟨fuel,out,r1,r2,middle,vec,nodes1,nodes2,ran,c1,c2,post,connected,t1,t2,work⟩ :=
    same_work_paths s layout ps count rank represented a b ha hb
  have hist1 := history_compressed history c1
  have hist2 := history_compressed hist1 c2
  have budget1 := t1.forest_budget valid history c1
  have budget2 := t2.forest_budget (valid.compressed c1) hist1 c2
  rw [c1.length] at budget2
  refine ⟨fuel,out,r1,r2,vec,ran,post,hist2,c2.length.trans c1.length,connected,?_⟩
  omega


open Proofs.UfFieldsUnite Proofs.UfSameCall Proofs.VectorFillCall

theorem unite_body_paths (P : List Cell) (counter : Nat) (groups : Int) (vec : List Int) (rank : Nat → Nat)
    (valid : Valid vec groups rank) (countFound : P[counter]? = some ⟨i32,groups⟩)
    (a b : Nat) (ha : a < vec.length) (hb : b < vec.length) (fuel : Nat)
    (fa : rank a+2 ≤ fuel) (fb : rank b+2 ≤ fuel) :
    ∃ (out : PRW) (r1 r2 : Nat) (middle two : List Int) (nodes1 nodes2 : List Nat),
      pexecW i32 fuel Proofs.UnionFindCandidateInstance.UnionFind_unite.body
        (fields P ⟨counter,true⟩ vec.length a b) vec = some out ∧
      out.ret = some (Proofs.UfUniteCall.uniteX two r1 r2 : Int) ∧
      Compressed vec middle a r1 ∧ Compressed middle two b r2 ∧
      out.vec = Proofs.UfUniteCall.uniteVec two r1 r2 ∧
      (∃ rank', Valid out.vec (countAfter groups r1 r2) rank') ∧
      out.ps.mem.take P.length = updatedMemory P counter groups r1 r2 ∧
      out.cost ≤ 90*nodes1.length+90*nodes2.length+340 ∧ out.need ≤ P.length+100 ∧ out.wk ≤ nodes1.length+nodes2.length+2 ∧
      Trace vec a r1 nodes1 ∧ Trace middle b r2 nodes2 := by
  let initial := fields P ⟨counter,true⟩ (vec.length : Int) a b
  have length := valid.length
  have counterInside := (List.getElem?_eq_some_iff.mp countFound).1
  have nvalid := Proofs.VectorSumCall.i32_valid (vec.length : Int) (by omega) (by omega)
  have av := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by omega)
  have bv := Proofs.VectorSumCall.i32_valid (b : Int) (by omega) (by omega)
  have nv := env_n P ⟨counter,true⟩ vec.length a b nvalid
  have aa := env_a P ⟨counter,true⟩ vec.length a b av
  have bb := env_b P ⟨counter,true⟩ vec.length a b bv
  have ca := (pexecW_prim i32 fuel (.check (condition 2 3)) initial vec).trans
    (pstmtW_check_ok i32 initial vec (condition 2 3) 1 (condition_value initial vec 2 3 vec.length a nv aa (by omega) (by omega)) (by decide))
  have cb := (pexecW_prim i32 fuel (.check (condition 2 4)) initial vec).trans
    (pstmtW_check_ok i32 initial vec (condition 2 4) 1 (condition_value initial vec 2 4 vec.length b nv bb (by omega) (by omega)) (by decide))
  have countLoc : Loc initial 0 counter groups := by
    refine ⟨rfl,?_⟩
    simpa [initial,fields,List.getElem?_append_left counterInside] using countFound
  obtain ⟨one,r1,run1,ret1,state1,c1,forest1,cost1,need1,work1,tail1⟩ :=
    inlined_correct initial vec (depth valid) (depth_forest valid) length 2 3 a nv aa ha fuel
      (by have bound := depth_le_rank valid a ha; omega)
  have middleValid := valid.compressed c1
  obtain ⟨traceRoot1,nodes1,trace1⟩ := trace_exists valid a ha
  have same1 := root_unique c1.reach trace1.reaches c1.root trace1.root
  subst traceRoot1
  rw [depth_of_trace valid trace1] at cost1 work1
  have r1inside := (List.getElem?_eq_some_iff.mp (Classical.choose_spec c1.root).1).1
  have r1valid := Proofs.VectorSumCall.i32_valid (r1 : Int) (by omega) (by omega)
  have bs1 : one.ps.bs.length = 8 := by rw [state1]; simp [inlineState,initial,fields]
  have mem1 : one.ps.mem.length = P.length+7 := by rw [state1]; simp [inlineState,initial,fields]
  have result1 : penv1 one.ps 8 i32 = some (r1 : Int) := by
    rw [state1]
    simpa [initial,fields] using inline_env_result initial vec.length r1 r1valid
  have dx := (pexecW_prim i32 fuel (.declare i32 true (.variable i32 8)) one.ps one.vec).trans
    (pstmtW_declare_ok i32 one.ps one.vec i32 true (.variable i32 8) r1
      (by rw [vdenL_scalar _ _ _ _ rfl]; exact result1) r1 (Ty.convert_of_valid _ _ r1valid))
  let afterX := appI one.ps r1
  have n1 : penv1 afterX 2 i32 = some (one.vec.length : Int) := by
    rw [c1.length]
    apply env_old one.ps i32 i32 _ r1 2
    rw [state1]
    exact inline_env_old initial vec.length r1 vec.length 2 nv
  have b1 : penv1 afterX 4 i32 = some (b : Int) := by
    apply env_old one.ps i32 i32 _ r1 4
    rw [state1]
    exact inline_env_old initial vec.length r1 b 4 bb
  have xloc : Loc afterX 8 (P.length+7) r1 := by
    simpa [bs1,mem1] using loc_app_new one.ps (r1 : Int)
  have cloc1 : Loc afterX 0 counter groups := by
    apply loc_app_old
    rw [state1]
    exact inline_loc initial vec.length r1 groups 0 counter countLoc
  obtain ⟨twoOut,r2,run2,ret2,state2,c2,forest2,cost2,need2,work2,tail2⟩ :=
    inlined_correct afterX one.vec (depth middleValid) (depth_forest middleValid) (by rw [c1.length]; exact length) 2 4 b n1 b1
      (by rw [c1.length]; exact hb) fuel
      (by have bound := depth_le_rank middleValid b (by rw [c1.length]; exact hb); omega)
  obtain ⟨traceRoot2,nodes2,trace2⟩ := trace_exists middleValid b (by rw [c1.length]; exact hb)
  have same2 := root_unique c2.reach trace2.reaches c2.root trace2.root
  subst traceRoot2
  rw [depth_of_trace middleValid trace2] at cost2 work2
  have bsX : afterX.bs.length = 9 := by simp [afterX,bs1]
  have memX : afterX.mem.length = P.length+8 := by simp [afterX,mem1]
  have bs2 : twoOut.ps.bs.length = 13 := by rw [state2]; simp [inlineState,bsX]
  have mem2 : twoOut.ps.mem.length = P.length+12 := by rw [state2]; simp [inlineState,memX]
  have r2inside : r2 < vec.length := by
    have inside := (List.getElem?_eq_some_iff.mp (Classical.choose_spec c2.root).1).1
    rw [c1.length] at inside
    exact inside
  have r2valid := Proofs.VectorSumCall.i32_valid (r2 : Int) (by omega) (by omega)
  have result2 : penv1 twoOut.ps 13 i32 = some (r2 : Int) := by
    rw [state2]
    simpa [bsX] using inline_env_result afterX one.vec.length r2 r2valid
  have dy := (pexecW_prim i32 fuel (.declare i32 true (.variable i32 13)) twoOut.ps twoOut.vec).trans
    (pstmtW_declare_ok i32 twoOut.ps twoOut.vec i32 true (.variable i32 13) r2
      (by rw [vdenL_scalar _ _ _ _ rfl]; exact result2) r2 (Ty.convert_of_valid _ _ r2valid))
  let ready := appI twoOut.ps r2
  have xl : Loc ready 8 (P.length+7) r1 := by
    apply loc_app_old
    rw [state2]
    exact inline_loc afterX one.vec.length r2 r1 8 (P.length+7) xloc
  have yl : Loc ready 13 (P.length+12) r2 := by simpa [bs2,mem2] using loc_app_new twoOut.ps (r2 : Int)
  have cl : Loc ready 0 counter groups := by
    apply loc_app_old
    rw [state2]
    exact inline_loc afterX one.vec.length r2 groups 0 counter cloc1
  have readyBS : ready.bs.length = 14 := by simp [ready,bs2]
  have readyMem : ready.mem.length = P.length+13 := by simp [ready,mem2]
  have readySaved : ready.mem.take P.length = P := by
    simp [ready,state2,afterX,state1,inlineState,appI,initial,fields,List.append_assoc]
  obtain ⟨vx,fx,nx⟩ := c1.root
  have xmid := (negative_entry c1 vx nx).mpr fx
  have xfinal := (negative_entry c2 vx nx).mpr xmid
  obtain ⟨vy,fy,ny⟩ := c2.root
  have yfinal := (negative_entry c2 vy ny).mpr fy
  have valid2 := (valid.compressed c1).compressed c2
  obtain ⟨last,runLast,retLast,vecLast,psLast,workLast,costLast,needLast,rankLast,validLast⟩ :=
    UfUniteTail.tail_correct ready twoOut.vec groups rank valid2 (P.length+7) (P.length+12) counter r1 r2
      xl yl cl (by omega) (by omega) (by omega) readyBS ⟨vx,xfinal,nx⟩ ⟨vy,yfinal,ny⟩ fuel
  have afterY := seqW_some dy rfl runLast
  have afterRoot2 := tail2 (.sequence (.primitive (.declare i32 true (.variable i32 13))) UfUniteTail.tail) _ afterY
  have afterDeclX := seqW_some dx rfl afterRoot2
  have afterRoot1 := tail1 (.sequence (.primitive (.declare i32 true (.variable i32 8)))
    (plug (inlined afterX.bs.length 2 4) (.sequence (.primitive (.declare i32 true (.variable i32 13))) UfUniteTail.tail))) _ afterDeclX
  have all := seqW_some ca rfl (seqW_some cb rfl afterRoot1)
  have bs0 : initial.bs.length = 4 := rfl
  rw [bs0,bsX] at all
  change pexecW i32 fuel (UfUniteTail.before_tail UfUniteTail.tail) initial vec = some _ at all
  rw [← UfUniteTail.body_eq] at all
  refine ⟨_,r1,r2,one.vec,twoOut.vec,nodes1,nodes2,all,retLast,c1,c2,vecLast,⟨rankLast,validLast⟩,?_,?_,?_,?_,trace1,trace2⟩
  · change last.ps.mem.take P.length = _
    rw [psLast]
    exact final_take ready twoOut.vec P (P.length+7) (P.length+12) counter r1 r2 groups readySaved (by omega) (by omega)
  · change 8+(8+(one.cost+(2+(twoOut.cost+(2+last.cost))))) ≤ _
    omega
  · change max (initial.mem.length+initial.bs.length+9) (max (initial.mem.length+initial.bs.length+9)
      (max one.need (max (one.ps.mem.length+one.ps.bs.length+5)
        (max twoOut.need (max (twoOut.ps.mem.length+twoOut.ps.bs.length+5) last.need))))) ≤ _
    simp only [initial,fields,List.length_append,List.length_cons,List.length_nil] at need1
    rw [memX,bsX] at need2
    rw [readyMem,readyBS] at needLast
    simp [initial,fields,mem1,bs1,mem2,bs2]
    omega
  · change 0+(0+(one.wk+(0+(twoOut.wk+(0+last.wk))))) ≤ _
    split at workLast <;> omega



open Proofs.UfUniteReady

theorem unite_call_ready_paths (caller : NState) {vslot vb V vsc cslot : Nat} {vbuf : Buffer Value}
    (ok : VOKWF caller vslot vb V vsc vbuf) (countBinding : CppState.Binding) (count : Int)
    (cell : caller.scalarCell cslot i32 = some (countBinding,⟨i32,count⟩)) (writable : countBinding.writable = true)
    (vec : List Int) (rank : Nat → Nat) (valid : Valid vec count rank)
    (items : vbuf.items = vec.map Value.integer) (bvalid : vbuf.Valid (accepts (.integer i32)))
    (limit : vbuf.limit = CppVectorBindings.sizeLimit i32) (owner : vbuf.owner = V)
    (en ea eb : NExpr) (a b : Nat) (ns : en.scalarOnly = true) (as_ : ea.scalarOnly = true) (bs_ : eb.scalarOnly = true)
    (nt : en.resultType = i32) (at_ : ea.resultType = i32) (bt_ : eb.resultType = i32)
    (nv : en.denote (envOf caller) = some (vec.length : Int))
    (av : ea.denote (envOf caller) = some (a : Int)) (bv : eb.denote (envOf caller) = some (b : Int))
    (ha : a < vec.length) (hb : b < vec.length) :
    ∃ Sinit fuel out, ∃ (r1 r2 : Nat) (middle two final : List Int) (nodes1 nodes2 : List Nat),
      prepare caller Proofs.UnionFindCandidateInstance.UnionFind_unite.parameters
        [.vectorReference vslot,.scalarReference cslot,.value en,.value ea,.value eb] = some Sinit ∧
      Proofs.UnionFindCandidateInstance.UnionFind_unite.callFuel fuel caller
        [.vectorReference vslot,.scalarReference cslot,.value en,.value ea,.value eb] =
          .finished (out,.scalar (Proofs.UfUniteCall.uniteX two r1 r2 : Int)) ∧
      Compressed vec middle a r1 ∧ Compressed middle two b r2 ∧ final = Proofs.UfUniteCall.uniteVec two r1 r2 ∧
      (∃ rank', Valid final (Proofs.UfFieldsUnite.countAfter count r1 r2) rank') ∧ (r1=r2 ↔ Connected vec a b) ∧
      out.scalars.bindings = caller.scalars.bindings ∧ out.scalars.baseMemory = caller.scalars.baseMemory ∧
      ScalarPost3 caller Sinit out (en.nodes+ea.nodes+eb.nodes) (90*nodes1.length+90*nodes2.length+400)
        (Proofs.UfFieldsUnite.updatedMemory caller.scalars.memory countBinding.address count r1 r2) (nodes1.length+nodes2.length+2) V final ∧
      (∃ buf, VOKWF out vslot vb V vsc buf ∧ buf.items = final.map Value.integer ∧
        buf.Valid (accepts (.integer i32)) ∧ buf.limit = CppVectorBindings.sizeLimit i32 ∧ buf.owner = V) ∧
      out.scalarCell cslot i32 = some (countBinding,⟨i32,Proofs.UfFieldsUnite.countAfter count r1 r2⟩) ∧
      (∀ slot ty binding value, caller.scalarCell slot ty = some (binding,value) →
        binding.address ≠ countBinding.address → out.scalarCell slot ty = some (binding,value)) ∧
      (∀ slot binding, caller.scalarCell slot i32 = some (binding,⟨i32,count⟩) →
        binding.address = countBinding.address → out.scalarCell slot i32 =
          some (binding,⟨i32,Proofs.UfFieldsUnite.countAfter count r1 r2⟩)) ∧
      Trace vec a r1 nodes1 ∧ Trace middle b r2 nodes2 := by
  have length := valid.length
  have nvalid := Proofs.VectorSumCall.i32_valid (vec.length : Int) (by omega) (by omega)
  have avalid := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by omega)
  have bvalidValue := Proofs.VectorSumCall.i32_valid (b : Int) (by omega) (by omega)
  obtain ⟨q,qwork,Sinit,prep,slots,memory,bindings,base,scopeEq,frame,work0,peak0⟩ :=
    prepare_same caller ok countBinding count cell writable en ea eb vec.length a b ns as_ bs_ nt at_ bt_ nv av bv
      nvalid avalid bvalidValue
  obtain ⟨_,_,_,found,_,_⟩ := scalarCell_facts cell
  have countInside := (List.getElem?_eq_some_iff.mp found).1
  have countFound : (callerP caller)[countBinding.address]? = some ⟨i32,count⟩ := by
    simpa [callerP,List.getElem?_append_left countInside] using found
  let vc : VCtx := ⟨i32,true,true,V,vsc,vbuf,vec,items,fun _ => rfl,by omega,
    caller.frame.state.liveSpace,caller.frame.state.storage.work,caller.scope+1,
    caller.frame.state.storage.objects.length⟩
  have initial : FW vc vec vbuf 0 Sinit.frame := by
    rw [frame]
    refine ⟨ok.valid,ok.lengths,rfl,rfl,?_,rfl,rfl,ok.vtag,ok.vfound,ok.flag,items,bvalid,limit,owner,by omega⟩
    intro root scope found
    have := ok.strict root scope found
    show scope < caller.scope+1
    omega
  obtain ⟨res,r1,r2,middle,two,nodes1,nodes2,ran,ret,c1,c2,finalEq,newValid,saved,cost,need,writes,trace1,trace2⟩ :=
    unite_body_paths (callerP caller) countBinding.address count vec rank valid countFound a b ha hb
      (max (rank a) (rank b)+2) (by omega) (by omega)
  have r1inside : r1 < two.length := by
    have inside := (List.getElem?_eq_some_iff.mp (Classical.choose_spec c1.root).1).1
    rw [c2.length,c1.length]
    exact inside
  have r2inside : r2 < two.length := by
    have inside := (List.getElem?_eq_some_iff.mp (Classical.choose_spec c2.root).1).1
    rw [c2.length]
    exact inside
  have resultInside := Proofs.UfUniteCall.uniteX_lt two r1 r2 r1inside r2inside
  have resultValid := Proofs.VectorSumCall.i32_valid (Proofs.UfUniteCall.uniteX two r1 r2 : Int) (by omega)
    (by rw [c2.length,c1.length] at resultInside; omega)
  have prefixLength : (callerP caller).length = caller.scalars.memory.length+
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have unchanged : (callerP caller ++ [(⟨i32,(vec.length : Int)⟩ : Cell),⟨i32,(a : Int)⟩,⟨i32,(b : Int)⟩]).take
      caller.scalars.memory.length = caller.scalars.memory := UfRootCall.take_P caller _
  have preparedRun : pexecW i32 (max (rank a) (rank b)+2) Proofs.UnionFindCandidateInstance.UnionFind_unite.body
      ⟨callerP caller ++ [⟨i32,(vec.length : Int)⟩,⟨i32,(a : Int)⟩,⟨i32,(b : Int)⟩],
        [⟨countBinding.address,true⟩,⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩]⟩
      vec = some res := ran
  obtain ⟨fuel,out,call,post,framePost⟩ := call_vecw_frame vc true (fun _ => ⟨rfl,rfl⟩) caller
    Proofs.UnionFindCandidateInstance.UnionFind_unite [.vectorReference vslot,.scalarReference cslot,.value en,.value ea,.value eb]
    Sinit (callerP caller ++ [⟨i32,(vec.length : Int)⟩,⟨i32,(a : Int)⟩,⟨i32,(b : Int)⟩])
    [⟨countBinding.address,true⟩,⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩]
    prep (by rw [slots]; rfl) memory bindings base scopeEq (by rw [frame]) (by rw [frame])
    initial rfl rfl rfl rfl peak0 (by simp [prefixLength]; omega) (by rw [unchanged]) ok.base (by decide)
    (max (rank a) (rank b)+2) res preparedRun _ ret i32 rfl resultValid (by omega) (by simp)
    (en.nodes+ea.nodes+eb.nodes) (90*nodes1.length+90*nodes2.length+400) (by omega)
  have savedCaller : res.ps.mem.take caller.scalars.memory.length =
      Proofs.UfFieldsUnite.updatedMemory caller.scalars.memory countBinding.address count r1 r2 := by
    calc res.ps.mem.take caller.scalars.memory.length =
        (res.ps.mem.take (callerP caller).length).take caller.scalars.memory.length := by
          rw [List.take_take,Nat.min_eq_left (by omega)]
      _ = (Proofs.UfFieldsUnite.updatedMemory (callerP caller) countBinding.address count r1 r2).take caller.scalars.memory.length := by rw [saved]
      _ = Proofs.UfFieldsUnite.updatedMemory ((callerP caller).take caller.scalars.memory.length) countBinding.address count r1 r2 := Proofs.UfFieldsUnite.updated_take _ _ _ _ _ _
      _ = Proofs.UfFieldsUnite.updatedMemory caller.scalars.memory countBinding.address count r1 r2 := by
        simp only [callerP]
        rw [List.take_left' rfl]
  rw [savedCaller] at post
  have metadata := Proofs.UfFieldsUnite.call_scalar_metadata _ _ _ _ _ _ i32 rfl call
  obtain ⟨w2,root2,neg2⟩ := c2.root
  have oldRoot2 : vec[r2]? = some w2 := (negative_entry c1 w2 neg2).mp root2
  have ready := ready_of_frame caller out vc res.vec framePost post.slots post.bindings
    (by rw [post.scalarMemory]; unfold Proofs.UfFieldsUnite.updatedMemory; split_ifs <;> simp) post.valid vslot vb ok rfl rfl
  have countValid : i32.valid (Proofs.UfFieldsUnite.countAfter count r1 r2) = true := by
    obtain ⟨rank',valid'⟩ := newValid
    exact valid'.count_range.2.2
  have counter := updated_counter caller out countBinding count r1 r2 cslot post.scalarMemory metadata.1 post.slots cell countValid
  refine ⟨Sinit,fuel,out,r1,r2,middle,two,res.vec,nodes1,nodes2,prep,call,c1,c2,finalEq,newValid,
    roots_connected vec a b r1 r2 c1.reach (reach_backward c1 c2.reach) c1.root ⟨w2,oldRoot2,neg2⟩,
    metadata.1,metadata.2,post.relax (le_refl _) (le_refl _) writes,ready,counter,?_,?_,trace1,trace2⟩
  · intro slot ty binding value found different
    exact updated_other caller out countBinding.address count r1 r2 post.scalarMemory metadata.1 post.slots slot ty binding value found different
  · intro slot binding found same
    apply updated_counter caller out binding count r1 r2 slot _ metadata.1 post.slots found countValid
    rw [same]
    exact post.scalarMemory



theorem unite_work_paths (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Represents s layout ps count rank) (a b : Nat) (ha : a < ps.length) (hb : b < ps.length) :
    ∃ fuel out, ∃ (r1 r2 : Nat) (middle two vec : List Int) (nextRank : Nat → Nat) (nodes1 nodes2 : List Nat),
      Proofs.UnionFindCandidateInstance.UnionFind_unite.callFuel fuel s
        (arguments layout ++ [.value (.literal i32 a),.value (.literal i32 b)]) =
          .finished (out,.scalar (Proofs.UfUniteCall.uniteX two r1 r2 : Int)) ∧
      Compressed ps middle a r1 ∧ Compressed middle two b r2 ∧
      vec = Proofs.UfUniteCall.uniteVec two r1 r2 ∧ (r1=r2 ↔ Proofs.UfFieldsSame.Connected ps a b) ∧
      vec.length = ps.length ∧ Represents out layout vec (Proofs.UfFieldsUnite.countAfter count r1 r2) nextRank ∧ Trace ps a r1 nodes1 ∧ Trace middle b r2 nodes2 ∧
      out.work ≤ s.work+91*nodes1.length+91*nodes2.length+405 := by
  obtain ⟨buf,cb,nb,inv⟩ := represented
  have av := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by have h := inv.math.length; omega)
  have bv := Proofs.VectorSumCall.i32_valid (b : Int) (by omega) (by have h := inv.math.length; omega)
  obtain ⟨init,fuel,out,r1,r2,middle,two,vec,nodes1,nodes2,prep,call,c1,c2,finalEq,newValid,connected,
      bindings,base,post,ready,counter,other,aliases,t1,t2⟩ :=
    unite_call_ready_paths s inv.ok cb count inv.countCell inv.writable ps rank inv.math
      inv.items inv.bufferValid inv.limit inv.owner (nExpr layout) (.literal i32 a) (.literal i32 b)
      a b rfl rfl rfl rfl rfl rfl inv.n_value (literal_value a av s) (literal_value b bv s) ha hb
  obtain ⟨nextRank,math⟩ := newValid
  obtain ⟨next,ok,items,valid,limit,owner⟩ := ready
  have length : vec.length = ps.length := by
    have len1 := c1.length
    have len2 := c2.length
    rw [finalEq]
    unfold Proofs.UfUniteCall.uniteVec
    split_ifs <;> (try simp only [List.length_set]) <;> omega
  have savedN := other layout.nSlot i32 nb ⟨i32,ps.length⟩ inv.nCell inv.different
  have representedPost : Represents out layout vec (Proofs.UfFieldsUnite.countAfter count r1 r2) nextRank := by
    refine ⟨next,cb,nb,ok,items,valid,limit,owner,math,counter,inv.writable,?_,inv.different⟩
    rw [length]
    exact savedN
  have scalarWork := post.scalarWork
  change out.scalars.work ≤ s.scalars.work+3+(90*nodes1.length+90*nodes2.length+400) at scalarWork
  have storageWork := post.storageWork
  refine ⟨fuel,out,r1,r2,middle,two,vec,nextRank,nodes1,nodes2,call,c1,c2,finalEq,connected,length,representedPost,t1,t2,?_⟩
  unfold NState.work
  omega

theorem unite_amortized (s : NState) (layout : Layout) (ps : List Int) (count : Int)
    (rank rho : Nat → Nat) (represented : Represents s layout ps count rank)
    (history : History ps rho) (a b : Nat) (ha : a < ps.length) (hb : b < ps.length) :
    ∃ fuel out, ∃ (r1 r2 : Nat) (two vec : List Int) (nextRank nextRho : Nat → Nat),
      Proofs.UnionFindCandidateInstance.UnionFind_unite.callFuel fuel s
        (arguments layout ++ [.value (.literal i32 a),.value (.literal i32 b)]) =
          .finished (out,.scalar (Proofs.UfUniteCall.uniteX two r1 r2 : Int)) ∧
      Represents out layout vec (Proofs.UfFieldsUnite.countAfter count r1 r2) nextRank ∧
      History vec nextRho ∧ vec.length = ps.length ∧
      (r1=r2 ↔ Proofs.UfFieldsSame.Connected ps a b) ∧
      out.work+91*forestPotential vec nextRho ≤
        s.work+91*forestPotential ps rho+769*(alpha ps.length+1) := by
  have valid : Valid ps count rank := by
    obtain ⟨buf,cb,nb,inv⟩ := represented
    exact inv.math
  obtain ⟨fuel,out,r1,r2,middle,two,vec,nextRank,nodes1,nodes2,ran,c1,c2,eq,connected,length,post,t1,t2,work⟩ :=
    unite_work_paths s layout ps count rank represented a b ha hb
  have hist1 := history_compressed history c1
  have hist2 := history_compressed hist1 c2
  have budget1 := t1.forest_budget valid history c1
  have budget2 := t2.forest_budget (valid.compressed c1) hist1 c2
  rw [c1.length] at budget2
  obtain ⟨w1,f1,n1⟩ := c1.root
  have f1middle := (negative_entry c1 w1 n1).mpr f1
  have f1two := (negative_entry c2 w1 n1).mpr f1middle
  obtain ⟨w2,f2,n2⟩ := c2.root
  have f2two := (negative_entry c2 w2 n2).mpr f2
  obtain ⟨nextRho,nextHistory,potential⟩ := unite_potential ((valid.compressed c1).compressed c2) hist2
    r1 r2 ⟨w1,f1two,n1⟩ ⟨w2,f2two,n2⟩
  rw [c2.length,c1.length] at potential
  rw [← eq] at nextHistory potential
  refine ⟨fuel,out,r1,r2,two,vec,nextRank,nextRho,ran,post,nextHistory,length,connected,?_⟩
  omega


theorem getter_work (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Represents s layout ps count rank) :
    ∃ fuel out, Proofs.UnionFindCandidateInstance.UnionFind_num_groups.callFuel fuel s (arguments layout) =
      .finished (out,.scalar count) ∧ Represents out layout ps count rank ∧ out.work ≤ s.work+41 := by
  obtain ⟨buf,cb,nb,inv⟩ := represented
  obtain ⟨init,fuel,out,prep,ran,bindings,base,post,ready,cells⟩ :=
    Proofs.UfCounterReady.num_groups_call_ready s inv.ok cb count inv.countCell inv.writable ps rank inv.math
      inv.items inv.bufferValid inv.limit inv.owner (nExpr layout) rfl rfl inv.n_value
  rw [← inv.math.count] at ran
  have scalarWork := post.scalarWork
  change out.scalars.work ≤ s.scalars.work+1+40 at scalarWork
  have storageWork := post.storageWork
  refine ⟨fuel,out,ran,inv.readonly_transition out ps inv.math rfl ready cells,?_⟩
  unfold NState.work
  omega

open Proofs.UfReceiverTrace
open Proofs.CppLoop (Outcome)

set_option maxRecDepth 4000 in
theorem amortized_step (s : NState) (layout : Layout) (ps : List Int) (count : Int)
    (rank rho : Nat → Nat) (represented : Represents s layout ps count rank)
    (history : History ps rho) (op : Operation) (allowed : op.allowed ps.length) :
    ∃ fuel out vec nextCount nextRank nextRho answer,
      call fuel s layout op = .finished (out,.scalar answer) ∧
      Represents out layout vec nextCount nextRank ∧ History vec nextRho ∧ vec.length = ps.length ∧
      out.work+91*forestPotential vec nextRho ≤
        s.work+91*forestPotential ps rho+769*(alpha ps.length+1) := by
  cases op with
  | root a =>
    obtain ⟨fuel,out,r,vec,ran,c,rep,hist,work⟩ := root_amortized s layout ps count rank rho represented history a allowed
    refine ⟨fuel,out,vec,count,rank,rho,(r : Int),ran,rep,hist,c.length,?_⟩
    omega
  | size a =>
    obtain ⟨fuel,out,r,vec,ran,c,rep,hist,work⟩ := size_amortized s layout ps count rank rho represented history a allowed
    refine ⟨fuel,out,vec,count,rank,rho,((component ps a).length : Int),ran,rep,hist,c.length,?_⟩
    omega
  | same a b =>
    obtain ⟨fuel,out,r1,r2,vec,ran,rep,hist,length,connected,work⟩ :=
      same_amortized s layout ps count rank rho represented history a b allowed.1 allowed.2
    refine ⟨fuel,out,vec,count,rank,rho,(if r1=r2 then 1 else 0),ran,rep,hist,length,?_⟩
    omega
  | unite a b =>
    obtain ⟨fuel,out,r1,r2,two,vec,nextRank,nextRho,ran,rep,hist,length,connected,work⟩ :=
      unite_amortized s layout ps count rank rho represented history a b allowed.1 allowed.2
    exact ⟨fuel,out,vec,Proofs.UfFieldsUnite.countAfter count r1 r2,nextRank,nextRho,
      (Proofs.UfUniteCall.uniteX two r1 r2 : Int),ran,rep,hist,length,work⟩
  | numGroups =>
    obtain ⟨fuel,out,ran,rep,work⟩ := getter_work s layout ps count rank represented
    refine ⟨fuel,out,ps,count,rank,rho,count,ran,rep,history,rfl,?_⟩
    omega

theorem amortized_calls (ops : List Operation) (s : NState) (layout : Layout)
    (ps : List Int) (count : Int) (rank rho : Nat → Nat)
    (represented : Represents s layout ps count rank) (history : History ps rho)
    (allowed : ∀ op ∈ ops, op.allowed ps.length) :
    ∃ fuels out vec nextCount nextRank nextRho answers,
      runCalls fuels ops s layout = .finished (out,answers) ∧
      Represents out layout vec nextCount nextRank ∧ History vec nextRho ∧ vec.length = ps.length ∧
      out.work+91*forestPotential vec nextRho ≤
        s.work+91*forestPotential ps rho+769*ops.length*(alpha ps.length+1) ∧
      fuels.length = ops.length ∧ answers.length = ops.length := by
  induction ops generalizing s ps count rank rho with
  | nil => exact ⟨[],s,ps,count,rank,rho,[],rfl,represented,history,rfl,by simp,rfl,rfl⟩
  | cons op ops ih =>
    obtain ⟨fuel,middle,vec1,count1,rank1,rho1,answer,ran,rep,hist,length1,headWork⟩ :=
      amortized_step s layout ps count rank rho represented history op (allowed op (by simp))
    have tailAllowed : ∀ other ∈ ops, other.allowed vec1.length := by
      intro other member
      rw [length1]
      exact allowed other (by simp [member])
    obtain ⟨fuels,out,vec,count2,rank2,rho2,answers,tailRun,finalRep,finalHist,length2,tailWork,fl,al⟩ :=
      ih middle vec1 count1 rank1 rho1 rep hist tailAllowed
    rw [length1] at tailWork
    have total : out.work+91*forestPotential vec rho2 ≤
        s.work+91*forestPotential ps rho+769*(op::ops).length*(alpha ps.length+1) := by
      simp only [List.length_cons,Nat.mul_add,Nat.add_mul,Nat.mul_one]
      simp only [Nat.mul_add,Nat.mul_one] at tailWork
      omega
    refine ⟨fuel::fuels,out,vec,count2,rank2,rho2,answer::answers,?_,finalRep,finalHist,
      length2.trans length1,total,by simp [fl],by simp [al]⟩
    simp only [runCalls,ran,bind,Outcome.bind,tailRun,pure]

theorem constructed_amortized_calls (caller : NState) (heap : Proofs.CppRootModel.Heap)
    (valid : caller.frame.state.wellFormed = true) (models : Proofs.CppRootModel.HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (en : NExpr) (n : Nat) (small : n < 2147483648) (scalar : en.scalarOnly = true)
    (type : en.resultType = i32) (value : en.denote (Proofs.CppNestedEval.envOf caller) = some (n : Int))
    (ops : List Operation) (allowed : ∀ op ∈ ops, op.allowed n) :
    ∃ receiver fuels out vec count rank historyRank answers,
      Proofs.UnionFindConstructionInstance.UnionFind_construct1.constructFuel 8 caller [.value en]
        (Proofs.UfConstructionExport.vectorField true) (.integer i32) (Proofs.UfConstructionExport.fields true) =
          .finished (receiver,Proofs.CppConstructorFinish.reference caller 2) ∧
      runCalls fuels ops receiver (layoutOf caller) = .finished (out,answers) ∧
      Represents out (layoutOf caller) vec count rank ∧ History vec historyRank ∧ vec.length = n ∧ out.work+91*forestPotential vec historyRank ≤
        caller.work+en.nodes+n+30+769*ops.length*(alpha n+1) ∧
      fuels.length = ops.length ∧ answers.length = ops.length := by
  obtain ⟨receiver,constructed,strong,constructionWork⟩ := Proofs.UfConstructionWork.construct_sized_work caller heap valid models lengths strict base en n small scalar type value
  obtain ⟨fuels,out,vec,count,rank,rho,answers,ran,finalRep,hist,length,pot,fl,al⟩ :=
    amortized_calls ops receiver (layoutOf caller) (List.replicate n (-1)) n (fun _ => 0) (fun _ => 0)
      strong.1 (initial_history n) (by simpa using allowed)
  simp only [forest_zero,List.length_replicate,Nat.mul_zero,Nat.add_zero] at pot
  exact ⟨receiver,fuels,out,vec,count,rank,rho,answers,constructed,ran,finalRep,hist,by simpa using length,by omega,fl,al⟩

theorem default_amortized_calls (caller : NState) (heap : Proofs.CppRootModel.Heap)
    (valid : caller.frame.state.wellFormed = true) (models : Proofs.CppRootModel.HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (ops : List Operation) (allowed : ∀ op ∈ ops, op.allowed 0) :
    ∃ receiver fuels out vec count rank historyRank answers,
      Proofs.UnionFindConstructionInstance.UnionFind_construct0.constructFuel 8 caller []
        (Proofs.UfConstructionExport.vectorField false) (.integer i32) (Proofs.UfConstructionExport.fields false) =
          .finished (receiver,Proofs.CppConstructorFinish.reference caller 2) ∧
      runCalls fuels ops receiver (layoutOf caller) = .finished (out,answers) ∧
      Represents out (layoutOf caller) vec count rank ∧ History vec historyRank ∧ vec.length = 0 ∧ out.work+91*forestPotential vec historyRank ≤
        caller.work+12+769*ops.length*(alpha 0+1) ∧
      fuels.length = ops.length ∧ answers.length = ops.length := by
  obtain ⟨receiver,constructed,strong,constructionWork⟩ := Proofs.UfConstructionWork.construct_default_work caller heap valid models lengths strict base
  obtain ⟨fuels,out,vec,count,rank,rho,answers,ran,finalRep,hist,length,pot,fl,al⟩ :=
    amortized_calls ops receiver (layoutOf caller) [] 0 (fun _ => 0) (fun _ => 0)
      strong.1 (initial_history 0) allowed
  simp only [forest_zero,List.length_nil,Nat.mul_zero,Nat.add_zero] at pot
  exact ⟨receiver,fuels,out,vec,count,rank,rho,answers,constructed,ran,finalRep,hist,length,by omega,fl,al⟩


theorem diagonal_work_unit (n m : Nat) :
    769*m*(alpha n+1) ≤ 2307*m*(diagonalAlpha n+1) := by
  have bound := Nat.mul_le_mul_left (769*m) (alpha_positive_unit n)
  calc
    _ ≤ (769*m)*(3*(diagonalAlpha n+1)) := bound
    _ = (769*3)*m*(diagonalAlpha n+1) := by ac_rfl
    _ = _ := rfl

end Proofs.UfMethodAmortized
