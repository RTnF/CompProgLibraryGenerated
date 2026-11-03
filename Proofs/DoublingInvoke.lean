import Proofs.DoublingPrologue
import Proofs.BitWidthU64

namespace Proofs.DoublingPrologue
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppMixedInvoke
open Proofs.DoublingNested Proofs.CppLoop
open Proofs.CppState (Cell)

abbrev bitWidthCall : Command :=
  .invokeScalar BitWidthU64Instance.bit_width_u64 [(.variable ⟨64,false,false⟩ 0 : Proofs.CppScalar.Expr)]

theorem env_two_values (S : NState) (P : List Cell) (K nI : Int) (bindings : S.scalars.bindings = [⟨P.length,true⟩,⟨P.length+1,false⟩])
    (memory : S.scalars.memory = P ++ [⟨u64,K⟩,⟨i32,nI⟩]) (hK : u64.valid K = true) (hn : i32.valid nI = true) :
    S.scalars.environment = some [K,nI] := by
  have c0 : S.scalars.memory[P.length]? = some ⟨u64,K⟩ := by
    rw [memory]; simp
  have c1 : S.scalars.memory[P.length+1]? = some ⟨i32,nI⟩ := by
    rw [memory]; simp
  unfold CppState.State.environment
  rw [bindings]
  simp only [List.mapM_cons,List.mapM_nil,c0,c1]
  simp only [Option.bind_eq_bind,Option.pure_def,Option.bind_some]
  rw [if_pos hK,if_pos hn]
  rfl

theorem env_two (F : Fixed) {sc : Nat} {rw0 : List Bool} (S : NState)
    (ps : PS F sc rw0 S (cells2 F) (binds2 F) slots3) (hK : u64.valid F.K = true) (hn : i32.valid (F.n : Int) = true) :
    S.scalars.environment = some [F.K,(F.n : Int)] :=
  env_two_values S F.P F.K (F.n : Int) (by simpa [binds2] using ps.bindings) (by simpa [cells2] using ps.memory) hK hn

def invokeNext (S : NState) (res : CppState.CallResult) : NState :=
  let scalars : CppState.State := {S.scalars with
    memory := res.memory ++ [(⟨⟨32,true,false⟩,res.value⟩ : Cell)],
    bindings := S.scalars.bindings ++ [(⟨S.scalars.memory.length,false⟩ : CppState.Binding)],
    work := S.scalars.work+1+res.work+1,
    peak := max S.scalars.peak
      (S.scalars.memory.length-S.scalars.baseMemory+S.scalars.bindings.length+res.peak)}
  ({S with scalars := scalars.observe 0,slots := S.slots ++ [.scalar S.scalars.bindings.length]} : NState).observe

theorem invoke_run (S : NState) (K : Int) (kv : u64.valid K = true) (nI : Int) (hn : i32.valid nI = true)
    (P : List Cell) (bindings : S.scalars.bindings = [⟨P.length,true⟩,⟨P.length+1,false⟩])
    (memory : S.scalars.memory = P ++ [⟨u64,K⟩,⟨i32,nI⟩]) (hK0 : 0 ≤ K) (hK : K < 2^64) :
    ∃ res, res.value = (Proofs.BitWidthU64.width K.toNat : Int) ∧ res.memory = S.scalars.memory ∧
      res.work ≤ 905 ∧ res.peak = 8 ∧
      CppNestedProgram.runFuel 81 bitWidthCall S = .finished ⟨invokeNext S res,none,false⟩ := by
  have env := env_two_values S P K nI bindings memory kv hn
  have ev : S.scalars.evaluate (.variable ⟨64,false,false⟩ 0) = some ⟨K,1⟩ := by
    simp [CppState.State.evaluate,env,Proofs.CppScalar.Expr.eval,kv]
  obtain ⟨res,call,hv,hm,hw,hp⟩ := Proofs.BitWidthU64.call_bounds K.toNat S.scalars.memory (by omega)
  have cast : ((K.toNat : Nat) : Int) = K := Int.toNat_of_nonneg hK0
  rw [cast] at call
  refine ⟨res,hv,hm,hw,hp,?_⟩
  simp [CppNestedProgram.runFuel,liftChecked,ev,call,Bind.bind,Outcome.bind,pure,invokeNext]
  rfl

section invokeFields
variable (S : NState) (res : CppState.CallResult)
theorem invokeNext_memory : (invokeNext S res).scalars.memory = res.memory ++ [(⟨⟨32,true,false⟩,res.value⟩ : Cell)] := rfl
theorem invokeNext_bindings : (invokeNext S res).scalars.bindings =
    S.scalars.bindings ++ [(⟨S.scalars.memory.length,false⟩ : CppState.Binding)] := rfl
theorem invokeNext_slots : (invokeNext S res).slots = S.slots ++ [.scalar S.scalars.bindings.length] := rfl
theorem invokeNext_scope : (invokeNext S res).scope = S.scope := rfl
theorem invokeNext_frame : (invokeNext S res).frame = S.frame := rfl
theorem invokeNext_base : (invokeNext S res).scalars.baseMemory = S.scalars.baseMemory := rfl
theorem invokeNext_work : (invokeNext S res).scalars.work = S.scalars.work+1+res.work+1 := rfl
theorem invokeNext_scalar_peak : (invokeNext S res).scalars.peak = max (max S.scalars.peak
    (S.scalars.memory.length-S.scalars.baseMemory+S.scalars.bindings.length+res.peak))
    ((res.memory ++ [(⟨⟨32,true,false⟩,res.value⟩ : Cell)]).length-S.scalars.baseMemory+
      (S.scalars.bindings ++ [(⟨S.scalars.memory.length,false⟩ : CppState.Binding)]).length+0) := rfl
theorem invokeNext_peak : (invokeNext S res).peak = max S.peak ((invokeNext S res).scalars.peak+S.frame.state.storage.peak) := rfl
end invokeFields

def slots5 : List Location := [.vector 0,.scalar 0,.scalar 1,.scalar 2,.scalar 3]
def cells3w (F : Fixed) : List Cell := cells2 F ++ [⟨i32,(F.w : Int)⟩]
def binds3w (F : Fixed) : List CppState.Binding := binds2 F ++ [⟨F.P.length+2,false⟩]

theorem invoke_step (F : Fixed) (ok : FixedOK F) {rw0 : List Bool} {W : Nat} (S : NState)
    (hK0 : 0 ≤ F.K) (hK : F.K < 2^64) (hw : F.w = Proofs.BitWidthU64.width F.K.toNat)
    (ps : PS F F.sc rw0 S (cells2 F) (binds2 F) slots3) (cb : Cb F W S) (cap : liveS S+12 ≤ F.SPB) :
    ∃ t, CppNestedProgram.runFuel 81 bitWidthCall S = .finished ⟨t,none,false⟩ ∧
      PS F F.sc rw0 t (cells3w F) (binds3w F) slots4 ∧ t.frame = S.frame ∧ Cb F (W+910) t := by
  have kv : u64.valid F.K = true := by simp [Ty.valid]; omega
  have hn := i32_valid_nat F.n ok.nSmall
  obtain ⟨res,hv,hm,hwk,hp,run⟩ := invoke_run S F.K kv (F.n : Int) hn F.P (by simpa [binds2] using ps.bindings)
    (by simpa [cells2] using ps.memory) hK0 hK
  have mem : S.scalars.memory.length = F.P.length+2 := by simp [ps.memory,cells2]
  have bnd : S.scalars.bindings.length = 2 := by simp [ps.bindings,binds2]
  refine ⟨_,run,⟨?_,?_,?_,?_,?_,?_,?_⟩,invokeNext_frame S res,?_⟩
  · rw [invokeNext_slots,bnd,ps.slots]; simp [slots3,slots4]
  · rw [invokeNext_memory,hm,hv,← hw,ps.memory]; simp [cells3w,cells2]
  · rw [invokeNext_bindings,ps.bindings,mem]; simp [binds3w,binds2]
  · rw [invokeNext_base]; exact ps.base
  · rw [invokeNext_scope]; exact ps.scope
  · rw [invokeNext_frame]; exact ps.frameBindings
  · rw [invokeNext_frame]; exact ps.writable
  · have lv := ps.live_eq
    have hB := ok.base
    have spb := cb.scalarPeak
    have sto := cb.storagePeak
    have out := cb.outerPeak
    have wk := cb.work
    have lv' : liveS S = F.P.length+2-F.B+2 := by rw [lv]; simp [cells2,binds2]
    have sp : (invokeNext S res).scalars.peak ≤ F.SPB := by
      rw [invokeNext_scalar_peak]
      simp only [List.length_append,List.length_singleton,hm,hp,mem,bnd,ps.base]
      unfold liveS at lv'; rw [ps.base,mem,bnd] at lv'; omega
    refine ⟨?_,sp,?_,?_⟩
    · rw [invokeNext_work]; omega
    · rw [invokeNext_frame]; exact sto
    · rw [invokeNext_peak]
      omega

def cells4 (F : Fixed) : List Cell := cells3w F ++ [⟨i32,(F.w : Int)⟩]
def binds4 (F : Fixed) : List CppState.Binding := binds3w F ++ [⟨F.P.length+3,false⟩]

abbrev declW : NStmt := .declare i32 false (.variable i32 3)

theorem declW_step (F : Fixed) (ok : FixedOK F) {rw0 : List Bool} {W : Nat} (S : NState)
    (ps : PS F F.sc rw0 S (cells3w F) (binds3w F) slots4) (cb : Cb F W S) (cap : liveS S+12 ≤ F.SPB) :
    ∃ t, declW.run S = some ⟨t,none,false⟩ ∧ PS F F.sc rw0 t (cells4 F) (binds4 F) slots5 ∧
      t.frame = S.frame ∧ Cb F (W+3) t := by
  have wv := i32_valid_nat F.w ok.wSmall
  have env : envOf S 3 i32 = some (F.w : Int) :=
    envOf_at S 3 2 ⟨F.P.length+2,false⟩ i32 (F.w : Int) (by simp [ps.slots,slots4])
      (by simp [ps.bindings,binds3w,binds2]) (by simp [ps.memory,cells3w,cells2]) wv
  obtain ⟨t,run,frame,sl,sc',me,bi,ba,wl,wu,pl,pu,ql,qu⟩ := declare_good (.variable i32 3) i32 false S (F.w : Int) (F.w : Int)
    (by simp [NExpr.scalarOnly]) (by simp [NExpr.denote,env]) (Ty.convert_of_valid _ _ wv)
  have memLen : S.scalars.memory.length = F.P.length+3 := by simp [ps.memory,cells3w,cells2]
  have bindLen : S.scalars.bindings.length = 3 := by simp [ps.bindings,binds3w,binds2]
  refine ⟨t,run,⟨?_,?_,?_,?_,?_,?_,?_⟩,frame,?_⟩
  · rw [sl,bindLen,ps.slots]; simp [slots4,slots5]
  · rw [me,ps.memory]; simp [cells4]
  · rw [bi,memLen,ps.bindings]; simp [binds4]
  · rw [ba]; exact ps.base
  · rw [sc']; exact ps.scope
  · rw [frame]; exact ps.frameBindings
  · rw [frame]; exact ps.writable
  · have wu' : t.scalars.work ≤ S.scalars.work+3 := by simp [NExpr.nodes] at wu; omega
    have pu' : t.scalars.peak ≤ max S.scalars.peak (liveS S+12) := by simp [NExpr.nodes] at pu; omega
    exact cb.step frame wu' pu' cap qu

end Proofs.DoublingPrologue
