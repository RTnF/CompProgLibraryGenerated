import Proofs.UfMethodPreparePeak
import Proofs.UfReceiverScalarPeak

namespace Proofs.UfUniformScalarPeak
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop Proofs.CppNestedEval
open Proofs.UfReceiverState Proofs.UfReceiverTrace Proofs.UfBalancedReceiver Proofs.CppCallFrame
open Proofs.DoublingNested (i32)

def budget (s : NState) : Nat := liveS s+s.frame.bindings.length+112

theorem budget_call (s : NState) (base : s.scalars.baseMemory ≤ s.scalars.memory.length) :
    (Proofs.DoublingCall.callerP s).length+12-s.scalars.baseMemory+100 = budget s := by
  simp only [Proofs.DoublingCall.callerP,List.length_append,List.length_replicate,budget,liveS]
  omega

theorem budget_kept {s t : NState} (effects : CallEffects s t) : budget t = budget s := by
  simp only [budget,effects.scalarLive,effects.vectorBindings]

theorem prepare_peak (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Represents s layout ps count rank) (op : Operation) (allowed : op.allowed ps.length) :
    ∃ init, prepare s op.program.parameters (arguments layout++op.extra) = some init ∧
      init.scalars.peak ≤ max s.scalars.peak (liveS s+s.frame.bindings.length+15) := by
  obtain ⟨buf,cb,nb,inv⟩ := represented
  have nvalid := Proofs.VectorSumCall.i32_valid (ps.length : Int) (by omega) (by have h := inv.math.length; omega)
  cases op with
  | root a | size a =>
    change a < ps.length at allowed
    have av := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by have h := inv.math.length; omega)
    obtain ⟨init,prep,peak⟩ := Proofs.UfMethodPreparePeak.prepare_fields_peak s inv.ok cb count inv.countCell inv.writable
      (nExpr layout) (.literal i32 a) ps.length a rfl rfl rfl rfl inv.n_value (literal_value a av s) nvalid av
    refine ⟨init,prep,?_⟩
    simp only [nExpr,NExpr.nodes] at peak
    clear * - peak
    omega
  | same a b | unite a b =>
    change a < ps.length ∧ b < ps.length at allowed
    have av := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by have h := inv.math.length; omega)
    have bv := Proofs.VectorSumCall.i32_valid (b : Int) (by omega) (by have h := inv.math.length; omega)
    obtain ⟨init,prep,peak⟩ := Proofs.UfMethodPreparePeak.prepare_same_peak s inv.ok cb count inv.countCell inv.writable
      (nExpr layout) (.literal i32 a) (.literal i32 b) ps.length a b rfl rfl rfl rfl rfl rfl
      inv.n_value (literal_value a av s) (literal_value b bv s) nvalid av bv
    refine ⟨init,prep,?_⟩
    simp only [nExpr,NExpr.nodes] at peak
    clear * - peak
    omega
  | numGroups =>
    obtain ⟨init,prep,peak⟩ := Proofs.UfMethodPreparePeak.prepare_counter_peak s inv.ok cb count inv.countCell inv.writable
      (nExpr layout) ps.length rfl rfl inv.n_value nvalid
    refine ⟨init,prep,?_⟩
    simp only [nExpr,NExpr.nodes] at peak
    clear * - peak
    omega

theorem call_peak (fuel : Nat) (s out : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Represents s layout ps count rank) (op : Operation) (allowed : op.allowed ps.length) (result : Ret)
    (actual : call fuel s layout op = .finished (out,result)) :
    out.scalars.peak ≤ max s.scalars.peak (budget s) := by
  obtain ⟨init,prep,peak⟩ := Proofs.UfReceiverScalarPeak.call_peak fuel s out layout ps count rank represented op allowed result actual
  obtain ⟨prepared,preparedEq,preparedPeak⟩ := prepare_peak s layout ps count rank represented op allowed
  have eq := Option.some.inj (preparedEq.symm.trans prep)
  subst prepared
  obtain ⟨buf,cb,nb,inv⟩ := represented
  rw [budget_call s inv.ok.base] at peak
  unfold budget at *
  clear * - peak preparedPeak
  omega

theorem calls_peak (ops : List Operation) (s : NState) (layout : Layout)
    (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Strong s layout ps count rank) (allowed : ∀ op ∈ ops, op.allowed ps.length) :
    ∃ fuels out vec nextCount nextRank answers,
      runCalls fuels ops s layout = .finished (out,answers) ∧
      Strong out layout vec nextCount nextRank ∧ vec.length = ps.length ∧
      fuels.length = ops.length ∧ answers.length = ops.length ∧
      out.work ≤ s.work+ops.length*Proofs.UfTraceWork.budget ps.length ∧
      out.scalars.peak ≤ max s.scalars.peak (budget s) := by
  induction ops generalizing s ps count rank with
  | nil => exact ⟨[],s,ps,count,rank,[],rfl,represented,rfl,rfl,rfl,by simp,Nat.le_max_left _ _⟩
  | cons op ops ih =>
    obtain ⟨fuel,middle,vec1,count1,rank1,answer,ran,rep,length1,headWork⟩ :=
      Proofs.UfTraceWork.step_work s layout ps count rank represented op (allowed op (by simp))
    have headPeak := call_peak fuel s middle layout ps count rank represented.1 op (allowed op (by simp)) (.scalar answer) ran
    obtain ⟨buf,cb,nb,inv⟩ := represented.1
    have effects := Proofs.UfReceiverMetadata.call_effect fuel s middle layout op (.scalar answer) inv.ok.strict ran
    have sameBudget := budget_kept effects
    have tailAllowed : ∀ other ∈ ops, other.allowed vec1.length := by
      intro other member
      rw [length1]
      exact allowed other (by simp [member])
    obtain ⟨fuels,out,vec,count2,rank2,answers,tailRun,finalRep,length2,fuelsLength,answersLength,tailWork,tailPeak⟩ :=
      ih middle vec1 count1 rank1 rep tailAllowed
    refine ⟨fuel::fuels,out,vec,count2,rank2,answer::answers,?_,finalRep,length2.trans length1,?_,?_,?_,?_⟩
    · simp only [runCalls,ran,bind,Outcome.bind,tailRun,pure]
    · simp [fuelsLength]
    · simp [answersLength]
    · rw [length1] at tailWork
      simp only [List.length_cons,Nat.succ_mul]
      omega
    · rw [sameBudget] at tailPeak
      clear * - headPeak tailPeak
      omega


theorem run_calls_unique (ops : List Operation) (first second : List Nat) (s : NState) (layout : Layout)
    (a b : NState × List Int) (one : runCalls first ops s layout = .finished a)
    (two : runCalls second ops s layout = .finished b) : a = b := by
  induction ops generalizing first second s a b with
  | nil =>
    cases first with
    | cons f fs => simp [runCalls] at one
    | nil =>
      cases second with
      | cons f fs => simp [runCalls] at two
      | nil => exact (Outcome.finished.inj one).symm.trans (Outcome.finished.inj two)
  | cons op ops ih =>
    cases first with
    | nil => simp [runCalls] at one
    | cons f fs =>
      cases second with
      | nil => simp [runCalls] at two
      | cons g gs =>
        cases r1 : call f s layout op with
        | fault => simp [runCalls,r1,bind,Outcome.bind] at one
        | exhausted => simp [runCalls,r1,bind,Outcome.bind] at one
        | finished pair1 =>
          obtain ⟨mid,ret⟩ := pair1
          cases r2 : call g s layout op with
          | fault => simp [runCalls,r2,bind,Outcome.bind] at two
          | exhausted => simp [runCalls,r2,bind,Outcome.bind] at two
          | finished pair2 =>
            have eq := Proofs.CppCallUnique.call_unique op.program f g s (arguments layout++op.extra) (mid,ret) pair2 r1 r2
            subst pair2
            cases ret with
            | unit => simp [runCalls,r1,bind,Outcome.bind] at one
            | vector owner element => simp [runCalls,r1,bind,Outcome.bind] at one
            | scalar answer =>
              cases tail1 : runCalls fs ops mid layout with
              | fault => simp [runCalls,r1,tail1,bind,Outcome.bind] at one
              | exhausted => simp [runCalls,r1,tail1,bind,Outcome.bind] at one
              | finished pair1 =>
                cases tail2 : runCalls gs ops mid layout with
                | fault => simp [runCalls,r2,tail2,bind,Outcome.bind] at two
                | exhausted => simp [runCalls,r2,tail2,bind,Outcome.bind] at two
                | finished pair2 =>
                  have eq := ih fs gs mid pair1 pair2 tail1 tail2
                  subst pair2
                  simp only [runCalls,r1,tail1,bind,Outcome.bind] at one
                  simp only [runCalls,r2,tail2,bind,Outcome.bind] at two
                  exact (Outcome.finished.inj one).symm.trans (Outcome.finished.inj two)

theorem actual_calls_peak (fuels : List Nat) (ops : List Operation) (s : NState) (layout : Layout)
    (out : NState) (answers : List Int) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Strong s layout ps count rank) (allowed : ∀ op ∈ ops, op.allowed ps.length)
    (actual : runCalls fuels ops s layout = .finished (out,answers)) :
    out.scalars.peak ≤ max s.scalars.peak (budget s) := by
  obtain ⟨builtFuels,computed,vec,nextCount,nextRank,builtAnswers,ran,strong,length,fuelsLength,answersLength,work,peak⟩ :=
    calls_peak ops s layout ps count rank represented allowed
  have same := run_calls_unique ops builtFuels fuels s layout (computed,builtAnswers) (out,answers) ran actual
  have outEq := congrArg Prod.fst same
  change computed = out at outEq
  rw [← outEq]
  exact peak

end Proofs.UfUniformScalarPeak
