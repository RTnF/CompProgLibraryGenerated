import Proofs.BeatsRep
namespace Proofs.BeatsRep
theorem cflag_stop (qa qb W1 W2 : Nat) (h : qb ≤ W1 ∨ W2 ≤ qa) : ((qb : Int) ≤ (W1 : Int)) ∨ ((W2 : Int) ≤ (qa : Int)) := by omega
theorem cflag_nstop (qa qb W1 W2 : Nat) (h : ¬ (qb ≤ W1 ∨ W2 ≤ qa)) : ¬ (((qb : Int) ≤ (W1 : Int)) ∨ ((W2 : Int) ≤ (qa : Int))) := by omega
theorem cflag_cov (qa qb W1 W2 : Nat) (h : qa ≤ W1 ∧ W2 ≤ qb) : ((qa : Int) ≤ (W1 : Int)) ∧ ((W2 : Int) ≤ (qb : Int)) := by omega
theorem cflag_ncov (qa qb W1 W2 : Nat) (h : ¬ (qa ≤ W1 ∧ W2 ≤ qb)) : ¬ (((qa : Int) ≤ (W1 : Int)) ∧ ((W2 : Int) ≤ (qb : Int))) := by omega
end Proofs.BeatsRep
