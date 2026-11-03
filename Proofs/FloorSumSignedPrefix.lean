import Proofs.FloorSumSignedBranch

namespace Proofs.FloorSumSignedPrefix
open Proofs.CppScalar Proofs.CppState Proofs.CppLoop Proofs.SafeModProofs
open Proofs.FloorSumSignedBranch Proofs.FloorSumSignedCorrection Proofs.FloorSumState Proofs.FloorSumArithmetic

def parameterState (n m a b : Int) (caller : List Cell) (work base peak : Nat) : State :=
  ⟨caller ++ [⟨signed64,n⟩,⟨signed64,m⟩,⟨signed64,a⟩,⟨signed64,b⟩],
    [⟨caller.length,true⟩,⟨caller.length+1,true⟩,⟨caller.length+2,true⟩,⟨caller.length+3,true⟩],work,base,peak⟩

def lowerExpression (slot : Nat) (lower : Int) : Expr :=
  .binary boolType .le (.cast signed64 (.literal ⟨32,true,false⟩ lower)) (.variable signed64 slot)

def upperExpression (slot : Nat) : Expr :=
  .binary boolType .lt (.cast signed64 (.variable signed64 slot))
    (.binary signed64 .mul (.literal signed64 1) (.literal signed64 4294967296))

def falseCheck : Stmt := .check (.literal boolType 0)
def trueCheck : Stmt := .check (.literal boolType 1)

def rangeAssertion (slot : Nat) (lower : Int) : Stmt :=
  .sequence (.branch (lowerExpression slot lower)
    (.branch (upperExpression slot) .skip falseCheck) falseCheck) (.sequence trueCheck .skip)

theorem assertion_runs (n m a b x lower : Int) (caller : List Cell) (work base peak slot : Nat)
    (hn : signed64.valid n = true) (hm : signed64.valid m = true)
    (ha : signed64.valid a = true) (hb : signed64.valid b = true)
    (hx : signed64.valid x = true) (hl32 : (⟨32,true,false⟩ : Ty).valid lower = true)
    (hl64 : signed64.valid lower = true) (lo : lower ≤ x) (hi : x < (inputLimit:Int))
    (sx : ([n,m,a,b] : List Int)[slot]? = some x) :
    runFuel 4 (rangeAssertion slot lower) (parameterState n m a b caller work base peak) =
      .finished ⟨parameterState n m a b caller (work+14) base
        (max peak (caller.length+4-base+10)),none,false⟩ := by
  have outside (i : Nat) : ¬ caller.length+i < caller.length := by omega
  have lowerCast := Ty.convert_of_valid signed64 lower hl64
  have upperCast := Ty.convert_of_valid signed64 x hx
  have upperBound : x < 4294967296 := by change x < 4294967296 at hi; exact hi
  have v1 : signed64.valid 1 = true := by decide
  have vBound : signed64.valid 4294967296 = true := by decide
  have product : signed64.convert 4294967296 = some 4294967296 := by decide
  have b1 : boolType.valid 1 = true := by decide
  have c1 : boolType.convert 1 = some 1 := by decide
  simp [rangeAssertion,lowerExpression,upperExpression,falseCheck,trueCheck,
    runFuel,liftChecked,bind,pure,Outcome.bind,Stmt.run,parameterState,
    State.evaluate,State.environment,State.observe,Expr.eval,Expr.nodes,
    List.getElem?_append,outside,hn,hm,ha,hb,hx,hl32,lowerCast,upperCast,sx,
    binaryValue,lo,upperBound,v1,vBound,product,b1,c1,Nat.add_assoc]

def ansDeclaration : Stmt := .declare unsigned64 true (.cast unsigned64 (.literal ⟨32,true,false⟩ 0))

theorem declare_ans (n m a b : Int) (caller : List Cell) (work base peak : Nat)
    (hn : signed64.valid n = true) (hm : signed64.valid m = true)
    (ha : signed64.valid a = true) (hb : signed64.valid b = true) :
    ansDeclaration.run (parameterState n m a b caller work base peak) =
      some ⟨mainState n m a b 0 caller (work+3) base
        (max peak (caller.length+5-base+7)),none,false⟩ := by
  have outside (i : Nat) : ¬ caller.length+i < caller.length := by omega
  have literal : (⟨32,true,false⟩ : Ty).valid 0 = true := by decide
  have zero : unsigned64.convert 0 = some 0 := by decide
  simp [ansDeclaration,Stmt.run,parameterState,mainState,State.evaluate,State.environment,State.observe,
    Expr.eval,Expr.nodes,List.getElem?_append,outside,hn,hm,ha,hb,literal,zero,Nat.add_assoc]

def inputPrefix : Stmt := .sequence (rangeAssertion 0 0)
  (.sequence (rangeAssertion 1 1) (.sequence ansDeclaration .skip))

theorem prefix_runs (n m : Nat) (a b : Int) (caller : List Cell) (work base peak : Nat)
    (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : signed64.valid a = true) (hb : signed64.valid b = true) :
    runFuel 6 inputPrefix (parameterState n m a b caller work base peak) =
      .finished ⟨mainState n m a b 0 caller (work+31) base
        (max peak (caller.length+4-base+10)),none,false⟩ := by
  have first := assertion_runs n m a b n 0 caller work base peak 0
    (input_signed_valid n hn) (input_signed_valid m hm) ha hb (input_signed_valid n hn)
    (by decide) (by decide) (by omega) (by exact_mod_cast hn) rfl
  have second := assertion_runs n m a b m 1 caller (work+14) base
    (max peak (caller.length+4-base+10)) 1
    (input_signed_valid n hn) (input_signed_valid m hm) ha hb (input_signed_valid m hm)
    (by decide) (by decide) (by omega) (by exact_mod_cast hm) rfl
  simp [Nat.add_assoc,Nat.max_assoc] at second
  have declared := declare_ans n m a b caller (work+28) base
    (max peak (caller.length+4-base+10))
    (input_signed_valid n hn) (input_signed_valid m hm) ha hb
  have declaredFuel := congrArg liftChecked declared
  change runFuel 3 ansDeclaration _ = .finished _ at declaredFuel
  have declaration := sequence_done 3 ansDeclaration .skip _ _ _ declaredFuel rfl
  have checkedM := sequence_done 4 _ _ _ _ _ second declaration
  have paddedN := runFuel_success_mono 4 1 _ _ _ first
  have combined := sequence_done 5 _ _ _ _ _ paddedN checkedM
  have resource : max (caller.length+4-base+10) (caller.length+5-base+7) = caller.length+4-base+10 := by omega
  simpa [inputPrefix,Nat.add_assoc,mainState,Nat.max_assoc,resource] using combined


def preparation : Stmt := .sequence (rangeAssertion 0 0)
  (.sequence (rangeAssertion 1 1) (.sequence (.sequence ansDeclaration .skip) normalizationSequence))

theorem preparation_runs (n m : Nat) (a b : Int) (caller : List Cell) (work base peak : Nat)
    (allocated : base ≤ caller.length) (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : signed64.valid a = true) (hb : signed64.valid b = true) :
    ∃ finalPeak,
      runFuel 20 preparation (parameterState n m a b caller work base peak) =
      .finished ⟨mainState n m (normalizedCoefficient a m) (normalizedCoefficient b m)
        (correctedAns (correctedAns 0 (triangle n:Int) a m) (n:Int) b m) caller
        (work+31+normalizationWork a m 34+normalizationWork b m 25) base finalPeak,none,false⟩ ∧
      finalPeak ≤ max peak (caller.length+35-base) ∧
      31+normalizationWork a m 34+normalizationWork b m 25 ≤ 130 ∧
      0 ≤ normalizedCoefficient a m ∧ 0 ≤ normalizedCoefficient b m := by
  have first := assertion_runs n m a b n 0 caller work base peak 0
    (input_signed_valid n hn) (input_signed_valid m hm) ha hb (input_signed_valid n hn)
    (by decide) (by decide) (by omega) (by exact_mod_cast hn) rfl
  have second := assertion_runs n m a b m 1 caller (work+14) base
    (max peak (caller.length+4-base+10)) 1
    (input_signed_valid n hn) (input_signed_valid m hm) ha hb (input_signed_valid m hm)
    (by decide) (by decide) (by omega) (by exact_mod_cast hm) rfl
  simp [Nat.add_assoc,Nat.max_assoc] at second
  have declared := declare_ans n m a b caller (work+28) base
    (max peak (caller.length+4-base+10))
    (input_signed_valid n hn) (input_signed_valid m hm) ha hb
  have declaredFuel := congrArg liftChecked declared
  change runFuel 3 ansDeclaration _ = .finished _ at declaredFuel
  have declaration := sequence_done 3 ansDeclaration .skip _ _ _ declaredFuel rfl
  have resource : max (caller.length+4-base+10) (caller.length+5-base+7) = caller.length+4-base+10 := by omega
  simp [Nat.add_assoc,Nat.max_assoc,resource] at declaration
  obtain ⟨finalPeak,normalized,bound,workBound,nonnegativeA,nonnegativeB⟩ := both_normalizations n m a b 0 caller
    (work+31) base (max peak (caller.length+4-base+10)) allocated hn hm positive ha hb (by decide)
  have paddedDeclaration := runFuel_success_mono 4 13 _ _ _ declaration
  have tail := sequence_done 17 _ _ _ _ _ paddedDeclaration normalized
  have paddedM := runFuel_success_mono 4 14 _ _ _ second
  have rest := sequence_done 18 _ _ _ _ _ paddedM tail
  have paddedN := runFuel_success_mono 4 15 _ _ _ first
  have combined := sequence_done 19 _ _ _ _ _ paddedN rest
  refine ⟨finalPeak,combined,?_,by omega,nonnegativeA,nonnegativeB⟩
  omega

end Proofs.FloorSumSignedPrefix
