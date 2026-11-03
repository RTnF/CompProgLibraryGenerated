import Proofs.FloorSumSignedArithmetic
import Proofs.FloorSumState
import Proofs.SafeModProofs
import Proofs.CppTargetCast

namespace Proofs.FloorSumSignedCorrection
open Proofs.CppScalar Proofs.FloorSumArithmetic Proofs.FloorSumState
open Proofs.FloorSumSignedArithmetic Proofs.SafeModProofs

theorem difference_range (x : Int) (m : Nat) (hx : signed64.valid x = true)
    (hm : m < inputLimit) (positive : 0 < m) (negative : x < 0) :
    0 ≤ x%(m:Int)-x ∧ x%(m:Int)-x < (wordLimit:Int) := by
  have bx : -9223372036854775808 ≤ x ∧ x < 9223372036854775808 := of_decide_eq_true hx
  have low := Int.emod_nonneg x (by omega : (m:Int) ≠ 0)
  have high := Int.emod_lt_of_pos x (by omega : 0 < (m:Int))
  simp only [inputLimit] at hm
  simp only [wordLimit]
  omega

theorem wrapped_difference (r x : Int)
    (low : 0 ≤ r-x) (high : r-x < (wordLimit:Int)) :
    (r-x%(wordLimit:Int))%(wordLimit:Int) = r-x := by
  simpa only [Int.sub_emod,Int.emod_emod] using Int.emod_eq_of_lt low high

theorem quotient_exact (x : Int) (m : Nat) (hx : signed64.valid x = true)
    (hm : m < inputLimit) (positive : 0 < m) (negative : x < 0) :
    ((x%(m:Int)-x%(wordLimit:Int))%(wordLimit:Int)).tdiv m = -(x/(m:Int)) := by
  have range := difference_range x m hx hm positive negative
  rw [wrapped_difference _ _ range.1 range.2,Int.tdiv_eq_ediv_of_nonneg range.1]
  exact coefficient_correction (m:Int) x (by omega)

def quotientExpression : Expr :=
  .divrem unsigned64 false
    (.binary unsigned64 .sub (.variable unsigned64 0) (.cast unsigned64 (.variable signed64 1)))
    (.cast unsigned64 (.variable signed64 2))

theorem quotient_eval_of_checked (r x m encoded diff quotient : Int)
    (vr : unsigned64.valid r = true) (vx : signed64.valid x = true) (vm : signed64.valid m = true)
    (castx : unsigned64.convert x = some encoded) (castm : unsigned64.convert m = some m)
    (sub : unsigned64.convert (r-encoded) = some diff)
    (div : checkedDivRem unsigned64 false diff m = some quotient) :
    quotientExpression.eval [r,x,m] = some ⟨quotient,7⟩ := by
  simp [quotientExpression,Expr.eval,binaryValue,vr,vx,vm,castx,castm,sub,div]

theorem input_signed_valid (m : Nat) (hm : m < inputLimit) : signed64.valid (m:Int) = true := by
  simp only [signed64,Ty.valid,Bool.false_eq_true,ite_false,ite_true]
  apply decide_eq_true
  simp [inputLimit] at hm
  omega

theorem quotient_eval (x : Int) (m : Nat) (hx : signed64.valid x = true)
    (hm : m < inputLimit) (positive : 0 < m) (negative : x < 0) :
    quotientExpression.eval [x%(m:Int),x,(m:Int)] = some ⟨-(x/(m:Int)),7⟩ := by
  have range := difference_range x m hx hm positive negative
  have low := Int.emod_nonneg x (by omega : (m:Int) ≠ 0)
  have high := Int.emod_lt_of_pos x (by omega : 0 < (m:Int))
  have bm : (m:Int) < (wordLimit:Int) := by simp [inputLimit,wordLimit] at *; omega
  have vr : unsigned64.valid (x%(m:Int)) = true := by
    show decide (0 ≤ x%(m:Int) ∧ x%(m:Int) < 18446744073709551616) = true
    apply decide_eq_true
    simp [wordLimit] at bm
    omega
  have vm := input_signed_valid m hm
  have wrap := wrapped_difference (x%(m:Int)) x range.1 range.2
  have mmod := Int.emod_eq_of_lt (show 0 ≤ (m:Int) by omega) bm
  have qlow := Int.tdiv_nonneg range.1 (show 0 ≤ (m:Int) by omega)
  have qhigh := Int.tdiv_le_self (m:Int) range.1
  have qvalid : unsigned64.valid ((x%(m:Int)-x).tdiv m) = true := by
    show decide (0 ≤ (x%(m:Int)-x).tdiv m ∧ (x%(m:Int)-x).tdiv m < 18446744073709551616) = true
    apply decide_eq_true
    simp [wordLimit] at range
    omega
  have div := checkedDivRem_division_exact unsigned64 (x%(m:Int)-x) m (by omega) qvalid
  have result : (x%(m:Int)-x).tdiv m = -(x/(m:Int)) := by
    rw [Int.tdiv_eq_ediv_of_nonneg range.1]
    exact coefficient_correction (m:Int) x (by omega)
  have castx : unsigned64.convert x = some (x%(wordLimit:Int)) := by
    simp [unsigned64,Ty.convert,wordLimit]
  have castm : unsigned64.convert (m:Int) = some (m:Int) := by
    simpa [unsigned64,Ty.convert,wordLimit] using congrArg some mmod
  have sub : unsigned64.convert (x%(m:Int)-x%(wordLimit:Int)) = some (x%(m:Int)-x) := by
    simpa [unsigned64,Ty.convert,wordLimit] using congrArg some wrap
  rw [result] at div
  exact quotient_eval_of_checked _ _ _ _ _ _ vr hx vm castx castm sub div

theorem normalized_targetCast (x : Int) (m : Nat) (hm : m < inputLimit) (positive : 0 < m) :
    signed64.targetConvert (x%(m:Int)) = some (x%(m:Int)) := by
  have low := Int.emod_nonneg x (by omega : (m:Int) ≠ 0)
  have high := Int.emod_lt_of_pos x (by omega : 0 < (m:Int))
  have bounds : -(2^(64-1):Int) ≤ x%(m:Int) ∧ x%(m:Int) < 2^(64-1) := by
    simp only [inputLimit] at hm
    constructor <;> omega
  have decoded := Proofs.CppTargetCast.decode_exact 64 (x%(m:Int)) (by decide) bounds.1 bounds.2
  simp [signed64,Ty.targetConvert,decoded]

def signedTriangleExpression : Expr :=
  .divrem unsigned64 false
    (.binary unsigned64 .mul (.cast unsigned64 (.variable signed64 0))
      (.cast unsigned64 (.binary signed64 .sub (.variable signed64 0)
        (.cast signed64 (.literal ⟨32,true,false⟩ 1)))))
    (.cast unsigned64 (.literal ⟨32,true,false⟩ 2))

theorem signedTriangle_eval_checked (n pred product : Int)
    (vn : signed64.valid n = true) (vs : signed64.valid (n-1) = true)
    (castn : unsigned64.convert n = some n)
    (castpred : unsigned64.convert (n-1) = some pred)
    (castproduct : unsigned64.convert (n*pred) = some product)
    (vq : unsigned64.valid (product.tdiv 2) = true) (tail : List Int := []) :
    signedTriangleExpression.eval (n::tail) = some ⟨product.tdiv 2,11⟩ := by
  have c1 : signed64.convert 1 = some 1 := by decide
  have c2 : unsigned64.convert 2 = some 2 := by decide
  have l1 : (⟨32,true,false⟩ : Ty).valid 1 = true := by decide
  have l2 : (⟨32,true,false⟩ : Ty).valid 2 = true := by decide
  have sub := Ty.convert_of_valid signed64 (n-1) vs
  have div := checkedDivRem_division_exact unsigned64 product 2 (by decide) vq
  simp [signedTriangleExpression,Expr.eval,binaryValue,vn,c1,c2,l1,l2,sub,castn,castpred,castproduct,div]

theorem signed_pred_valid (n : Nat) (hn : n < inputLimit) : signed64.valid ((n:Int)-1) = true := by
  simp only [signed64,Ty.valid,Bool.false_eq_true,ite_false,ite_true]
  apply decide_eq_true
  simp only [inputLimit] at hn
  constructor <;> omega

theorem signedTriangle_eval (n : Nat) (hn : n < inputLimit) (tail : List Int := []) :
    signedTriangleExpression.eval ((n:Int)::tail) = some ⟨(triangle n : Nat),11⟩ := by
  have vn := input_signed_valid n hn
  have vs := signed_pred_valid n hn
  by_cases zero : n = 0
  · subst n
    have evaluated := signedTriangle_eval_checked 0 (wordLimit-1 : Nat) 0
      vn vs (by decide) (by decide) (by decide) (by decide) tail
    simpa [triangle] using evaluated
  · have nb : n < wordLimit := by simp [inputLimit,wordLimit] at *; omega
    have pb : n-1 < wordLimit := by omega
    have productBound := triangular_product_bound n hn
    have quotientBound : n*(n-1)/2 < wordLimit := by
      have bounded := Nat.div_le_self (n*(n-1)) 2
      omega
    have sub : (n:Int)-1 = ((n-1 : Nat):Int) := by omega
    have castn := Ty.convert_of_valid unsigned64 (n:Int) (unsigned64_valid n nb)
    have castpred : unsigned64.convert ((n:Int)-1) = some ((n-1 : Nat):Int) := by
      rw [sub]
      exact Ty.convert_of_valid unsigned64 _ (unsigned64_valid (n-1) pb)
    have castproduct : unsigned64.convert ((n:Int)*((n-1 : Nat):Int)) = some ((n*(n-1) : Nat):Int) := by
      simpa only [Int.natCast_mul] using
        Ty.convert_of_valid unsigned64 ((n*(n-1) : Nat):Int) (unsigned64_valid _ productBound)
    have qeq : ((n*(n-1) : Nat):Int).tdiv 2 = ((n*(n-1)/2 : Nat):Int) := rfl
    have vq : unsigned64.valid (((n*(n-1) : Nat):Int).tdiv 2) = true := by
      rw [qeq]
      exact unsigned64_valid _ quotientBound
    simpa only [qeq,triangle] using signedTriangle_eval_checked (n:Int) (n-1 : Nat) (n*(n-1) : Nat)
      vn vs castn castpred castproduct vq tail

theorem unsigned_product_eval (left right : Expr) (env : List Int) (a b : Int) (wa wb : Nat)
    (hl : left.eval env = some ⟨a,wa⟩) (hr : right.eval env = some ⟨b,wb⟩) :
    (Expr.binary unsigned64 .mul left right).eval env = some ⟨(a*b)%(wordLimit:Int),wa+wb+1⟩ := by
  simp [Expr.eval,hl,hr,binaryValue,unsigned64,Ty.convert,wordLimit]

theorem unsigned_subtract_eval (left right : Expr) (env : List Int) (a b : Int) (wa wb : Nat)
    (hl : left.eval env = some ⟨a,wa⟩) (hr : right.eval env = some ⟨b,wb⟩) :
    (Expr.binary unsigned64 .sub left right).eval env = some ⟨(a-b)%(wordLimit:Int),wa+wb+1⟩ := by
  simp [Expr.eval,hl,hr,binaryValue,unsigned64,Ty.convert,wordLimit]

def triangleProductExpression : Expr :=
  .binary unsigned64 .mul signedTriangleExpression (.variable unsigned64 1)

theorem triangleProduct_eval_checked (n coefficient tri : Int)
    (ht : signedTriangleExpression.eval [n,coefficient] = some ⟨tri,11⟩)
    (hc : unsigned64.valid coefficient = true) :
    triangleProductExpression.eval [n,coefficient] = some ⟨(tri*coefficient)%(wordLimit:Int),13⟩ := by
  have hr : (Expr.variable unsigned64 1).eval [n,coefficient] = some ⟨coefficient,1⟩ := by
    simp [Expr.eval,hc]
  exact unsigned_product_eval _ _ _ _ _ _ _ ht hr

theorem triangleProduct_eval (n coefficient : Nat) (hn : n < inputLimit)
    (hc : coefficient < wordLimit) :
    triangleProductExpression.eval [(n:Int),(coefficient:Int)] =
      some ⟨((triangle n:Int)*(coefficient:Int))%(wordLimit:Int),13⟩ :=
  triangleProduct_eval_checked _ _ _ (signedTriangle_eval n hn [(coefficient:Int)])
    (unsigned64_valid coefficient hc)

theorem subtract_product_modulo (ans product : Int) :
    (ans-product%(wordLimit:Int))%(wordLimit:Int) = (ans-product)%(wordLimit:Int) := by
  simp only [Int.sub_emod,Int.emod_emod]


-- Move a proved expression to the slots assigned by the C++ lowering pass.
def reindex (slots : Nat → Nat) : Expr → Expr
  | .literal ty v => .literal ty v
  | .variable ty i => .variable ty (slots i)
  | .cast ty e => .cast ty (reindex slots e)
  | .targetCast ty e => .targetCast ty (reindex slots e)
  | .unary ty op e => .unary ty op (reindex slots e)
  | .binary ty op l r => .binary ty op (reindex slots l) (reindex slots r)
  | .divrem ty rem l r => .divrem ty rem (reindex slots l) (reindex slots r)

def SlotAgreement (slots : Nat → Nat) (source target : List Int) : Expr → Prop
  | .literal .. => True
  | .variable _ i => target[slots i]? = source[i]?
  | .cast _ e | .targetCast _ e | .unary _ _ e => SlotAgreement slots source target e
  | .binary _ _ l r | .divrem _ _ l r =>
      SlotAgreement slots source target l ∧ SlotAgreement slots source target r

theorem reindex_eval (e : Expr) (slots : Nat → Nat) (source target : List Int)
    (h : SlotAgreement slots source target e) :
    (reindex slots e).eval target = e.eval source := by
  induction e with
  | literal ty v => rfl
  | «variable» ty i =>
      change target[slots i]? = source[i]? at h
      simp only [reindex,Expr.eval,h]
  | cast ty e ih => simp only [reindex,Expr.eval,ih h]
  | targetCast ty e ih => simp only [reindex,Expr.eval,ih h]
  | unary ty op e ih => simp only [reindex,Expr.eval,ih h]
  | binary ty op l r il ir => simp only [reindex,Expr.eval,il h.1,ir h.2]
  | divrem ty rem l r il ir => simp only [reindex,Expr.eval,il h.1,ir h.2]

theorem reindex_nodes (e : Expr) (slots : Nat → Nat) :
    (reindex slots e).nodes = e.nodes := by
  induction e <;> simp_all [reindex,Expr.nodes]

def correctionSlots (coefficientSlot : Nat) : Nat → Nat
  | 0 => 6
  | 1 => coefficientSlot
  | _ => 1

def aCorrectionExpression : Expr :=
  .binary unsigned64 .mul signedTriangleExpression (reindex (correctionSlots 2) quotientExpression)

def bCorrectionExpression : Expr :=
  .binary unsigned64 .mul (.cast unsigned64 (.variable signed64 0))
    (reindex (correctionSlots 3) quotientExpression)

theorem aCorrection_eval (n m : Nat) (a b ans temporary : Int) (tail : List Int)
    (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : signed64.valid a = true) (negative : a < 0) :
    aCorrectionExpression.eval ((n:Int)::(m:Int)::a::b::ans::temporary::(a%(m:Int))::tail) =
      some ⟨((triangle n:Int)*(-(a/(m:Int))))%(wordLimit:Int),19⟩ := by
  have agree : SlotAgreement (correctionSlots 2) [a%(m:Int),a,(m:Int)]
      ((n:Int)::(m:Int)::a::b::ans::temporary::(a%(m:Int))::tail) quotientExpression := by
    simp [SlotAgreement,quotientExpression,correctionSlots]
  have quotient := reindex_eval quotientExpression (correctionSlots 2) _ _ agree
  rw [quotient_eval a m ha hm positive negative] at quotient
  exact unsigned_product_eval _ _ _ _ _ _ _
    (signedTriangle_eval n hn ((m:Int)::a::b::ans::temporary::(a%(m:Int))::tail)) quotient

theorem unsigned_head_cast_eval (n : Int) (tail : List Int)
    (vn : signed64.valid n = true) (cn : unsigned64.convert n = some n) :
    (Expr.cast unsigned64 (.variable signed64 0)).eval (n::tail) = some ⟨n,2⟩ := by
  simp [Expr.eval,vn,cn]

theorem bCorrection_eval (n m : Nat) (a b ans temporary : Int) (tail : List Int)
    (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (hb : signed64.valid b = true) (negative : b < 0) :
    bCorrectionExpression.eval ((n:Int)::(m:Int)::a::b::ans::temporary::(b%(m:Int))::tail) =
      some ⟨((n:Int)*(-(b/(m:Int))))%(wordLimit:Int),10⟩ := by
  have agree : SlotAgreement (correctionSlots 3) [b%(m:Int),b,(m:Int)]
      ((n:Int)::(m:Int)::a::b::ans::temporary::(b%(m:Int))::tail) quotientExpression := by
    simp [SlotAgreement,quotientExpression,correctionSlots]
  have quotient := reindex_eval quotientExpression (correctionSlots 3) _ _ agree
  rw [quotient_eval b m hb hm positive negative] at quotient
  have castn := Ty.convert_of_valid unsigned64 (n:Int)
    (unsigned64_valid n (by simp [inputLimit,wordLimit] at *; omega))
  have evaluated := unsigned_head_cast_eval (n:Int)
    ((m:Int)::a::b::ans::temporary::(b%(m:Int))::tail) (input_signed_valid n hn) castn
  exact unsigned_product_eval _ _ _ _ _ _ _ evaluated quotient


def ansUpdateExpression (product : Expr) : Expr :=
  .binary unsigned64 .sub (.variable unsigned64 4) product

theorem ansUpdate_eval (product : Expr) (env : List Int) (ans value : Int) (work : Nat)
    (slot : env[4]? = some ans) (valid : unsigned64.valid ans = true)
    (hp : product.eval env = some ⟨value,work⟩) :
    (ansUpdateExpression product).eval env = some ⟨(ans-value)%(wordLimit:Int),work+2⟩ := by
  have evaluated : (Expr.variable unsigned64 4).eval env = some ⟨ans,1⟩ := by
    simp [Expr.eval,slot,valid]
  simpa only [ansUpdateExpression,Nat.add_comm 1 work,Nat.add_assoc] using
    unsigned_subtract_eval (.variable unsigned64 4) product env ans value 1 work evaluated hp

theorem aAnsUpdate_eval (n m : Nat) (a b ans temporary : Int) (tail : List Int)
    (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : signed64.valid a = true) (negative : a < 0)
    (valid : unsigned64.valid ans = true) :
    (ansUpdateExpression aCorrectionExpression).eval
      ((n:Int)::(m:Int)::a::b::ans::temporary::(a%(m:Int))::tail) =
      some ⟨(ans-(triangle n:Int)*(-(a/(m:Int))))%(wordLimit:Int),21⟩ := by
  have result := ansUpdate_eval aCorrectionExpression _ ans _ 19 (by rfl) valid
    (aCorrection_eval n m a b ans temporary tail hn hm positive ha negative)
  simpa only [subtract_product_modulo] using result

theorem bAnsUpdate_eval (n m : Nat) (a b ans temporary : Int) (tail : List Int)
    (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (hb : signed64.valid b = true) (negative : b < 0)
    (valid : unsigned64.valid ans = true) :
    (ansUpdateExpression bCorrectionExpression).eval
      ((n:Int)::(m:Int)::a::b::ans::temporary::(b%(m:Int))::tail) =
      some ⟨(ans-(n:Int)*(-(b/(m:Int))))%(wordLimit:Int),12⟩ := by
  have result := ansUpdate_eval bCorrectionExpression _ ans _ 10 (by rfl) valid
    (bCorrection_eval n m a b ans temporary tail hn hm positive hb negative)
  simpa only [subtract_product_modulo] using result

end Proofs.FloorSumSignedCorrection
