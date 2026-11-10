import Proofs.CppClassCopyCommands
import Proofs.CppConstructorMultiFinish
import Proofs.CppConstructorView
import Proofs.CppFrameResolveExtension
import Proofs.CppNestedCall
import Proofs.MemberSupport
import Proofs.GenericLazy
import Proofs.MonoidLazyCall
import Proofs.CppScalarValuePrepare
import Proofs.CppScalarContents
import Proofs.GenericExtrema
import Proofs.GenericCall
open Proofs.CppScalar
namespace CopiedScalarFieldsAudit
open Proofs
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.StraightLine Proofs.ScalarStraight Proofs.IntSim Proofs.ModIntCall
open Proofs.ModIntExec Proofs.PowModStep Proofs.PexecKit Proofs.QuotientSearch
open Proofs.ExtremaCall
open Proofs.CppState (Cell)

open Proofs.GroupCall


open Proofs.MonoidLazyCall Proofs.MonoidCall

abbrev copyPicked (k : Nat) (t1 t2 : Ty) (second : Bool) : NExpr :=
  if second then .variable t2 (k+1) else .variable t1 k

def copyBody (k : Nat) (t1 t2 : Ty) (xe ye : NExpr) (second : Bool) : Command :=
  .sequence (.primitive (.declare t1 true xe))
    (.sequence (.primitive (.declare t2 true ye))
      (.sequence (.primitive (.ret (copyPicked k t1 t2 second))) Sk))

theorem copy_exec (P : List Cell) (R : List CppState.Binding) (t1 t2 : Ty)
    (xe ye : NExpr) (x y : Int) (second : Bool)
    (hx : t1.valid x = true) (hy : t2.valid y = true)
    (dx : xe.denote (penv (ws P R [])) = some x)
    (dy : ye.denote (penv (ws P R [⟨t1,x⟩])) = some y) :
    ∃ r, pexec 1 (copyBody R.length t1 t2 xe ye second) (ws P R []) = some r ∧
      r.ret = some (if second then y else x) ∧ r.cost ≤ xe.nodes+ye.nodes+4 ∧
      r.need ≤ P.length+R.length+xe.nodes+ye.nodes+12 ∧
      r.ps = ws P R [⟨t1,x⟩,⟨t2,y⟩] := by
  let L1 : List Cell := [⟨t1,x⟩]
  let L2 : List Cell := [⟨t1,x⟩,⟨t2,y⟩]
  have q1 := (pexec_prim 1 _ _).trans (ws_declare P R [] t1 xe x dx (Ty.convert_of_valid _ _ hx))
  have q2 := (pexec_prim 1 _ _).trans (ws_declare P R L1 t2 ye y dy (Ty.convert_of_valid _ _ hy))
  have dpick : (copyPicked R.length t1 t2 second).denote (penv (ws P R L2)) =
      some (if second then y else x) := by
    cases second
    · change (NExpr.variable t1 R.length).denote (penv (ws P R L2)) = some x
      rw [den_variable]
      exact ws_env_loc P R L2 0 ⟨t1,x⟩ t1 rfl rfl hx
    · change (NExpr.variable t2 (R.length+1)).denote (penv (ws P R L2)) = some y
      rw [den_variable]
      exact ws_env_loc P R L2 1 ⟨t2,y⟩ t2 rfl rfl hy
  have qr := exec_ret 1 (ws P R L2) (copyPicked R.length t1 t2 second)
    (if second then y else x) dpick
  refine ⟨_,seq_some q1 rfl (seq_some q2 rfl qr),rfl,?_,?_,rfl⟩
  · cases second <;> simp [copyPicked,NExpr.nodes] <;> omega
  · cases second <;> simp [copyPicked,NExpr.nodes,ws,L1,L2] <;> omega

def copyBlock (k : Nat) (t1 t2 : Ty) (xe ye : NExpr) (second : Bool) : Command :=
  .sequence (.scope (copyBody k t1 t2 xe ye second)) Sk

theorem copy_block_exec (P : List Cell) (R : List CppState.Binding) (t1 t2 : Ty)
    (xe ye : NExpr) (x y : Int) (second : Bool)
    (hx : t1.valid x = true) (hy : t2.valid y = true)
    (dx : xe.denote (penv (ws P R [])) = some x)
    (dy : ye.denote (penv (ws P R [⟨t1,x⟩])) = some y) :
    ∃ r, pexec 1 (copyBlock R.length t1 t2 xe ye second) ⟨P,R⟩ = some r ∧
      r.ret = some (if second then y else x) ∧ r.cost ≤ xe.nodes+ye.nodes+5 ∧
      r.need ≤ P.length+R.length+xe.nodes+ye.nodes+12 ∧ r.ps = ⟨P,R⟩ := by
  obtain ⟨r,ran,ret,cost,need,ps⟩ := copy_exec P R t1 t2 xe ye x y second hx hy dx dy
  simp only [ws_nil] at ran
  have sc := pexec_scope 1 _ (⟨P,R⟩ : PS) r ran
  refine ⟨_,seq_ret (b:=Sk) sc ret,ret,?_,need,?_⟩
  · simp only
    omega
  · rw [ps]
    simp [ws]

end CopiedScalarFieldsAudit

