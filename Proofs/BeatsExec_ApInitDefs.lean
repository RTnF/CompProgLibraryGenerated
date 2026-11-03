import Proofs.BeatsExecL1
namespace Proofs.BeatsExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec
set_option maxRecDepth 100000

abbrev ApInitc0_6 (o : Nat) (REST : Command) : Command := REST
abbrev ApInitc0_5 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.assign (o + 6) i32 (.literal i32 (1)))) (ApInitc0_6 o REST)
abbrev ApInitc0_4 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 13) i32 (.cast u64 (.literal i32 (0))) (.variable i32 (o + 1)))) (ApInitc0_5 o REST)
abbrev ApInitc0_3 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 12) i32 (.cast u64 (.literal i32 (0))) (.literal i32 (0)))) (ApInitc0_4 o REST)
abbrev ApInitc0_2 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.write (.local 11) i32 (.cast u64 (.literal i32 (0))) (.literal i32 (0)))) (ApInitc0_3 o REST)
abbrev ApInitc0_1 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (ApInitc0_2 o REST)
abbrev ApInitc0_0 (o : Nat) (REST : Command) : Command := .sequence (.primitive (.declare i32 true (.literal i32 (0)))) (ApInitc0_1 o REST)
abbrev ApInitc0 (o : Nat) (REST : Command) : Command := ApInitc0_0 o REST
abbrev ApInitBody (o : Nat) : Command := ApInitc0 o (Sk)

def ui1 (s : BS) (idx : Nat) (a : Int) : BS := { s with sk := s.sk.set idx a }
def ui2 (s : BS) (idx : Nat) (a : Int) : BS := { s with sl := s.sl.set idx a }
def ui3 (s : BS) (idx : Nat) (a : Int) : BS := { s with sr := s.sr.set idx a }


end Proofs.BeatsExec
