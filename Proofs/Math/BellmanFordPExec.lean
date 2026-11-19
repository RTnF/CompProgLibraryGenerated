import Proofs.Math.BellmanFordExec

namespace Proofs.BellmanFordPExec

open Proofs.BellmanFordExec

/-- The parent list after relaxing edge `e` (the distance list is `D` before the relaxation). -/
def relaxPL (inf : Int) (F T : List Nat) (Cc : List Int) (e : Nat) (D Pp : List Int) : List Int :=
  if D.getD (F.getD e 0) 0 ≠ inf ∧ D.getD (F.getD e 0) 0 + Cc.getD e 0 < D.getD (T.getD e 0) 0
  then Pp.set (T.getD e 0) ((F.getD e 0 : Nat) : Int) else Pp

/-- The parent list after relaxing the edges `0 .. t-1` in order (the distance list before edge `e` is `passPrefix e`). -/
def passPrefixP (inf : Int) (F T : List Nat) (Cc : List Int) (t : Nat) (D0 P0 : List Int) : List Int :=
  (List.range t).foldl (fun p e => relaxPL inf F T Cc e (passPrefix inf F T Cc e D0) p) P0

theorem passPrefixP_succ (inf : Int) (F T : List Nat) (Cc : List Int) (t : Nat) (D0 P0 : List Int) :
    passPrefixP inf F T Cc (t + 1) D0 P0 = relaxPL inf F T Cc t (passPrefix inf F T Cc t D0) (passPrefixP inf F T Cc t D0 P0) := by
  unfold passPrefixP
  rw [List.range_succ, List.foldl_append]
  rfl

/-- The parent list after `r` full passes. -/
def roundsPL (inf : Int) (F T : List Nat) (Cc : List Int) (m : Nat) : Nat → List Int → List Int → List Int
  | 0, _, P => P
  | r + 1, D, P => passPrefixP inf F T Cc m (roundsL inf F T Cc m r D) (roundsPL inf F T Cc m r D P)

-- ===== the marking passes =====

/-- The marking step for one edge whose start is neither unreached nor... (the inside of `if (dist[u] != inf)`). -/
def markIn (inf : Int) (F T : List Nat) (Cc : List Int) (e : Nat) (s : List Int × List Int) : List Int × List Int :=
  if s.1.getD (F.getD e 0) 0 = -inf then (s.1.set (T.getD e 0) (-inf), s.2.set (T.getD e 0) (-1))
  else if s.1.getD (F.getD e 0) 0 + Cc.getD e 0 < s.1.getD (T.getD e 0) 0
    then (s.1.set (T.getD e 0) (-inf), s.2.set (T.getD e 0) (-1)) else s

/-- The marking step for one edge. -/
def markEdge (inf : Int) (F T : List Nat) (Cc : List Int) (e : Nat) (s : List Int × List Int) : List Int × List Int :=
  if s.1.getD (F.getD e 0) 0 ≠ inf then markIn inf F T Cc e s else s

/-- The marking edges `0 .. t-1` in order. -/
def markPrefix (inf : Int) (F T : List Nat) (Cc : List Int) (t : Nat) (s : List Int × List Int) : List Int × List Int :=
  (List.range t).foldl (fun s e => markEdge inf F T Cc e s) s

theorem markPrefix_succ (inf : Int) (F T : List Nat) (Cc : List Int) (t : Nat) (s : List Int × List Int) :
    markPrefix inf F T Cc (t + 1) s = markEdge inf F T Cc t (markPrefix inf F T Cc t s) := by
  unfold markPrefix
  rw [List.range_succ, List.foldl_append]
  rfl

/-- `r` full marking rounds. -/
def markRounds (inf : Int) (F T : List Nat) (Cc : List Int) (m : Nat) : Nat → List Int × List Int → List Int × List Int
  | 0, s => s
  | r + 1, s => markPrefix inf F T Cc m (markRounds inf F T Cc m r s)

end Proofs.BellmanFordPExec
