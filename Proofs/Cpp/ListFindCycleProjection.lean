import Proofs.Cpp.Gen.GraphList
import Proofs.Math.FindCycleSpec
import Proofs.Math.ListLowlinkMultigraph
import Proofs.Cpp.Lib.Basic

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FindCycleInv Proofs.FindCycleStep
open Proofs.LowlinkInv (AdjH upd upd_same upd_ne)
open Proofs.LowlinkMultigraph (offsets endpoints offsets_succ endpoint_get adj_rows)

namespace Proofs.Cpp.ListFindCycle

variable {Cost E : Type} [Inhabited E] [Field "from" E Int] [Field "to" E Int]

def edgesAt (g : cp.ListGraph Cost E) (v : Nat) : List E := (get g.adj (v : Int)).toList

def directedRows (g : cp.ListGraph Cost E) : List (List Nat) :=
  (List.range g.adj.size).map (fun v => (edgesAt g v).map (fun e => (Field.get (member := "to") e : Int).toNat))

structure ValidGraph (g : cp.ListGraph Cost E) : Prop where
  size_eq : g.n_ = (g.adj.size : Int)
  row : ∀ v, v < g.adj.size → ∀ e ∈ edgesAt g v,
    Field.get (member := "from") e = (v : Int) ∧ 0 ≤ (Field.get (member := "to") e : Int) ∧
      (Field.get (member := "to") e : Int) < g.n_

omit [Inhabited E] [Field "from" E Int] in
private theorem directedRows_get (g : cp.ListGraph Cost E) (v : Nat) (hv : v < g.adj.size) :
    (directedRows g)[v]'(by simpa [directedRows] using hv) =
      (edgesAt g v).map (fun e => (Field.get (member := "to") e : Int).toNat) := by
  simp [directedRows]

omit [Inhabited E] in
theorem directed_adj (g : cp.ListGraph Cost E) (valid : ValidGraph g) (v w : Nat) :
    AdjH (offsets (directedRows g)) (endpoints (directedRows g)) v w ↔
      v < g.adj.size ∧ ∃ e ∈ edgesAt g v, Field.get (member := "to") e = (w : Int) := by
  rw [adj_rows]
  constructor
  · rintro ⟨hrow, hmem⟩
    have hv : v < g.adj.size := by simpa [directedRows] using hrow
    rw [directedRows_get g v hv] at hmem
    obtain ⟨edge, hed, hto⟩ := List.mem_map.mp hmem
    have hnn := (valid.row v hv edge hed).2.1
    exact ⟨hv, edge, hed, by omega⟩
  · rintro ⟨hv, edge, hed, hto⟩
    refine ⟨by simpa [directedRows] using hv, ?_⟩
    rw [directedRows_get g v hv]
    exact List.mem_map.mpr ⟨edge, hed, by simp [hto]⟩

omit [Inhabited E] in
theorem directed_graph_view (g : cp.ListGraph Cost E) (valid : ValidGraph g) :
    FGH g.adj.size (offsets (directedRows g)) (endpoints (directedRows g)) := by
  constructor
  · intro v hv
    rw [offsets_succ _ _ (by simpa [directedRows] using hv)]
    omega
  · intro v w ha
    obtain ⟨hv, edge, hedge, hto⟩ := (directed_adj g valid v w).mp ha
    have hb := (valid.row v hv edge hedge).2.2
    rw [hto, valid.size_eq] at hb
    exact ⟨hv, by omega⟩

omit [Inhabited E] [Field "from" E Int] in
theorem directed_cursor (g : cp.ListGraph Cost E) (v : Nat) (hv : v < g.adj.size)
    (pre post : List E) (edge : E) (split : edgesAt g v = pre ++ edge :: post) :
    let rs := directedRows g
    let q := offsets rs v + pre.length
    q < offsets rs (v + 1) ∧ endpoints rs q = (Field.get (member := "to") edge : Int).toNat := by
  have hrow : v < (directedRows g).length := by simpa [directedRows] using hv
  have hlist := directedRows_get g v hv
  rw [split, List.map_append, List.map_cons] at hlist
  have hi : pre.length < (directedRows g)[v].length := by rw [hlist]; simp
  dsimp only
  constructor
  · rw [offsets_succ _ _ hrow]
    omega
  · rw [endpoint_get _ _ _ hrow hi]
    have he : (directedRows g)[v][pre.length]? = some ((Field.get (member := "to") edge : Int).toNat) := by
      rw [hlist, List.getElem?_append_right (by simp)]
      simp
    simpa only [List.getElem?_eq_getElem hi, Option.some.injEq] using he

/-- The mutable arrays project to the ghost colours and retain the full parent edge of each
active non-root vertex, including any user-defined payload. -/
structure Active (g : cp.ListGraph Cost E) (visited : Array Int) (parents : Array E) (st : FS) : Prop where
  visited_size : visited.size = g.adj.size
  parents_size : parents.size = g.adj.size
  color : ∀ v, v < g.adj.size → get visited (v : Int) = st.C v
  parent_edge : ∀ j, j + 1 < st.sp →
    let parent := get parents (st.Sk (j + 1) : Int)
    parent ∈ edgesAt g (st.Sk j) ∧ Field.get (member := "to") parent = (st.Sk (j + 1) : Int)

theorem Active.parent_endpoints {g : cp.ListGraph Cost E} {visited : Array Int} {parents : Array E}
    {st : FS} (active : Active g visited parents st) (valid : ValidGraph g)
    (inv : FInv g.adj.size (offsets (directedRows g)) (endpoints (directedRows g)) st)
    {j : Nat} (hj : j + 1 < st.sp) :
    let e := get parents (st.Sk (j + 1) : Int)
    e ∈ edgesAt g (st.Sk j) ∧ Field.get (member := "from") e = (st.Sk j : Int) ∧
      Field.get (member := "to") e = (st.Sk (j + 1) : Int) := by
  obtain ⟨he, hto⟩ := active.parent_edge j hj
  have hgray := inv.sk_gray j (by omega)
  have hvertex := inv.c_lt (st.Sk j) (by omega)
  exact ⟨he, (valid.row (st.Sk j) hvertex _ he).1, hto⟩

theorem Active.gray_ancestor {g : cp.ListGraph Cost E} {visited : Array Int} {parents : Array E}
    {st : FS} (active : Active g visited parents st) (valid : ValidGraph g)
    (inv : FInv g.adj.size (offsets (directedRows g)) (endpoints (directedRows g)) st)
    {v : Nat} (hv : v < g.adj.size) {edge : E} (he : edge ∈ edgesAt g v)
    (gray : get visited (Field.get (member := "to") edge) = 1) :
    ∃ first, first < st.sp ∧ (st.Sk first : Int) = Field.get (member := "to") edge := by
  obtain ⟨_, hnn, hlt⟩ := valid.row v hv edge he
  let w := (Field.get (member := "to") edge : Int).toNat
  have hw : (w : Int) = Field.get (member := "to") edge := by omega
  have hwin : w < g.adj.size := by rw [valid.size_eq, ← hw] at hlt; omega
  rw [← hw, active.color w hwin] at gray
  obtain ⟨j, hj, hjw⟩ := inv.gray_sk w gray
  exact ⟨j, hj, by rw [hjw, hw]⟩

omit [Field "from" E Int] [Field "to" E Int] in
private theorem get_set_cast {α : Type} [Inhabited α] (a : Array α) (i v : Nat) (x : α)
    (hi : i < a.size) : get (set a (i : Int) x) (v : Int) = if v = i then x else get a (v : Int) := by
  simpa only [get_eq, Int.toNat_natCast] using
    (getElemBang_set a (i : Int) x v (by simpa using hi))

omit [Field "from" E Int] in
theorem Active.enter_root {g : cp.ListGraph Cost E} {visited : Array Int} {parents : Array E} {st : FS}
    (active : Active g visited parents st) (hd : Nat → Nat) {r : Nat} (hr : r < g.adj.size) :
    Active g (set visited (r : Int) 1) parents (fRoot hd st r) := by
  refine ⟨by simpa using active.visited_size, active.parents_size, ?_, ?_⟩
  · intro v hv
    rw [get_set_cast _ _ _ _ (by simpa [active.visited_size] using hr), active.color v hv]
    rfl
  · intro j hj
    change j + 1 < 1 at hj
    omega

omit [Field "from" E Int] in
theorem Active.skip {g : cp.ListGraph Cost E} {visited : Array Int} {parents : Array E} {st : FS}
    (active : Active g visited parents st) (v : Nat) : Active g visited parents (fSkip st v) :=
  ⟨active.visited_size, active.parents_size, active.color, active.parent_edge⟩

omit [Field "from" E Int] in
theorem Active.pop {g : cp.ListGraph Cost E} {visited : Array Int} {parents : Array E} {st : FS}
    (active : Active g visited parents st) {r : Nat} (hr : r < g.adj.size) :
    Active g (set visited (r : Int) 2) parents (fPop st r) := by
  refine ⟨by simpa using active.visited_size, active.parents_size, ?_, ?_⟩
  · intro v hv
    rw [get_set_cast _ _ _ _ (by simpa [active.visited_size] using hr), active.color v hv]
    rfl
  · intro j hj
    change j + 1 < st.sp - 1 at hj
    exact active.parent_edge j (by omega)

omit [Field "from" E Int] in
theorem Active.enter_child {g : cp.ListGraph Cost E} {visited : Array Int} {parents : Array E} {st : FS}
    (active : Active g visited parents st)
    (inv : FInv g.adj.size (offsets (directedRows g)) (endpoints (directedRows g)) st)
    {v w : Nat} {edge : E} (_hsp : 0 < st.sp) (htop : st.Sk (st.sp - 1) = v)
    (hw : w < g.adj.size) (white : st.C w = 0)
    (hedge : edge ∈ edgesAt g v) (hto : Field.get (member := "to") edge = (w : Int)) :
    Active g (set visited (w : Int) 1) (set parents (w : Int) edge)
      (fPush (offsets (directedRows g)) st v w) := by
  have hwv : w < visited.size := by simpa only [active.visited_size] using hw
  have hwp : w < parents.size := by simpa only [active.parents_size] using hw
  refine ⟨by simpa using active.visited_size, by simpa using active.parents_size, ?_, ?_⟩
  · intro r hr
    rw [get_set_cast _ _ _ _ hwv, active.color r hr]
    rfl
  · intro j hj
    change j + 1 < st.sp + 1 at hj
    dsimp only [fPush]
    rw [upd_ne _ _ _ j (by omega)]
    by_cases hlast : j + 1 = st.sp
    · rw [hlast, upd_same, get_set_cast _ _ _ _ hwp, ite_eq_left rfl]
      have hindex : j = st.sp - 1 := by omega
      rw [hindex, htop]
      exact ⟨hedge, hto⟩
    · rw [upd_ne _ _ _ (j + 1) hlast, get_set_cast _ _ _ _ hwp]
      have hgray := inv.sk_gray (j + 1) (by omega)
      have hneq : st.Sk (j + 1) ≠ w := by intro he; rw [he, white] at hgray; contradiction
      rw [ite_eq_right hneq]
      exact active.parent_edge j (by omega)

end Proofs.Cpp.ListFindCycle

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FindCycleInv Proofs.FindCycleStep
open Proofs.LowlinkInv (upd upd_same upd_ne)
open Proofs.LowlinkMultigraph (offsets endpoints offsets_succ)

namespace Proofs.Cpp.ListFindCycle

/-- Lower frames remain at the same vertices and retain the position at which they suspended. -/
def Parked (level : Nat) (before after : FS) : Prop :=
  ∀ i, i < level → after.Sk i = before.Sk i ∧ after.It (before.Sk i) = before.It (before.Sk i)

theorem Parked.refl (level : Nat) (st : FS) : Parked level st st := fun _ _ => ⟨rfl, rfl⟩

theorem Parked.trans {k : Nat} {a b c : FS} (h₁ : Parked k a b) (h₂ : Parked k b c) : Parked k a c := by
  intro i hi
  obtain ⟨hs, hc⟩ := h₁ i hi
  have h := h₂ i hi
  rw [hs] at h
  exact ⟨h.1, h.2.trans hc⟩

theorem Parked.lower {k l : Nat} {a b : FS} (h : Parked k a b) (hle : l ≤ k) : Parked l a b :=
  fun i hi => h i (Nat.lt_of_lt_of_le hi hle)

def VisitedPersists (before after : FS) : Prop := ∀ v, before.C v ≠ 0 → after.C v ≠ 0

theorem VisitedPersists.trans {a b c : FS} (h₁ : VisitedPersists a b) (h₂ : VisitedPersists b c) :
    VisitedPersists a c := fun v hv => h₂ v (h₁ v hv)

theorem persists_with_update {st st' : FS} {v : Nat} {color : Int}
    (hcolor : color ≠ 0) (updated : st'.C = upd st.C v color) : VisitedPersists st st' := by
  intro w hw
  rw [updated]
  by_cases hwv : w = v
  · subst w
    rw [upd_same]
    exact hcolor
  · rwa [upd_ne _ _ _ _ hwv]

section
variable {n : Nat} {hd tg : Nat → Nat} {st : FS}

private theorem ancestor_ne {v i : Nat} (inv : FInv n hd tg st) (htop : st.Sk (st.sp - 1) = v)
    (hi : i < st.sp - 1) : st.Sk i ≠ v := by
  intro h
  have same := inv.sk_inj i (st.sp - 1) (by omega) (by omega) (h.trans htop.symm)
  omega

theorem skip_parked {v : Nat} (inv : FInv n hd tg st) (htop : st.Sk (st.sp - 1) = v) :
    Parked (st.sp - 1) st (fSkip st v) := by
  intro i hi
  exact ⟨rfl, upd_ne _ _ _ _ (ancestor_ne inv htop hi)⟩

theorem push_parked {v w : Nat} (inv : FInv n hd tg st) (htop : st.Sk (st.sp - 1) = v)
    (white : st.C w = 0) : Parked (st.sp - 1) st (fPush hd st v w) := by
  intro i hi
  have hgray := inv.sk_gray i (by omega)
  have hneq : st.Sk i ≠ w := by intro h; rw [h, white] at hgray; contradiction
  refine ⟨upd_ne _ _ _ _ (by omega), ?_⟩
  change upd (upd st.It v (st.It v + 1)) w (hd w : Int) (st.Sk i) = st.It (st.Sk i)
  rw [upd_ne _ _ _ _ hneq, upd_ne _ _ _ _ (ancestor_ne inv htop hi)]

theorem pop_parked {v : Nat} : Parked (st.sp - 1) st (fPop st v) := Parked.refl _ _

end

variable {Cost E : Type} [Inhabited E] [Field "to" E Int]

/-- A row is positioned by the number of original edge values already scanned, with the same
cursor as its CSR projection. -/
def AtCursor (g : cp.ListGraph Cost E) (st : FS) (v : Nat) (rest : List E) : Prop :=
  ∃ pre, edgesAt g v = pre ++ rest ∧ st.It v = (offsets (directedRows g) v : Int) + (pre.length : Int)

omit [Inhabited E] in
theorem row_width (g : cp.ListGraph Cost E) (v : Nat) (hv : v < g.adj.size) :
    offsets (directedRows g) (v + 1) = offsets (directedRows g) v + (edgesAt g v).length := by
  have hrow : v < (directedRows g).length := by simpa [directedRows] using hv
  rw [offsets_succ _ _ hrow]
  simp [directedRows]

omit [Inhabited E] in
theorem AtCursor.done {g : cp.ListGraph Cost E} {st : FS} {v : Nat} (h : AtCursor g st v [])
    (hv : v < g.adj.size) : st.It v = (offsets (directedRows g) (v + 1) : Int) := by
  obtain ⟨pre, hrow, hc⟩ := h
  rw [row_width g v hv, hrow]
  simpa using hc

omit [Inhabited E] in
theorem AtCursor.head {g : cp.ListGraph Cost E} {st : FS} {v : Nat} {edge : E} {rest : List E}
    (h : AtCursor g st v (edge :: rest)) (hv : v < g.adj.size) :
    ∃ q : Nat, (q : Int) = st.It v ∧ q < offsets (directedRows g) (v + 1) ∧
      endpoints (directedRows g) q = (Field.get (member := "to") edge : Int).toNat ∧ edge ∈ edgesAt g v := by
  obtain ⟨pre, hrow, hc⟩ := h
  obtain ⟨hl, hto⟩ := directed_cursor g v hv pre rest edge hrow
  exact ⟨_, by simp [hc], hl, hto, by simp [hrow]⟩

omit [Inhabited E] in
theorem AtCursor.advance {g : cp.ListGraph Cost E} {before after : FS} {v : Nat} {edge : E} {rest : List E}
    (h : AtCursor g before v (edge :: rest)) (next : after.It v = before.It v + 1) :
    AtCursor g after v rest := by
  obtain ⟨pre, hrow, hc⟩ := h
  exact ⟨pre ++ [edge], by simpa using hrow, by simp [next, hc, Int.add_assoc]⟩

end Proofs.Cpp.ListFindCycle
