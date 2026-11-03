import Proofs.CppNestedScope
import Proofs.Generated.DoublingNested

namespace Proofs.DoublingNested
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppMixedInvoke
open Proofs.CppState (Cell)

abbrev i32 : Ty := ⟨32,true,false⟩
abbrev u64 : Ty := ⟨64,false,false⟩
abbrev bl : Ty := ⟨1,false,true⟩
abbrev atom : Element := .integer i32

-- Reference semantics: row k+1 jumps through row k, `next[j] = row[row[j]]`.
def jump (row : List Int) (x : Int) : Int := row.getD x.toNat 0
def nextRow (row : List Int) : List Int := row.map (jump row)
def tableRow (items : List Int) : Nat → List Int
  | 0 => items
  | k+1 => nextRow (tableRow items k)

theorem nextRow_length (row : List Int) : (nextRow row).length = row.length := by simp [nextRow]

theorem tableRow_length (items : List Int) (k : Nat) : (tableRow items k).length = items.length := by
  induction k with
  | zero => rfl
  | succ k ih => simp [tableRow,nextRow_length,ih]

theorem tableRow_range (items : List Int) (valid : ∀ x ∈ items, 0 ≤ x ∧ x < items.length) (k : Nat) :
    ∀ x ∈ tableRow items k, 0 ≤ x ∧ x < items.length := by
  induction k with
  | zero => exact valid
  | succ k ih =>
    intro x member
    simp only [tableRow,nextRow,List.mem_map] at member
    obtain ⟨y,yMember,rfl⟩ := member
    obtain ⟨nonneg,small⟩ := ih y yMember
    have inside : y.toNat < (tableRow items k).length := by rw [tableRow_length]; omega
    have : (tableRow items k)[y.toNat]? = some ((tableRow items k)[y.toNat]) := by simp [inside]
    have found : jump (tableRow items k) y = (tableRow items k)[y.toNat] := by
      simp [jump,List.getD_eq_getElem?_getD,inside]
    rw [found]
    exact ih _ (List.getElem_mem inside)

theorem tableRow_get (items : List Int) (k j : Nat) (inside : j < items.length) :
    (tableRow items (k+1))[j]? = some (jump (tableRow items k) (tableRow items k)[j]!) := by
  have inside' : j < (tableRow items k).length := by rw [tableRow_length]; exact inside
  simp [tableRow,nextRow,List.getElem?_map,inside']

-- State shapes of the main phase. Slots are declaration ordered:
-- 0:v 1:kmax 2:n 3:hidden bit width 4:w 5:ret [6:i [7:j]].
def mainSlots : List Location :=
  [.vector 0,.scalar 0,.scalar 1,.scalar 2,.scalar 3,.vector 1,.scalar 4,.scalar 5]

def vbind (V vsc : Nat) : Binding := ⟨V,atom,false,.root vsc⟩
def rbind (R sc : Nat) : Binding := ⟨R,.vector atom,true,.root sc⟩

-- After declaring i (slot 6): locals K n W w i.
structure Sh6 (S : NState) (P : List Cell) (B : Nat) (K : Int) (n w i : Nat) (V vsc R sc scope : Nat)
    (rw : List Bool) : Prop where
  slots : S.slots = mainSlots.take 7
  memory : S.scalars.memory = P ++ [⟨u64,K⟩,⟨i32,n⟩,⟨i32,w⟩,⟨i32,w⟩,⟨i32,i⟩]
  bindings : S.scalars.bindings = [⟨P.length,true⟩,⟨P.length+1,false⟩,⟨P.length+2,false⟩,
    ⟨P.length+3,false⟩,⟨P.length+4,true⟩]
  base : S.scalars.baseMemory = B
  scope : S.scope = scope
  frameBindings : S.frame.bindings = [vbind V vsc,rbind R sc]
  writable : S.frame.rootWritable = rw

-- After declaring j (slot 7): locals K n W w i j.
structure Sh8 (S : NState) (P : List Cell) (B : Nat) (K : Int) (n w i j : Nat) (V vsc R sc scope : Nat)
    (rw : List Bool) : Prop where
  slots : S.slots = mainSlots
  memory : S.scalars.memory = P ++ [⟨u64,K⟩,⟨i32,n⟩,⟨i32,w⟩,⟨i32,w⟩,⟨i32,i⟩,⟨i32,j⟩]
  bindings : S.scalars.bindings = [⟨P.length,true⟩,⟨P.length+1,false⟩,⟨P.length+2,false⟩,
    ⟨P.length+3,false⟩,⟨P.length+4,true⟩,⟨P.length+5,true⟩]
  base : S.scalars.baseMemory = B
  scope : S.scope = scope
  frameBindings : S.frame.bindings = [vbind V vsc,rbind R sc]
  writable : S.frame.rootWritable = rw

-- Row buffers of the constructed table: rows below `done` are complete, row
-- `done` holds `cur` with capacity `curCap`, later rows are untouched.
structure RowsOK (T : Proofs.CppNestedVectorStore.State) (R n w : Nat) (items : List Int) (V : Nat)
    (vBuffer : Buffer Value) (done : Nat) (cur : List Int) (curCap : Nat) : Prop where
  vFound : T.storage.lookup V = some vBuffer
  complete : ∀ k, k < done → ∃ b, T.storage.lookup (R+1+k) = some b ∧
    b.items = (tableRow items k).map Value.integer ∧ b.capacity = n ∧ b.limit = CppVectorBindings.sizeLimit i32
  current : done < w → ∃ b, T.storage.lookup (R+1+done) = some b ∧
    b.items = cur.map Value.integer ∧ b.capacity = curCap ∧ b.limit = CppVectorBindings.sizeLimit i32
  untouched : ∀ k, done < k → k < w → ∃ b, T.storage.lookup (R+1+k) = some b ∧
    b.items = [] ∧ b.capacity = 0 ∧ b.limit = CppVectorBindings.sizeLimit i32

-- Expressions of the generated body.
abbrev ci : NExpr := .cast u64 (.variable i32 6)
abbrev cj : NExpr := .cast u64 (.variable i32 7)
abbrev cim1 : NExpr := .cast u64 (.binary i32 .sub (.variable i32 6) (.literal i32 1))
abbrev innerRead : NExpr := .read i32 (.row (.local 5) atom cim1) cj
abbrev valueExpr : NExpr := .read i32 (.row (.local 5) atom cim1) (.cast u64 innerRead)

theorem env_ext {S u : NState} (ext : Ext S u) : envOf u = envOf S := by
  obtain ⟨_,_,_,slots,_,memory,bindings,_⟩ := ext
  funext slot ty
  simp [envOf,NState.scalarCell,NState.scalarSlot,slots,memory,bindings]

theorem i32_valid_nat (n : Nat) (small : n < 2147483648) : i32.valid (n : Int) = true := by
  simp [Ty.valid]
  omega

theorem u64_valid_nat (n : Nat) (small : n < 18446744073709551616) : u64.valid (n : Int) = true := by
  simp [Ty.valid]
  omega

theorem envOf_at (s : NState) (slot idx : Nat) (binding : CppState.Binding) (ty : Ty) (value : Int)
    (hs : s.slots[slot]? = some (.scalar idx)) (hb : s.scalars.bindings[idx]? = some binding)
    (hm : s.scalars.memory[binding.address]? = some ⟨ty,value⟩) (valid : ty.valid value = true) :
    envOf s slot ty = some value := by
  simp [envOf,NState.scalarCell,NState.scalarSlot,hs,hb,hm,valid]

theorem Sh8.value (S : NState) {P B K n w i j V vsc R sc scope rw}
    (shape : Sh8 S P B K n w i j V vsc R sc scope rw) (hi : i < 2147483648) (hj : j < 2147483648)
    (hn : n < 2147483648) :
    envOf S 6 i32 = some (i : Int) ∧ envOf S 7 i32 = some (j : Int) ∧ envOf S 2 i32 = some (n : Int) := by
  obtain ⟨slots,memory,bindings,base,_,_,_⟩ := shape
  refine ⟨envOf_at S 6 4 ⟨P.length+4,true⟩ i32 i (by simp [slots,mainSlots]) (by simp [bindings])
      (by simp [memory]) (i32_valid_nat i hi),
    envOf_at S 7 5 ⟨P.length+5,true⟩ i32 j (by simp [slots,mainSlots]) (by simp [bindings])
      (by simp [memory]) (i32_valid_nat j hj),
    envOf_at S 2 1 ⟨P.length+1,false⟩ i32 n (by simp [slots,mainSlots]) (by simp [bindings])
      (by simp [memory]) (i32_valid_nat n hn)⟩

-- Frame facts needed to evaluate `ret[k]` in a state.
structure Ctx (u : NState) (R sc w : Nat) : Prop where
  slot : u.vectorSlot 5 = some 1
  binding : u.frame.bindings[1]? = some ⟨R,.vector (.integer i32),true,.root sc⟩
  graph : RootGraph u.frame.state R i32 w sc
  lengths : u.frame.rootWritable.length = u.frame.state.forest.objects.length
  flag : u.frame.rootWritable[R]? = some true

theorem Ctx.ext {S u : NState} {R sc w : Nat} (ctx : Ctx S R sc w) (ext : Ext S u)
    (prefixTwo : 1 < S.frame.bindings.length) : Ctx u R sc w := by
  obtain ⟨state,rw,⟨extra,bindings⟩,slots,_,_,_,_⟩ := ext
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa [NState.vectorSlot,slots] using ctx.slot
  · rw [bindings,List.getElem?_append_left prefixTwo]; exact ctx.binding
  · rw [state]; exact ctx.graph
  · rw [rw,state]; exact ctx.lengths
  · rw [rw]; exact ctx.flag

theorem cj_scalar : cj.scalarOnly = true := by simp [NExpr.scalarOnly]
theorem cim1_scalar : cim1.scalarOnly = true := by simp [NExpr.scalarOnly]

theorem cj_value (S : NState) {P B K n w i j V vsc R sc scope rw}
    (shape : Sh8 S P B K n w i j V vsc R sc scope rw) (hi : i < 2147483648) (hj : j < 2147483648)
    (hn : n < 2147483648) : cj.denote (envOf S) = some (j : Int) := by
  obtain ⟨_,e7,_⟩ := Sh8.value S shape hi hj hn
  have valid : u64.valid (j : Int) = true := u64_valid_nat j (by omega)
  simp [NExpr.denote,e7,Ty.convert_of_valid _ _ valid]

theorem cim1_value (S : NState) {P B K n w i j V vsc R sc scope rw}
    (shape : Sh8 S P B K n w i j V vsc R sc scope rw) (hi : i < 2147483648) (hj : j < 2147483648)
    (hn : n < 2147483648) (positive : 1 ≤ i) : cim1.denote (envOf S) = some ((i-1 : Nat) : Int) := by
  obtain ⟨e6,_,_⟩ := Sh8.value S shape hi hj hn
  have sub : i32.valid ((i : Int) - 1) = true := by simp [Ty.valid]; omega
  have valid : u64.valid ((i-1 : Nat) : Int) = true := u64_valid_nat (i-1) (by omega)
  have lit : i32.valid (1 : Int) = true := by simp [Ty.valid]
  have cast : ((i : Int) - 1) = ((i-1 : Nat) : Int) := by omega
  simp [NExpr.denote,e6,lit,binaryValue,Ty.convert_of_valid _ _ sub]
  rw [cast] at *
  exact Ty.convert_of_valid _ _ valid

theorem inner_ev (S : NState) {P B K n w i j V vsc R sc scope rw} (shape : Sh8 S P B K n w i j V vsc R sc scope rw)
    (ctx : Ctx S R sc w) (prefixTwo : 1 < S.frame.bindings.length)
    (hi : i < 2147483648) (hj : j < 2147483648) (hn : n < 2147483648) (positive : 1 ≤ i) (iw : i < w)
    (prev : Buffer Value) (found : S.frame.state.storage.lookup (R+1+(i-1)) = some prev) (x1 : Int)
    (item : prev.items[j]? = some (Value.integer x1)) :
    ∀ u, Ext S u → ∃ t, Ev u innerRead t x1 [rowBinding R i32 (i-1)] (cim1.nodes+2+cj.nodes+1)
      (max (cim1.nodes+cj.nodes+4) (max (cim1.nodes+2) (max cj.nodes 2))) := by
  intro u ext
  have ctx' := ctx.ext ext prefixTwo
  have env := env_ext ext
  have result := Ev.readRow u 5 1 cim1 cj (i-1) j R w sc i32 x1 prev [] cj.nodes cj.nodes cim1_scalar
    (by rw [env]; exact cim1_value S shape hi hj hn positive) ctx'.slot ctx'.binding ctx'.graph ctx'.lengths
    ctx'.flag (by omega) (by rw [ext.1]; exact found) item
    (by
      intro u' ext'
      have e := env_ext (ext.trans ext')
      exact Ev.scalar cj_scalar (by rw [e]; exact cj_value S shape hi hj hn))
  simpa using result

theorem cast_ev (S : NState) {P B K n w i j V vsc R sc scope rw} (shape : Sh8 S P B K n w i j V vsc R sc scope rw)
    (ctx : Ctx S R sc w) (prefixTwo : 1 < S.frame.bindings.length)
    (hi : i < 2147483648) (hj : j < 2147483648) (hn : n < 2147483648) (positive : 1 ≤ i) (iw : i < w)
    (prev : Buffer Value) (found : S.frame.state.storage.lookup (R+1+(i-1)) = some prev) (m : Nat)
    (item : prev.items[j]? = some (Value.integer (m : Int))) (small : m < 18446744073709551616) :
    ∀ u, Ext S u → ∃ t, Ev u (.cast u64 innerRead) t (m : Int) [rowBinding R i32 (i-1)]
      ((cim1.nodes+2+cj.nodes+1)+1)
      (max (innerRead.nodes+1) (max (max (cim1.nodes+cj.nodes+4) (max (cim1.nodes+2) (max cj.nodes 2))) 1)) := by
  intro u ext
  have inner := inner_ev S shape ctx prefixTwo hi hj hn positive iw prev found _ item (u.charge 0 (innerRead.nodes+1))
    (ext.trans (Ext.charge u 0 (innerRead.nodes+1)))
  obtain ⟨t,ev⟩ := inner
  exact ⟨_,Ev.cast ev (Ty.convert_of_valid _ _ (u64_valid_nat m small))⟩

theorem value_ev (S : NState) {P B K n w i j V vsc R sc scope rw} (shape : Sh8 S P B K n w i j V vsc R sc scope rw)
    (ctx : Ctx S R sc w) (prefixTwo : 1 < S.frame.bindings.length)
    (hi : i < 2147483648) (hj : j < 2147483648) (hn : n < 2147483648) (positive : 1 ≤ i) (iw : i < w)
    (prev : Buffer Value) (found : S.frame.state.storage.lookup (R+1+(i-1)) = some prev) (m : Nat)
    (item : prev.items[j]? = some (Value.integer (m : Int))) (small : m < 18446744073709551616) (x2 : Int)
    (item2 : prev.items[m]? = some (Value.integer x2)) :
    ∀ u, Ext S u → ∃ t, Ev u valueExpr t x2 [rowBinding R i32 (i-1),rowBinding R i32 (i-1)] 40 40 := by
  intro u ext
  have ctx' := ctx.ext ext prefixTwo
  have env := env_ext ext
  have result := Ev.readRow u 5 1 cim1 (.cast u64 innerRead) (i-1) m R w sc i32 x2 prev _ _ _ cim1_scalar
    (by rw [env]; exact cim1_value S shape hi hj hn positive) ctx'.slot ctx'.binding ctx'.graph ctx'.lengths
    ctx'.flag (by omega) (by rw [ext.1]; exact found) item2
    (by
      intro u' ext'
      exact cast_ev S shape ctx prefixTwo hi hj hn positive iw prev found m item small u' (ext.trans ext'))
  obtain ⟨t,ev⟩ := result
  exact ⟨t,ev.mono (by simp [NExpr.nodes,Container.nodes]) (by simp [NExpr.nodes,Container.nodes])⟩

abbrev ciExpr : NExpr := ci

theorem ci_scalar : ci.scalarOnly = true := by simp [NExpr.scalarOnly]

theorem ci_value (S : NState) {P B K n w i j V vsc R sc scope rw}
    (shape : Sh8 S P B K n w i j V vsc R sc scope rw) (hi : i < 2147483648) (hj : j < 2147483648)
    (hn : n < 2147483648) : ci.denote (envOf S) = some (i : Int) := by
  obtain ⟨e6,_,_⟩ := Sh8.value S shape hi hj hn
  have valid : u64.valid (i : Int) = true := u64_valid_nat i (by omega)
  simp [NExpr.denote,e6,Ty.convert_of_valid _ _ valid]

-- Replacing the current row's buffer keeps all other facts about the table.
theorem rowsOK_set {T T' : Proofs.CppNestedVectorStore.State} {R n w : Nat} {items : List Int} {V : Nat}
    {vBuffer : Buffer Value} {done : Nat} {cur : List Int} {curCap : Nat} (cur' : List Int) (curCap' : Nat)
    (rows : RowsOK T R n w items V vBuffer done cur curCap) (before : V < R) (hd : done < w)
    (b' : Buffer Value) (self : T'.storage.lookup (R+1+done) = some b')
    (other : ∀ o, o ≠ R+1+done → T'.storage.lookup o = T.storage.lookup o)
    (itemsEq : b'.items = cur'.map Value.integer) (capEq : b'.capacity = curCap')
    (limitEq : b'.limit = CppVectorBindings.sizeLimit i32) :
    RowsOK T' R n w items V vBuffer done cur' curCap' := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [other V (by omega)]; exact rows.vFound
  · intro k lt
    obtain ⟨b,found,i1,c1,l1⟩ := rows.complete k lt
    exact ⟨b,by rw [other _ (by omega)]; exact found,i1,c1,l1⟩
  · intro _
    exact ⟨b',self,itemsEq,capEq,limitEq⟩
  · intro k gt lt
    obtain ⟨b,found,i1,c1,l1⟩ := rows.untouched k gt lt
    exact ⟨b,by rw [other _ (by omega)]; exact found,i1,c1,l1⟩

abbrev appendStmt : NStmt := .append (.row (.local 5) atom ci) i32 valueExpr

theorem append_step (S : NState) {P B K n w i j V vsc R sc scope rw} (items : List Int) (vbuf : Buffer Value)
    (shape : Sh8 S P B K n w i j V vsc R sc scope rw) (ctx : Ctx S R sc w)
    (rows : RowsOK S.frame.state R n w items V vbuf i ((tableRow items i).take j) n)
    (before : V < R) (nEq : n = items.length) (itemsValid : ∀ x ∈ items, 0 ≤ x ∧ x < items.length)
    (hn : n < 2147483648) (hi : i < 2147483648) (hj : j < 2147483648) (positive : 1 ≤ i) (iw : i < w)
    (jn : j < n) :
    ∃ t, appendStmt.run S = some ⟨t,none,false⟩ ∧
      Sh8 t P B K n w i j V vsc R sc scope rw ∧ Ctx t R sc w ∧
      RowsOK t.frame.state R n w items V vbuf i ((tableRow items i).take (j+1)) n ∧
      t.frame.state.liveSpace = S.frame.state.liveSpace ∧
      t.frame.state.forest = S.frame.state.forest ∧
      t.frame.state.storage.baseSpace = S.frame.state.storage.baseSpace ∧
      t.frame.state.storage.work = S.frame.state.storage.work+2 ∧
      t.frame.state.storage.peak ≤ max S.frame.state.storage.peak
        (S.frame.state.liveSpace+1-S.frame.state.storage.baseSpace) ∧
      S.frame.state.storage.peak ≤ t.frame.state.storage.peak ∧
      S.scalars.work ≤ t.scalars.work ∧ t.scalars.work ≤ S.scalars.work+45 ∧
      S.scalars.peak ≤ t.scalars.peak ∧ t.scalars.peak ≤ max S.scalars.peak (liveS S+40) ∧
      S.peak ≤ t.peak ∧ t.peak ≤ max S.peak (t.scalars.peak+t.frame.state.storage.peak) := by
  have prefixTwo : 1 < S.frame.bindings.length := by simp [shape.frameBindings]
  -- the previous row, read twice
  obtain ⟨prev,foundPrev,prevItems,prevCap,prevLimit⟩ := rows.complete (i-1) (by omega)
  have rowLen : (tableRow items (i-1)).length = n := by rw [tableRow_length,nEq]
  have rowValid := tableRow_range items itemsValid (i-1)
  have jr : j < (tableRow items (i-1)).length := by omega
  obtain ⟨x1,hx1⟩ : ∃ x1 : Int, x1 = (tableRow items (i-1))[j] := ⟨_,rfl⟩
  obtain ⟨x1nonneg,x1small⟩ := rowValid x1 (by rw [hx1]; exact List.getElem_mem jr)
  have m1 : x1 = ((x1.toNat : Nat) : Int) := by omega
  have item1 : prev.items[j]? = some (Value.integer ((x1.toNat : Nat) : Int)) := by
    rw [prevItems,← m1]; simp [List.getElem?_map,jr,hx1]
  have mr : x1.toNat < (tableRow items (i-1)).length := by omega
  obtain ⟨x2,hx2⟩ : ∃ x2 : Int, x2 = (tableRow items (i-1))[x1.toNat] := ⟨_,rfl⟩
  obtain ⟨x2nonneg,x2small⟩ := rowValid x2 (by rw [hx2]; exact List.getElem_mem mr)
  have item2 : prev.items[x1.toNat]? = some (Value.integer x2) := by
    rw [prevItems]; simp [List.getElem?_map,mr,hx2]
  have valueEv := value_ev S shape ctx prefixTwo hi hj hn positive iw prev foundPrev x1.toNat item1
    (by omega) x2 item2
  -- the current row
  obtain ⟨cur,foundCur,curItems,curCap,curLimit⟩ := rows.current iw
  have takeLen : ((tableRow items i).take j).length = j := by
    simp [List.length_take,tableRow_length,nEq]; omega
  have room : cur.items.length < cur.capacity := by
    rw [curItems,curCap]; simp [takeLen]; omega
  have accepted : i32.valid x2 = true := by
    simp [Ty.valid]; omega
  obtain ⟨t,run,tframe,sl,sc',me,bi,ba,gl,gu,gpl,gpu,ql,qu⟩ := append_row_stmt S 5 1 ci valueExpr i R w sc i32 x2
    cur [rowBinding R i32 (i-1),rowBinding R i32 (i-1)] 40 40 ci_scalar (ci_value S shape hi hj hn)
    (by simp [NState.vectorSlot,shape.slots,mainSlots]) (by simpa using ctx.binding) ctx.graph ctx.lengths ctx.flag
    iw foundCur room accepted valueEv
  -- facts about the replaced buffer
  obtain ⟨objectBuffer,object,foundObject⟩ := row_object S.frame R i32 w sc i ctx.graph iw
  have sameCur : objectBuffer = cur := by
    rw [foundCur] at foundObject
    exact (Option.some.inj foundObject).symm
  subst sameCur
  obtain ⟨_,curOwner,curValid,_,_⟩ := buffer_facts S.frame (R+1+i) i32 objectBuffer _ object
  have newValid := CppVector.append_preserves_valid objectBuffer (accepts (.integer i32)) (.integer x2) curValid
    (by simpa [accepts] using accepted) room
  have wf := row_update_valid S.frame R i32 w sc i ctx.graph iw objectBuffer
    {objectBuffer with items := objectBuffer.items ++ [Value.integer x2]}
    ⟨{objectBuffer with items := objectBuffer.items ++ [Value.integer x2]},(),2,objectBuffer.capacity+2⟩
    foundCur rfl (by simpa using curOwner) newValid
  have bound := CppVectorStore.lookup_bound S.frame.state.storage (R+1+i) objectBuffer foundCur
  have updatedSelf := CppNestedOps.updated_lookup_self S.frame (R+1+i) objectBuffer
    ⟨{objectBuffer with items := objectBuffer.items ++ [Value.integer x2]},(),2,objectBuffer.capacity+2⟩ bound
  have updatedOther : ∀ o, o ≠ R+1+i → (S.frame.updated (R+1+i) objectBuffer
      ⟨{objectBuffer with items := objectBuffer.items ++ [Value.integer x2]},(),2,objectBuffer.capacity+2⟩).state.storage.lookup o =
        S.frame.state.storage.lookup o := fun o different =>
    CppNestedOps.updated_lookup_other S.frame (R+1+i) o objectBuffer _ (by omega)
  have rootGraph := rootGraph_updated S.frame R i32 w sc ctx.graph (R+1+i) objectBuffer
    ⟨{objectBuffer with items := objectBuffer.items ++ [Value.integer x2]},(),2,objectBuffer.capacity+2⟩
    (by omega) wf
  have tstate : t.frame.state = (S.frame.updated (R+1+i) objectBuffer
    ⟨{objectBuffer with items := objectBuffer.items ++ [Value.integer x2]},(),2,objectBuffer.capacity+2⟩).state := by
    rw [tframe]
  have tbindings : t.frame.bindings = S.frame.bindings := by simp [tframe,Frame.updated]
  have twritable : t.frame.rootWritable = S.frame.rootWritable := by simp [tframe,Frame.updated]
  have rowTable : (tableRow items i)[j]? = some x2 := by
    have := tableRow_get items (i-1) j (by omega)
    rw [show i-1+1 = i by omega] at this
    rw [this]
    have bang : (tableRow items (i-1))[j]! = x1 := by simp [hx1,getElem!_pos,jr]
    simp [jump,bang,hx2,List.getD_eq_getElem?_getD,mr]
  have newItems : (objectBuffer.items ++ [Value.integer x2]) =
      ((tableRow items i).take (j+1)).map Value.integer := by
    rw [curItems,List.take_succ,rowTable]
    simp
  have rows' : RowsOK t.frame.state R n w items V vbuf i ((tableRow items i).take (j+1)) n :=
    rowsOK_set _ _ rows before iw {objectBuffer with items := objectBuffer.items ++ [Value.integer x2]}
      (by rw [tstate]; exact updatedSelf) (by intro o ho; rw [tstate]; exact updatedOther o ho)
      newItems (by simpa using curCap) (by simpa using curLimit)
  have rowTagS := row_tag S.frame R i32 w sc i ctx.graph iw
  have lengthsEq : t.frame.state.storage.objects.length = S.frame.state.storage.objects.length := by
    rw [tstate]; simp [Frame.updated]
  have forestEq : t.frame.state.forest = S.frame.state.forest := by rw [tstate]; rfl
  have live := liveSpace_update S.frame.state t.frame.state (R+1+i) bound lengthsEq forestEq
    (by intro o ho; rw [tstate]; exact updatedOther o ho)
  have nodeS := nodeSpace_row S.frame.state i32 R i objectBuffer rowTagS foundCur
  have nodeT := nodeSpace_row t.frame.state i32 R i
    {objectBuffer with items := objectBuffer.items ++ [Value.integer x2]}
    (by rw [forestEq]; exact rowTagS) (by rw [tstate]; exact updatedSelf)
  simp only [] at nodeT
  have storageT : t.frame.state.storage.work = S.frame.state.storage.work+2 ∧
      t.frame.state.storage.peak = max S.frame.state.storage.peak
        (S.frame.state.liveSpace+(objectBuffer.capacity+2-(objectBuffer.capacity+1))-S.frame.state.storage.baseSpace) ∧
      t.frame.state.storage.baseSpace = S.frame.state.storage.baseSpace := by
    rw [tstate]; simp [Frame.updated]
  simp [NExpr.nodes,Container.nodes] at gu gpu
  refine ⟨t,run,⟨?_,?_,?_,?_,?_,?_,?_⟩,⟨?_,?_,?_,?_,?_⟩,rows',?_,forestEq,storageT.2.2,storageT.1,?_,?_,gl,?_,gpl,?_,ql,qu⟩
  · rw [sl]; exact shape.slots
  · rw [me]; exact shape.memory
  · rw [bi]; exact shape.bindings
  · rw [ba]; exact shape.base
  · rw [sc']; exact shape.scope
  · rw [tbindings]; exact shape.frameBindings
  · rw [twritable]; exact shape.writable
  · simp [NState.vectorSlot,sl,shape.slots,mainSlots]
  · rw [tbindings]; exact ctx.binding
  · rw [tstate]; exact rootGraph
  · rw [twritable,forestEq]; exact ctx.lengths
  · rw [twritable]; exact ctx.flag
  · simp [nodeS,nodeT] at live; omega
  · rw [storageT.2.1]; omega
  · rw [storageT.2.1]; omega
  · omega
  · omega

abbrev incJ : NExpr := .binary i32 .add (.variable i32 7) (.literal i32 1)
abbrev assignJ : NStmt := .assign 7 i32 incJ
abbrev incI : NExpr := .binary i32 .add (.variable i32 6) (.literal i32 1)
abbrev assignI : NStmt := .assign 6 i32 incI

theorem incJ_scalar : incJ.scalarOnly = true := by simp [NExpr.scalarOnly]
theorem incI_scalar : incI.scalarOnly = true := by simp [NExpr.scalarOnly]

theorem assignJ_step (S : NState) {P B K n w i j V vsc R sc scope rw}
    (shape : Sh8 S P B K n w i j V vsc R sc scope rw) (hj : j+1 < 2147483648) :
    ∃ t, assignJ.run S = some ⟨t,none,false⟩ ∧ Sh8 t P B K n w i (j+1) V vsc R sc scope rw ∧
      t.frame = S.frame ∧ S.scalars.work ≤ t.scalars.work ∧ t.scalars.work ≤ S.scalars.work+4 ∧
      S.scalars.peak ≤ t.scalars.peak ∧ t.scalars.peak ≤ max S.scalars.peak (liveS S+3) ∧
      S.peak ≤ t.peak ∧ t.peak ≤ max S.peak (t.scalars.peak+t.frame.state.storage.peak) ∧ liveS t = liveS S := by
  obtain ⟨slots,memory,bindings,base,sc',fb,wr⟩ := shape
  have vj := i32_valid_nat j (by omega)
  have vj1 := i32_valid_nat (j+1) hj
  have e7 : envOf S 7 i32 = some (j : Int) := envOf_at S 7 5 ⟨P.length+5,true⟩ i32 j
    (by simp [slots,mainSlots]) (by simp [bindings]) (by simp [memory]) vj
  have lit : i32.valid (1 : Int) = true := by simp [Ty.valid]
  have value : incJ.denote (envOf S) = some ((j : Int) + 1) := by
    have vj1' : i32.valid ((j : Int) + 1) = true := by simp [Ty.valid]; omega
    exact denote_inc (envOf S) 7 i32 j e7 lit (Ty.convert_of_valid _ _ vj1')
  obtain ⟨t,run,frame,sl,sc,me,bi,ba,gl,gu,gpl,gpu,ql,qu,live⟩ := assign_good incJ 7 5 i32 S _ ((j : Int)+1)
    ⟨P.length+5,true⟩ ⟨i32,j⟩ incJ_scalar value (Ty.convert_of_valid _ _ (by simp [Ty.valid]; omega))
    (by simp [slots,mainSlots]) (by simp [bindings]) (by simp [memory]) rfl vj rfl
  refine ⟨t,run,⟨?_,?_,?_,?_,?_,?_,?_⟩,frame,gl,?_,gpl,?_,ql,qu,live⟩
  · rw [sl]; exact slots
  · rw [me,memory]
    simp [List.set_append_right]
  · rw [bi]; exact bindings
  · rw [ba]; exact base
  · rw [sc]; exact sc'
  · rw [frame]; exact fb
  · rw [frame]; exact wr
  · simp [NExpr.nodes] at gu; omega
  · simp [NExpr.nodes] at gpu; omega

-- Every object lives in a scope at most `sc`; deeper scopes own nothing. The objects of
-- scope `sc` itself all belong to one tree (the table built by this call).
def Bnd (T : Proofs.CppNestedVectorStore.State) (sc : Nat) : Prop :=
  (∀ owner context, T.forest.context owner = some context → context ≤ sc) ∧
  ∃ root, ∀ owner, T.forest.context owner = some sc → T.forest.rootOwner owner = some root

theorem Bnd.fresh {T : Proofs.CppNestedVectorStore.State} {sc scope : Nat} (bound : Bnd T sc)
    (deeper : sc ≤ scope) : ∀ owner, T.forest.context owner ≠ some (scope+1) := by
  intro owner h
  have := bound.1 owner _ h
  omega

theorem Bnd.of_forest {T T' : Proofs.CppNestedVectorStore.State} {sc : Nat} (bound : Bnd T sc)
    (same : T'.forest = T.forest) : Bnd T' sc := by
  obtain ⟨le,root,tree⟩ := bound
  refine ⟨fun owner context h => le owner context (by rw [same] at h; exact h),root,fun owner h => ?_⟩
  rw [same] at h ⊢
  exact tree owner h

-- Data that stays fixed through the main loops.
structure Fixed where
  P : List Cell
  B : Nat
  K : Int
  n : Nat
  w : Nat
  V : Nat
  vsc : Nat
  R : Nat
  sc : Nat
  rw : List Bool
  items : List Int
  vbuf : Buffer Value
  SPB : Nat
  TPB : Nat

-- Two states with the same forest and object table differ only in counters.
def SameObjects (T T' : Proofs.CppNestedVectorStore.State) : Prop :=
  T'.forest = T.forest ∧ T'.storage.objects = T.storage.objects ∧ T'.storage.baseSpace = T.storage.baseSpace

theorem SameObjects.lookup {T T' : Proofs.CppNestedVectorStore.State} (same : SameObjects T T') (owner : Nat) :
    T'.storage.lookup owner = T.storage.lookup owner := by
  simp [Store.lookup,same.2.1]

theorem SameObjects.wellFormed {T T' : Proofs.CppNestedVectorStore.State} (same : SameObjects T T') :
    T'.wellFormed = T.wellFormed := by
  have check : T'.check = T.check := by
    funext o
    simp [State.check,same.1,same.lookup o,CppVectorOwnership.Forest.lookup]
  simp [State.wellFormed,same.1,same.2.1,check]

theorem SameObjects.liveSpace {T T' : Proofs.CppNestedVectorStore.State} (same : SameObjects T T') :
    T'.liveSpace = T.liveSpace := by
  have node : T'.nodeSpace = T.nodeSpace := by
    funext o
    simp [State.nodeSpace,same.1,same.lookup o]
  simp [State.liveSpace,same.2.1,node]

theorem SameObjects.rootGraph {T T' : Proofs.CppNestedVectorStore.State} {R sc w : Nat} {ty : Ty}
    (same : SameObjects T T') (g : RootGraph T R ty w sc) : RootGraph T' R ty w sc := by
  obtain ⟨buffer,found,epoch,items⟩ := g.buffer
  refine ⟨by rw [same.wellFormed]; exact g.valid,by rw [same.1]; exact g.tag,buffer,?_,epoch,items⟩
  rw [same.lookup]; exact found

theorem SameObjects.rows {T T' : Proofs.CppNestedVectorStore.State} {R n w : Nat} {items : List Int} {V : Nat}
    {vbuf : Buffer Value} {done : Nat} {cur : List Int} {curCap : Nat} (same : SameObjects T T')
    (rows : RowsOK T R n w items V vbuf done cur curCap) : RowsOK T' R n w items V vbuf done cur curCap := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [same.lookup]; exact rows.vFound
  · intro k lt
    obtain ⟨b,found,i1,c1,l1⟩ := rows.complete k lt
    exact ⟨b,by rw [same.lookup]; exact found,i1,c1,l1⟩
  · intro d
    obtain ⟨b,found,i1,c1,l1⟩ := rows.current d
    exact ⟨b,by rw [same.lookup]; exact found,i1,c1,l1⟩
  · intro k gt lt
    obtain ⟨b,found,i1,c1,l1⟩ := rows.untouched k gt lt
    exact ⟨b,by rw [same.lookup]; exact found,i1,c1,l1⟩

theorem SameObjects.bnd {T T' : Proofs.CppNestedVectorStore.State} {sc : Nat} (same : SameObjects T T')
    (bound : Bnd T sc) : Bnd T' sc := bound.of_forest same.1

theorem noopRetired_same (f : Frame) : SameObjects f.state (noopRetired f).state := ⟨rfl,rfl,rfl⟩

structure FixedOK (F : Fixed) : Prop where
  nEq : F.n = F.items.length
  itemsValid : ∀ x ∈ F.items, 0 ≤ x ∧ x < F.items.length
  nSmall : F.n < 2147483648
  wSmall : F.w < 2147483648
  before : F.V < F.R
  base : F.B ≤ F.P.length
  spb : F.P.length + 12 - F.B + 40 ≤ F.SPB

-- Invariant of the innermost loop at cell value `j` with `r` row entries written.
structure InnerInv (F : Fixed) (LC scope i W0 T0 slack : Nat) (S : NState) (j r : Nat) : Prop where
  shape : Sh8 S F.P F.B F.K F.n F.w i j F.V F.vsc F.R F.sc scope F.rw
  ctx : Ctx S F.R F.sc F.w
  bnd : Bnd S.frame.state F.sc
  rows : RowsOK S.frame.state F.R F.n F.w F.items F.V F.vbuf i ((tableRow F.items i).take r) F.n
  live : S.frame.state.liveSpace = LC
  space : LC+1-S.frame.state.storage.baseSpace ≤ F.TPB
  scalarWork : S.scalars.work ≤ W0+j*60+slack
  storageWork : S.frame.state.storage.work = T0+2*r
  scalarPeak : S.scalars.peak ≤ F.SPB
  storagePeak : S.frame.state.storage.peak ≤ F.TPB
  outerPeak : S.peak ≤ F.SPB+F.TPB

theorem liveS_sh8 {S : NState} {P B K n w i j V vsc R sc scope rw}
    (shape : Sh8 S P B K n w i j V vsc R sc scope rw) : liveS S = P.length+6-B+6 := by
  obtain ⟨_,memory,bindings,base,_,_,_⟩ := shape
  simp [liveS,memory,bindings,base]

theorem InnerInv.enter {F : Fixed} {LC : Nat} {scope i W0 T0 slack : Nat} {S : NState} {j r : Nat}
    (inv : InnerInv F LC scope i W0 T0 slack S j r) :
    InnerInv F LC (scope+1) i W0 T0 slack {S with scope := S.scope+1} j r := by
  obtain ⟨shape,ctx,bnd,rows,live,space,work,sw,sp,st,op⟩ := inv
  have hs : S.scope = scope := shape.scope
  refine ⟨⟨shape.slots,shape.memory,shape.bindings,shape.base,by simp [hs],shape.frameBindings,shape.writable⟩,
    ?_,bnd,rows,live,space,work,sw,sp,st,op⟩
  exact ⟨ctx.slot,ctx.binding,ctx.graph,ctx.lengths,ctx.flag⟩

theorem append_scope (F : Fixed) (ok : FixedOK F) {LC : Nat} {scope i W0 T0 slack j : Nat} {S1 : NState}
    (hi : 1 ≤ i) (iw : i < F.w) (jn : j < F.n) (inv : InnerInv F LC scope i W0 T0 slack S1 j j) :
    ∃ tA, appendStmt.run {S1 with scope := S1.scope+1} = some ⟨tA,none,false⟩ ∧
      InnerInv F LC (scope+1) i W0 T0 (slack+45) tA j (j+1) ∧
      tA.scalars.memory = S1.scalars.memory ∧ tA.frame.bindings = S1.frame.bindings := by
  have nSmall := ok.nSmall
  have wSmall := ok.wSmall
  have spb := ok.spb
  have baseOK := ok.base
  have entered := inv.enter
  obtain ⟨tA,run,shape,ctx,rows,live,forest,base,storageWork,storagePeak,storagePeakLow,gl,gu,gpl,gpu,ql,qu⟩ :=
    append_step {S1 with scope := S1.scope+1} F.items F.vbuf entered.shape entered.ctx entered.rows ok.before ok.nEq
      ok.itemsValid nSmall (by omega) (by omega) hi iw jn
  have liveS2 : liveS ({S1 with scope := S1.scope+1} : NState) = F.P.length+6-F.B+6 := liveS_sh8 entered.shape
  have sw := inv.scalarWork
  have sp := inv.scalarPeak
  have st := inv.storagePeak
  have op := inv.outerPeak
  have lv := inv.live
  have spc := inv.space
  have stw := inv.storageWork
  simp only [] at gu gpl gpu ql qu gl storageWork storagePeak storagePeakLow
  rw [liveS2] at gpu
  refine ⟨tA,run,⟨shape,ctx,?_,rows,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_⟩
  · exact inv.bnd.of_forest forest
  · rw [live]; exact lv
  · rw [base]; exact spc
  · omega
  · omega
  · omega
  · rw [lv] at storagePeak
    omega
  · rw [lv] at storagePeak
    omega
  · exact shape.memory.trans inv.shape.memory.symm
  · rw [shape.frameBindings]; exact inv.shape.frameBindings.symm

theorem leave_inv (F : Fixed) (ok : FixedOK F) {LC : Nat} {scope i W0 T0 slack slack' j r r' : Nat} {S1 tA : NState}
    (scopeLe : F.sc ≤ scope) (outer : InnerInv F LC scope i W0 T0 slack S1 j r')
    (inner : InnerInv F LC (scope+1) i W0 T0 slack' tA j r)
    (sameMemory : tA.scalars.memory = S1.scalars.memory) (sameBindings : tA.frame.bindings = S1.frame.bindings) :
    S1.leave tA none = some (S1.left tA) ∧ InnerInv F LC scope i W0 T0 (slack'+1) (S1.left tA) j r := by
  have spb := ok.spb
  have baseOK := ok.base
  have scopeEq : S1.scope = scope := outer.shape.scope
  have take : tA.scalars.memory.take S1.scalars.memory.length = S1.scalars.memory := by
    rw [sameMemory]; simp
  refine ⟨?_,?_⟩
  · apply leave_scalar S1 tA none (by simp)
    · rw [sameMemory]; exact Nat.le_refl _
    · rw [take]
    · exact inner.ctx.graph.valid
    · rw [scopeEq]; exact inner.bnd.fresh scopeLe
  · have same := noopRetired_same tA.frame
    have liveOuter := liveS_sh8 outer.shape
    have lengthTake : (tA.scalars.memory.take S1.scalars.memory.length).length = S1.scalars.memory.length := by
      rw [take]
    refine ⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,⟨?_,?_,?_,?_,?_⟩,same.bnd inner.bnd,same.rows inner.rows,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa using outer.shape.slots
    · rw [left_memory,take]; exact outer.shape.memory
    · rw [left_bindings]; exact outer.shape.bindings
    · rw [left_baseMemory]; exact outer.shape.base
    · rw [left_scope]; exact scopeEq
    · rw [left_frameBindings,sameBindings]; simpa using outer.shape.frameBindings
    · rw [left_rootWritable]; exact inner.shape.writable
    · simp [NState.vectorSlot,outer.shape.slots,mainSlots]
    · rw [left_frameBindings,sameBindings]; simpa using outer.ctx.binding
    · rw [left_state]; exact same.rootGraph inner.ctx.graph
    · rw [left_rootWritable,left_state]; exact inner.ctx.lengths
    · rw [left_rootWritable]; exact inner.ctx.flag
    · rw [left_state,same.liveSpace]; exact inner.live
    · rw [left_state]; show LC+1-(noopRetired tA.frame).state.storage.baseSpace ≤ F.TPB
      exact inner.space
    · rw [left_work]; have := inner.scalarWork; omega
    · rw [left_state]; exact inner.storageWork
    · rw [left_scalar_peak]; rw [lengthTake]
      have := outer.scalarPeak; have := inner.scalarPeak
      unfold liveS at liveOuter
      omega
    · rw [left_state]
      show max tA.frame.state.storage.peak (tA.frame.state.liveSpace-tA.frame.state.storage.baseSpace) ≤ F.TPB
      have := inner.storagePeak; have := inner.live; have := inner.space
      omega
    · rw [left_peak]
      have a := outer.outerPeak; have b := inner.outerPeak
      have c : (S1.left tA).scalars.peak ≤ F.SPB := by
        rw [left_scalar_peak,lengthTake]
        have := outer.scalarPeak; have := inner.scalarPeak
        unfold liveS at liveOuter
        omega
      have d : (noopRetired tA.frame).state.storage.peak ≤ F.TPB := by
        show max tA.frame.state.storage.peak (tA.frame.state.liveSpace-tA.frame.state.storage.baseSpace) ≤ F.TPB
        have := inner.storagePeak; have := inner.live; have := inner.space
        omega
      omega

theorem assign_inv (F : Fixed) (ok : FixedOK F) {LC : Nat} {scope i W0 T0 slack j : Nat} {S : NState}
    (jn : j+1 < F.n+1) (slackOK : slack+4 ≤ 60) (inv : InnerInv F LC scope i W0 T0 slack S j (j+1)) :
    ∃ t, assignJ.run S = some ⟨t,none,false⟩ ∧ InnerInv F LC scope i W0 T0 0 t (j+1) (j+1) := by
  have nSmall := ok.nSmall
  have spb := ok.spb
  have baseOK := ok.base
  obtain ⟨t,run,shape,frame,gl,gu,gpl,gpu,ql,qu,live⟩ := assignJ_step S inv.shape (by omega)
  have liveOuter := liveS_sh8 inv.shape
  have sw := inv.scalarWork
  have sp := inv.scalarPeak
  have st := inv.storagePeak
  have op := inv.outerPeak
  have fstate : t.frame.state = S.frame.state := by rw [frame]
  refine ⟨t,run,⟨shape,⟨?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · simp [NState.vectorSlot,shape.slots,mainSlots]
  · rw [frame]; exact inv.ctx.binding
  · rw [fstate]; exact inv.ctx.graph
  · rw [frame]; exact inv.ctx.lengths
  · rw [frame]; exact inv.ctx.flag
  · rw [fstate]; exact inv.bnd
  · rw [fstate]; exact inv.rows
  · rw [fstate]; exact inv.live
  · rw [fstate]; exact inv.space
  · omega
  · rw [fstate]; exact inv.storageWork
  · omega
  · rw [fstate]; exact st
  · rw [fstate] at qu; omega

abbrev innerBody : Command :=
  .sequence (.scope (.sequence (.primitive appendStmt) (.primitive .skip)))
    (.sequence (.primitive assignJ) (.primitive .skip))

theorem inner_body (F : Fixed) (ok : FixedOK F) {LC : Nat} {scope i W0 T0 j : Nat} {S1 : NState}
    (hi : 1 ≤ i) (iw : i < F.w) (jn : j < F.n) (scopeLe : F.sc ≤ scope)
    (inv : InnerInv F LC scope i W0 T0 4 S1 j j) :
    RunsTo innerBody S1 fun step => step.returned = none ∧ step.breaking = false ∧
      InnerInv F LC scope i W0 T0 0 step.state (j+1) (j+1) := by
  obtain ⟨tA,runA,invA,memA,bindA⟩ := append_scope F ok hi iw jn inv
  obtain ⟨leaveEq,invR⟩ := leave_inv F ok scopeLe inv invA memA bindA
  obtain ⟨tJ,runJ,invJ⟩ := assign_inv F ok (by omega) (by omega) invR
  apply RunsTo.seq
  apply RunsTo.scopeSimple
  apply RunsTo.seqSkip
  apply RunsTo.primitive runA
  refine ⟨rfl,rfl,rfl,rfl,S1.left tA,leaveEq,rfl,rfl,?_⟩
  apply RunsTo.seqSkip
  exact RunsTo.primitive runJ ⟨rfl,rfl,rfl,rfl,invJ⟩

theorem InnerInv.tick (F : Fixed) (ok : FixedOK F) {LC : Nat} {scope i W0 T0 j r : Nat} {t u : NState}
    (inv : InnerInv F LC scope i W0 T0 0 t j r) (good : Good t u 3 3) :
    InnerInv F LC scope i W0 T0 4 (u.charge 1 0) j r := by
  have spb := ok.spb
  have baseOK := ok.base
  obtain ⟨⟨frame,slots,scope',memory,bindings,base⟩,wl,wu,storage,pl,pu,ql,qu⟩ := good
  have liveOuter := liveS_sh8 inv.shape
  have sw := inv.scalarWork
  have sp := inv.scalarPeak
  have st := inv.storagePeak
  have op := inv.outerPeak
  have fstate : u.frame.state = t.frame.state := by rw [frame]
  have fbind : u.frame.bindings = t.frame.bindings := by rw [frame]
  have fwrite : u.frame.rootWritable = t.frame.rootWritable := by rw [frame]
  have st' : u.frame.state.storage.peak = t.frame.state.storage.peak := by rw [storage]
  have liveU : liveS u = liveS t := liveS_core ⟨frame,slots,scope',memory,bindings,base⟩
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,⟨?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [slots,inv.shape.slots]
  · simp [memory,inv.shape.memory]
  · simp [bindings,inv.shape.bindings]
  · simp [base,inv.shape.base]
  · simp [scope',inv.shape.scope]
  · simp [fbind,inv.shape.frameBindings]
  · simp [fwrite,inv.shape.writable]
  · simp [NState.vectorSlot,slots,inv.shape.slots,mainSlots]
  · simp [fbind]; exact inv.ctx.binding
  · simp [fstate]; exact inv.ctx.graph
  · simp [fwrite,fstate]; exact inv.ctx.lengths
  · simp [fwrite]; exact inv.ctx.flag
  · simp [fstate]; exact inv.bnd
  · simp [fstate]; exact inv.rows
  · simp [fstate]; exact inv.live
  · show LC+1-u.frame.state.storage.baseSpace ≤ F.TPB
    rw [fstate]; exact inv.space
  · simp [charge_work]; omega
  · simp [fstate]; exact inv.storageWork
  · simp only [charge_scalar_peak]; unfold liveS at liveOuter liveU pu; omega
  · simp [fstate]; exact st
  · simp only [charge_peak]; simp [fstate]
    unfold liveS at liveOuter liveU pu
    omega

abbrev loopCond : NExpr := .binary bl .lt (.variable i32 7) (.variable i32 2)
abbrev innerWhile : Command := .whileLoop loopCond innerBody

theorem loopCond_scalar : loopCond.scalarOnly = true := by simp [NExpr.scalarOnly]

theorem inner_loop (F : Fixed) (ok : FixedOK F) {LC : Nat} {scope i W0 T0 j0 : Nat} {S : NState}
    (hi : 1 ≤ i) (iw : i < F.w) (scopeLe : F.sc ≤ scope) (jle : j0 ≤ F.n)
    (inv : InnerInv F LC scope i W0 T0 0 S j0 j0) :
    RunsTo innerWhile S fun step => step.returned = none ∧ step.breaking = false ∧
      InnerInv F LC scope i W0 T0 4 step.state F.n F.n := by
  have nSmall := ok.nSmall
  have wSmall := ok.wSmall
  refine RunsTo.whileGhost (fun g t => ∃ j, g = F.n-j ∧ j ≤ F.n ∧ InnerInv F LC scope i W0 T0 0 t j j) _ ?_
    F.n (F.n-j0) S (by omega) ⟨j0,rfl,jle,inv⟩
  intro g t ⟨j,hg,hjle,tinv⟩
  obtain ⟨ei,ej,en⟩ := Sh8.value t tinv.shape (by omega) (by omega) (by omega)
  have value : loopCond.denote (envOf t) = some (if (j : Int) < (F.n : Int) then 1 else 0) :=
    denote_lt (envOf t) 7 2 i32 j F.n ej en
  obtain ⟨u,hu,good⟩ := scalar_eval loopCond t _ loopCond_scalar value
  have self := release_self good.1.1
  have ticked := tinv.tick F ok good
  refine ⟨u,_,hu,?_,?_⟩
  · intro zero
    have notLt : ¬ j < F.n := by
      intro h
      have : ((j : Int) < (F.n : Int)) := by omega
      simp [this] at zero
    have eq : j = F.n := by omega
    subst eq
    rw [self]
    exact ⟨rfl,rfl,ticked⟩
  · intro nonzero
    have lt : j < F.n := by
      by_cases h : j < F.n
      · exact h
      · have : ¬ ((j : Int) < (F.n : Int)) := by omega
        simp [this] at nonzero
    rw [self]
    refine (inner_body F ok hi iw lt scopeLe ticked).mono ?_
    intro step ⟨noReturn,notBreaking,post⟩
    exact ⟨noReturn,notBreaking,F.n-(j+1),by omega,j+1,rfl,by omega,post⟩

theorem liveS_sh6 {S : NState} {P B K n w i V vsc R sc scope rw}
    (shape : Sh6 S P B K n w i V vsc R sc scope rw) : liveS S = P.length+5-B+5 := by
  obtain ⟨_,memory,bindings,base,_,_,_⟩ := shape
  simp [liveS,memory,bindings,base]

theorem Sh6.value (S : NState) {P B K n w i V vsc R sc scope rw}
    (shape : Sh6 S P B K n w i V vsc R sc scope rw) (hi : i < 2147483648) (hw : w < 2147483648)
    (hn : n < 2147483648) :
    envOf S 6 i32 = some (i : Int) ∧ envOf S 4 i32 = some (w : Int) ∧ envOf S 2 i32 = some (n : Int) := by
  obtain ⟨slots,memory,bindings,base,_,_,_⟩ := shape
  refine ⟨envOf_at S 6 4 ⟨P.length+4,true⟩ i32 i (by simp [slots,mainSlots]) (by simp [bindings])
      (by simp [memory]) (i32_valid_nat i hi),
    envOf_at S 4 3 ⟨P.length+3,false⟩ i32 w (by simp [slots,mainSlots]) (by simp [bindings])
      (by simp [memory]) (i32_valid_nat w hw),
    envOf_at S 2 1 ⟨P.length+1,false⟩ i32 n (by simp [slots,mainSlots]) (by simp [bindings])
      (by simp [memory]) (i32_valid_nat n hn)⟩

theorem assignI_step (S : NState) {P B K n w i V vsc R sc scope rw}
    (shape : Sh6 S P B K n w i V vsc R sc scope rw) (hi : i+1 < 2147483648) :
    ∃ t, assignI.run S = some ⟨t,none,false⟩ ∧ Sh6 t P B K n w (i+1) V vsc R sc scope rw ∧
      t.frame = S.frame ∧ S.scalars.work ≤ t.scalars.work ∧ t.scalars.work ≤ S.scalars.work+4 ∧
      S.scalars.peak ≤ t.scalars.peak ∧ t.scalars.peak ≤ max S.scalars.peak (liveS S+3) ∧
      S.peak ≤ t.peak ∧ t.peak ≤ max S.peak (t.scalars.peak+t.frame.state.storage.peak) ∧ liveS t = liveS S := by
  obtain ⟨slots,memory,bindings,base,sc',fb,wr⟩ := shape
  have vi := i32_valid_nat i (by omega)
  have e6 : envOf S 6 i32 = some (i : Int) := envOf_at S 6 4 ⟨P.length+4,true⟩ i32 i
    (by simp [slots,mainSlots]) (by simp [bindings]) (by simp [memory]) vi
  have lit : i32.valid (1 : Int) = true := by simp [Ty.valid]
  have value : incI.denote (envOf S) = some ((i : Int) + 1) := by
    have vi1' : i32.valid ((i : Int) + 1) = true := by simp [Ty.valid]; omega
    exact denote_inc (envOf S) 6 i32 i e6 lit (Ty.convert_of_valid _ _ vi1')
  obtain ⟨t,run,frame,sl,sc,me,bi,ba,gl,gu,gpl,gpu,ql,qu,live⟩ := assign_good incI 6 4 i32 S _ ((i : Int)+1)
    ⟨P.length+4,true⟩ ⟨i32,i⟩ incI_scalar value (Ty.convert_of_valid _ _ (by simp [Ty.valid]; omega))
    (by simp [slots,mainSlots]) (by simp [bindings]) (by simp [memory]) rfl vi rfl
  refine ⟨t,run,⟨?_,?_,?_,?_,?_,?_,?_⟩,frame,gl,?_,gpl,?_,ql,qu,live⟩
  · rw [sl]; exact slots
  · rw [me,memory]
    simp [List.set_append_right]
  · rw [bi]; exact bindings
  · rw [ba]; exact base
  · rw [sc]; exact sc'
  · rw [frame]; exact fb
  · rw [frame]; exact wr
  · simp [NExpr.nodes] at gu; omega
  · simp [NExpr.nodes] at gpu; omega

abbrev cn : NExpr := .cast u64 (.variable i32 2)
abbrev reserveStmt : NStmt := .reserve (.row (.local 5) atom ci) i32 cn
abbrev declJ : NStmt := .declare i32 true (.literal i32 0)

theorem cn_scalar : cn.scalarOnly = true := by simp [NExpr.scalarOnly]

theorem Sh6.ci_value (S : NState) {P B K n w i V vsc R sc scope rw}
    (shape : Sh6 S P B K n w i V vsc R sc scope rw) (hi : i < 2147483648) (hw : w < 2147483648)
    (hn : n < 2147483648) : ci.denote (envOf S) = some (i : Int) := by
  obtain ⟨e6,_,_⟩ := Sh6.value S shape hi hw hn
  have valid : u64.valid (i : Int) = true := u64_valid_nat i (by omega)
  simp [NExpr.denote,e6,Ty.convert_of_valid _ _ valid]

theorem Sh6.cn_value (S : NState) {P B K n w i V vsc R sc scope rw}
    (shape : Sh6 S P B K n w i V vsc R sc scope rw) (hi : i < 2147483648) (hw : w < 2147483648)
    (hn : n < 2147483648) : cn.denote (envOf S) = some (n : Int) := by
  obtain ⟨_,_,e2⟩ := Sh6.value S shape hi hw hn
  have valid : u64.valid (n : Int) = true := u64_valid_nat n (by omega)
  simp [NExpr.denote,e2,Ty.convert_of_valid _ _ valid]

theorem sizeLimit_i32 (n : Nat) (small : n < 2147483648) : n ≤ CppVectorBindings.sizeLimit i32 := by
  simp [CppVectorBindings.sizeLimit]
  omega

theorem reserve_step (S : NState) {P B K n w i V vsc R sc scope rw} (items : List Int) (vbuf : Buffer Value)
    (shape : Sh6 S P B K n w i V vsc R sc scope rw) (ctx : Ctx S R sc w)
    (rows : RowsOK S.frame.state R n w items V vbuf i [] 0) (before : V < R) (iw : i < w)
    (hi : i < 2147483648) (hw : w < 2147483648) (hn : n < 2147483648) :
    ∃ t, reserveStmt.run S = some ⟨t,none,false⟩ ∧ Sh6 t P B K n w i V vsc R sc scope rw ∧ Ctx t R sc w ∧
      RowsOK t.frame.state R n w items V vbuf i [] n ∧
      t.frame.state.liveSpace = S.frame.state.liveSpace+n ∧
      t.frame.state.forest = S.frame.state.forest ∧
      t.frame.state.storage.baseSpace = S.frame.state.storage.baseSpace ∧
      t.frame.state.storage.work = S.frame.state.storage.work+1 ∧
      t.frame.state.storage.peak ≤ max S.frame.state.storage.peak
        (S.frame.state.liveSpace+n+1-S.frame.state.storage.baseSpace) ∧
      S.frame.state.storage.peak ≤ t.frame.state.storage.peak ∧
      S.scalars.work ≤ t.scalars.work ∧ t.scalars.work ≤ S.scalars.work+9 ∧
      S.scalars.peak ≤ t.scalars.peak ∧ t.scalars.peak ≤ max S.scalars.peak (liveS S+9) ∧
      S.peak ≤ t.peak ∧ t.peak ≤ max S.peak (t.scalars.peak+t.frame.state.storage.peak) := by
  obtain ⟨cur,foundCur,curItems,curCap,curLimit⟩ := rows.current iw
  have limit : n ≤ cur.limit := by rw [curLimit]; exact sizeLimit_i32 n hn
  obtain ⟨t,result,run,tframe,kind,sl,sc',me,bi,ba,gl,gu,gpl,gpu,ql,qu⟩ := reserve_row_stmt S 5 1 ci cn i n R w sc i32 cur
    ci_scalar (Sh6.ci_value S shape hi hw hn) cn_scalar (Sh6.cn_value S shape hi hw hn)
    (by simp [NState.vectorSlot,shape.slots,mainSlots]) (by simpa using ctx.binding) ctx.graph ctx.lengths ctx.flag
    iw foundCur limit
  obtain ⟨objectBuffer,object,foundObject⟩ := row_object S.frame R i32 w sc i ctx.graph iw
  have sameCur : objectBuffer = cur := by
    rw [foundCur] at foundObject
    exact (Option.some.inj foundObject).symm
  subst sameCur
  obtain ⟨_,curOwner,curValid,_,_⟩ := buffer_facts S.frame (R+1+i) i32 objectBuffer _ object
  have curEmpty : objectBuffer.items = [] := by
    rw [curItems]; simp
  have curZero : objectBuffer.capacity = 0 := curCap
  -- the new buffer is empty with capacity n in both cases
  obtain ⟨newBuffer,hnew,newItems,newCap,newLimit,newOwner,newValid⟩ :
      ∃ newBuffer : Buffer Value, result.buffer = newBuffer ∧ newBuffer.items = [] ∧ newBuffer.capacity = n ∧
        newBuffer.limit = CppVectorBindings.sizeLimit i32 ∧ newBuffer.owner = R+1+i ∧
        newBuffer.Valid (accepts (.integer i32)) := by
    rcases kind with ⟨grow,rfl⟩ | ⟨fits,rfl⟩
    · refine ⟨{objectBuffer with capacity := n,epoch := objectBuffer.epoch+1},rfl,by simpa using curEmpty,rfl,
        by simpa using curLimit,by simpa using curOwner,?_⟩
      exact CppVector.reserve_preserves_valid objectBuffer (accepts (.integer i32)) n curValid limit grow
    · have nz : n = 0 := by omega
      refine ⟨objectBuffer,rfl,curEmpty,by omega,curLimit,curOwner,curValid⟩
  have wf := row_update_valid S.frame R i32 w sc i ctx.graph iw objectBuffer newBuffer result foundCur hnew
    newOwner newValid
  have bound := CppVectorStore.lookup_bound S.frame.state.storage (R+1+i) objectBuffer foundCur
  have updatedSelf := CppNestedOps.updated_lookup_self S.frame (R+1+i) objectBuffer result bound
  have updatedOther : ∀ o, o ≠ R+1+i → (S.frame.updated (R+1+i) objectBuffer result).state.storage.lookup o =
      S.frame.state.storage.lookup o := fun o different =>
    CppNestedOps.updated_lookup_other S.frame (R+1+i) o objectBuffer result (by omega)
  have rootGraph := rootGraph_updated S.frame R i32 w sc ctx.graph (R+1+i) objectBuffer result (by omega) wf
  have tstate : t.frame.state = (S.frame.updated (R+1+i) objectBuffer result).state := by rw [tframe]
  have tbindings : t.frame.bindings = S.frame.bindings := by simp [tframe,Frame.updated]
  have twritable : t.frame.rootWritable = S.frame.rootWritable := by simp [tframe,Frame.updated]
  have rows' : RowsOK t.frame.state R n w items V vbuf i [] n :=
    rowsOK_set [] n rows before iw newBuffer (by rw [tstate,updatedSelf,hnew])
      (by intro o ho; rw [tstate]; exact updatedOther o ho) (by simp [newItems]) newCap newLimit
  have rowTagS := row_tag S.frame R i32 w sc i ctx.graph iw
  have lengthsEq : t.frame.state.storage.objects.length = S.frame.state.storage.objects.length := by
    rw [tstate]; simp [Frame.updated]
  have forestEq : t.frame.state.forest = S.frame.state.forest := by rw [tstate]; rfl
  have live := liveSpace_update S.frame.state t.frame.state (R+1+i) bound lengthsEq forestEq
    (by intro o ho; rw [tstate]; exact updatedOther o ho)
  have nodeS := nodeSpace_row S.frame.state i32 R i objectBuffer rowTagS foundCur
  have nodeT := nodeSpace_row t.frame.state i32 R i newBuffer (by rw [forestEq]; exact rowTagS)
    (by rw [tstate,updatedSelf,hnew])
  rw [nodeS,curZero] at live
  rw [nodeT,newCap] at live
  have storageT : t.frame.state.storage.work = S.frame.state.storage.work+1 ∧
      t.frame.state.storage.baseSpace = S.frame.state.storage.baseSpace ∧
      S.frame.state.storage.peak ≤ t.frame.state.storage.peak ∧
      t.frame.state.storage.peak ≤ max S.frame.state.storage.peak
        (S.frame.state.liveSpace+n+1-S.frame.state.storage.baseSpace) := by
    rw [tstate]
    rcases kind with ⟨grow,rfl⟩ | ⟨fits,rfl⟩
    · simp [Frame.updated,curEmpty]; omega
    · have nz : n = 0 := by have := curZero; omega
      subst nz
      simp [Frame.updated]; omega
  simp [NExpr.nodes] at gu gpu
  refine ⟨t,run,⟨?_,?_,?_,?_,?_,?_,?_⟩,⟨?_,?_,?_,?_,?_⟩,rows',?_,forestEq,storageT.2.1,storageT.1,
    storageT.2.2.2,storageT.2.2.1,gl,?_,gpl,?_,ql,qu⟩
  · rw [sl]; exact shape.slots
  · rw [me]; exact shape.memory
  · rw [bi]; exact shape.bindings
  · rw [ba]; exact shape.base
  · rw [sc']; exact shape.scope
  · rw [tbindings]; exact shape.frameBindings
  · rw [twritable]; exact shape.writable
  · simp [NState.vectorSlot,sl,shape.slots,mainSlots]
  · rw [tbindings]; exact ctx.binding
  · rw [tstate]; exact rootGraph
  · rw [twritable,forestEq]; exact ctx.lengths
  · rw [twritable]; exact ctx.flag
  · omega
  · omega
  · omega

-- Invariant of the outer loop test: rows below `i` are complete, `i` is untouched.
structure OuterInv (F : Fixed) (scope L0 W0 T0 slack : Nat) (S : NState) (i : Nat) : Prop where
  shape : Sh6 S F.P F.B F.K F.n F.w i F.V F.vsc F.R F.sc scope F.rw
  ctx : Ctx S F.R F.sc F.w
  bnd : Bnd S.frame.state F.sc
  rows : RowsOK S.frame.state F.R F.n F.w F.items F.V F.vbuf i [] 0
  live : S.frame.state.liveSpace = L0+F.w+1+F.n*i
  space : L0+F.w+F.n*F.w+3 ≤ F.TPB
  scalarWork : S.scalars.work ≤ W0+(i-1)*(60*F.n+200)+slack
  storageWork : S.frame.state.storage.work = T0+(i-1)*(2*F.n+1)
  scalarPeak : S.scalars.peak ≤ F.SPB
  storagePeak : S.frame.state.storage.peak ≤ F.TPB
  outerPeak : S.peak ≤ F.SPB+F.TPB

abbrev outerCond : NExpr := .binary bl .lt (.variable i32 6) (.variable i32 4)
theorem outerCond_scalar : outerCond.scalarOnly = true := by simp [NExpr.scalarOnly]

theorem OuterInv.tick (F : Fixed) (ok : FixedOK F) {scope L0 W0 T0 i : Nat} {t u : NState}
    (inv : OuterInv F scope L0 W0 T0 0 t i) (good : Good t u 3 3) :
    OuterInv F scope L0 W0 T0 4 (u.charge 1 0) i := by
  have spb := ok.spb
  have baseOK := ok.base
  obtain ⟨⟨frame,slots,scope',memory,bindings,base⟩,wl,wu,storage,pl,pu,ql,qu⟩ := good
  have liveOuter := liveS_sh6 inv.shape
  have sw := inv.scalarWork
  have sp := inv.scalarPeak
  have st := inv.storagePeak
  have op := inv.outerPeak
  have fstate : u.frame.state = t.frame.state := by rw [frame]
  have fbind : u.frame.bindings = t.frame.bindings := by rw [frame]
  have fwrite : u.frame.rootWritable = t.frame.rootWritable := by rw [frame]
  have st' : u.frame.state.storage.peak = t.frame.state.storage.peak := by rw [storage]
  have liveU : liveS u = liveS t := liveS_core ⟨frame,slots,scope',memory,bindings,base⟩
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,⟨?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [slots,inv.shape.slots]
  · simp [memory,inv.shape.memory]
  · simp [bindings,inv.shape.bindings]
  · simp [base,inv.shape.base]
  · simp [scope',inv.shape.scope]
  · simp [fbind,inv.shape.frameBindings]
  · simp [fwrite,inv.shape.writable]
  · simp [NState.vectorSlot,slots,inv.shape.slots,mainSlots]
  · simp [fbind]; exact inv.ctx.binding
  · simp [fstate]; exact inv.ctx.graph
  · simp [fwrite,fstate]; exact inv.ctx.lengths
  · simp [fwrite]; exact inv.ctx.flag
  · simp [fstate]; exact inv.bnd
  · simp [fstate]; exact inv.rows
  · simp [fstate]; exact inv.live
  · exact inv.space
  · simp [charge_work]; omega
  · simp [fstate]; exact inv.storageWork
  · simp only [charge_scalar_peak]; unfold liveS at liveOuter liveU pu; omega
  · simp [fstate]; exact st
  · simp only [charge_peak]; simp [fstate]
    unfold liveS at liveOuter liveU pu
    omega

theorem OuterInv.enter {F : Fixed} {scope L0 W0 T0 slack i : Nat} {S : NState}
    (inv : OuterInv F scope L0 W0 T0 slack S i) :
    OuterInv F (scope+1) L0 W0 T0 slack {S with scope := S.scope+1} i := by
  obtain ⟨shape,ctx,bnd,rows,live,space,sw,stw,sp,st,op⟩ := inv
  have hs : S.scope = scope := shape.scope
  refine ⟨⟨shape.slots,shape.memory,shape.bindings,shape.base,by simp [hs],shape.frameBindings,shape.writable⟩,
    ⟨ctx.slot,ctx.binding,ctx.graph,ctx.lengths,ctx.flag⟩,bnd,rows,live,space,sw,stw,sp,st,op⟩

-- Finishing row `i` and moving on to row `i+1`.
theorem rowsOK_advance {T : Proofs.CppNestedVectorStore.State} {R n w : Nat} {items : List Int} {V : Nat}
    {vbuf : Buffer Value} {i : Nat} (nEq : n = items.length) (iw : i < w)
    (rows : RowsOK T R n w items V vbuf i ((tableRow items i).take n) n) :
    RowsOK T R n w items V vbuf (i+1) [] 0 := by
  have full : (tableRow items i).take n = tableRow items i := by
    apply List.take_of_length_le
    rw [tableRow_length]; omega
  refine ⟨rows.vFound,?_,?_,?_⟩
  · intro k lt
    by_cases earlier : k < i
    · exact rows.complete k earlier
    · have same : k = i := by omega
      subst same
      obtain ⟨b,found,items',cap,limit⟩ := rows.current iw
      exact ⟨b,found,by rw [items',full],cap,limit⟩
  · intro next
    exact rows.untouched (i+1) (by omega) next
  · intro k gt lt
    exact rows.untouched k (by omega) lt

theorem declJ_step (S : NState) {P B K n w i V vsc R sc scope rw}
    (shape : Sh6 S P B K n w i V vsc R sc scope rw) :
    ∃ t, declJ.run S = some ⟨t,none,false⟩ ∧ Sh8 t P B K n w i 0 V vsc R sc scope rw ∧
      t.frame = S.frame ∧ S.scalars.work ≤ t.scalars.work ∧ t.scalars.work ≤ S.scalars.work+2 ∧
      S.scalars.peak ≤ t.scalars.peak ∧ t.scalars.peak ≤ max S.scalars.peak (liveS S+2) ∧
      S.peak ≤ t.peak ∧ t.peak ≤ max S.peak (t.scalars.peak+t.frame.state.storage.peak) := by
  have valid : i32.valid (0 : Int) = true := by simp [Ty.valid]
  obtain ⟨t,run,frame,sl,sc',me,bi,ba,gl,gu,gpl,gpu,ql,qu⟩ := declare_good (.literal i32 0) i32 true S 0 0
    (by simp [NExpr.scalarOnly]) (by simp [NExpr.denote,valid]) (Ty.convert_of_valid _ _ valid)
  have memLength : S.scalars.memory.length = P.length+5 := by simp [shape.memory]
  have bindLength : S.scalars.bindings.length = 5 := by simp [shape.bindings]
  refine ⟨t,run,⟨?_,?_,?_,?_,?_,?_,?_⟩,frame,gl,?_,gpl,?_,ql,qu⟩
  · rw [sl,bindLength,shape.slots]; simp [mainSlots]
  · rw [me,shape.memory]; simp
  · rw [bi,memLength,shape.bindings]; simp
  · rw [ba]; exact shape.base
  · rw [sc']; exact shape.scope
  · rw [frame]; exact shape.frameBindings
  · rw [frame]; exact shape.writable
  · simpa [NExpr.nodes] using gu
  · simpa [NExpr.nodes] using gpu

theorem le_cap (x y a b cap : Nat) (hx : x ≤ max y (a+b)) (hy : y ≤ cap) (hab : a+b ≤ cap) : x ≤ cap := by
  omega

theorem le_cap1 (x y e cap : Nat) (hx : x ≤ max y e) (hy : y ≤ cap) (he : e ≤ cap) : x ≤ cap := by
  omega

theorem cap_live (P B SPB : Nat) (base : B ≤ P) (spb : P+12-B+40 ≤ SPB) (k : Nat) (hk : k ≤ 40) :
    P+5-B+5+k ≤ SPB := by omega

theorem cap_space (live L0 w n i TPB base : Nat) (lv : live = L0+w+1+n*i) (spc : L0+w+n*w+3 ≤ TPB)
    (fmul : n*(i+1) ≤ n*w) (mulEq : n*(i+1) = n*i+n) : live+n+1-base ≤ TPB := by omega

theorem mul_succ_le (n i w : Nat) (h : i+1 ≤ w) : n*(i+1) ≤ n*w := Nat.mul_le_mul_left n h

theorem prepare_inner (F : Fixed) (ok : FixedOK F) {scope L0 W0 T0 i : Nat} (lc : Nat)
    (hlc : lc = L0+F.w+1+F.n*(i+1)) {S1 : NState}
    (hi : 1 ≤ i) (iw : i < F.w) (inv : OuterInv F scope L0 W0 T0 4 S1 i) :
    ∃ tR tD, reserveStmt.run {S1 with scope := S1.scope+1} = some ⟨tR,none,false⟩ ∧
      declJ.run {tR with scope := tR.scope+1} = some ⟨tD,none,false⟩ ∧
      Sh6 tR F.P F.B F.K F.n F.w i F.V F.vsc F.R F.sc (scope+1) F.rw ∧
      InnerInv F lc (scope+2) i tD.scalars.work tD.frame.state.storage.work 0 tD 0 0 ∧
      tD.scalars.work ≤ S1.scalars.work+11 ∧ tD.frame.state.storage.work = S1.frame.state.storage.work+1 ∧
      tD.frame = tR.frame ∧ tR.frame.state.liveSpace = lc ∧
      tR.scalars.memory = S1.scalars.memory ∧ tR.scalars.bindings = S1.scalars.bindings ∧
      Ctx tR F.R F.sc F.w ∧ Bnd tR.frame.state F.sc ∧
      tR.scalars.work ≤ S1.scalars.work+9 ∧ tR.frame.state.storage.work = S1.frame.state.storage.work+1 ∧
      tR.scalars.peak ≤ F.SPB ∧ tR.peak ≤ F.SPB+F.TPB := by
  have nSmall := ok.nSmall
  have wSmall := ok.wSmall
  have spb := ok.spb
  have baseOK := ok.base
  have entered := inv.enter
  obtain ⟨tR,runR,shapeR,ctxR,rowsR,liveR,forestR,baseR,workR,peakR,peakRLow,rwl,rwu,rpl,rpu,rql,rqu⟩ :=
    reserve_step {S1 with scope := S1.scope+1} F.items F.vbuf entered.shape entered.ctx entered.rows ok.before iw
      (by omega) wSmall nSmall
  have shape3 : Sh6 {tR with scope := tR.scope+1} F.P F.B F.K F.n F.w i F.V F.vsc F.R F.sc (scope+2) F.rw :=
    ⟨shapeR.slots,shapeR.memory,shapeR.bindings,shapeR.base,by simp [shapeR.scope],shapeR.frameBindings,
      shapeR.writable⟩
  obtain ⟨tD,runD,shapeD,frameD,dwl,dwu,dpl,dpu,dql,dqu⟩ := declJ_step {tR with scope := tR.scope+1} shape3
  have bndR : Bnd tR.frame.state F.sc := inv.bnd.of_forest forestR
  have liveS1 := liveS_sh6 inv.shape
  have liveR1 : liveS tR = F.P.length+5-F.B+5 := liveS_sh6 shapeR
  have sw := inv.scalarWork
  have sp := inv.scalarPeak
  have st := inv.storagePeak
  have op := inv.outerPeak
  have lv := inv.live
  have spc := inv.space
  have stw := inv.storageWork
  have fmul := mul_succ_le F.n i F.w (by omega)
  have mulEq : F.n*(i+1) = F.n*i+F.n := Nat.mul_succ F.n i
  have stateEq : tD.frame.state = tR.frame.state := by rw [frameD]
  have liveR' : tR.frame.state.liveSpace = S1.frame.state.liveSpace+F.n := liveR
  have liveTR : tR.frame.state.liveSpace = lc := by
    rw [liveR',hlc]; omega
  have rwu' : tR.scalars.work ≤ S1.scalars.work+9 := rwu
  have workR' : tR.frame.state.storage.work = S1.frame.state.storage.work+1 := workR
  have baseR' : tR.frame.state.storage.baseSpace = S1.frame.state.storage.baseSpace := baseR
  have dwu' : tD.scalars.work ≤ tR.scalars.work+2 := dwu
  have dpu' : tD.scalars.peak ≤ max tR.scalars.peak (liveS tR+2) := dpu
  have rpu' : tR.scalars.peak ≤ max S1.scalars.peak (liveS S1+9) := rpu
  have rqu' : tR.peak ≤ max S1.peak (tR.scalars.peak+tR.frame.state.storage.peak) := rqu
  have dqu' : tD.peak ≤ max tR.peak (tD.scalars.peak+tD.frame.state.storage.peak) := dqu
  have peakR' : tR.frame.state.storage.peak ≤ max S1.frame.state.storage.peak
      (S1.frame.state.liveSpace+F.n+1-S1.frame.state.storage.baseSpace) := peakR
  have stTD : tD.frame.state.storage.peak = tR.frame.state.storage.peak := by rw [stateEq]
  have workTD : tD.frame.state.storage.work = tR.frame.state.storage.work := by rw [stateEq]
  have liveS3 : liveS tR = F.P.length+5-F.B+5 := liveR1
  have liveSD : liveS S1 = F.P.length+5-F.B+5 := liveS1
  have hRsp : tR.scalars.peak ≤ F.SPB := le_cap _ _ _ _ _ rpu' sp
    (by rw [liveSD]; exact cap_live _ _ _ baseOK spb 9 (by omega))
  have hRst : tR.frame.state.storage.peak ≤ F.TPB := le_cap1 _ _ _ _ peakR' st
    (by
      have := cap_space S1.frame.state.liveSpace L0 F.w F.n i F.TPB S1.frame.state.storage.baseSpace lv spc fmul mulEq
      exact this)
  have hRo : tR.peak ≤ F.SPB+F.TPB := le_cap _ _ _ _ _ rqu' op (Nat.add_le_add hRsp hRst)
  refine ⟨tR,tD,runR,runD,shapeR,⟨shapeD,⟨?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [NState.vectorSlot,shapeD.slots,mainSlots]
  · rw [frameD]; exact ctxR.binding
  · rw [stateEq]; exact ctxR.graph
  · rw [frameD]; exact ctxR.lengths
  · rw [frameD]; exact ctxR.flag
  · rw [stateEq]; exact bndR
  · rw [stateEq]; exact rowsR
  · rw [stateEq]; exact liveTR
  · have : lc+1-tD.frame.state.storage.baseSpace ≤ F.TPB := by
      rw [stateEq]; omega
    exact this
  · omega
  · omega
  · have a : tR.scalars.peak ≤ F.SPB := le_cap _ _ _ _ _ rpu' sp
      (by rw [liveSD]; exact cap_live _ _ _ baseOK spb 9 (by omega))
    have b : tD.scalars.peak ≤ F.SPB := le_cap _ _ _ _ _ dpu' a
      (by rw [liveS3]; exact cap_live _ _ _ baseOK spb 2 (by omega))
    exact b
  · have a : tR.frame.state.storage.peak ≤ F.TPB := le_cap1 _ _ _ _ peakR' st
      (by
        have := cap_space S1.frame.state.liveSpace L0 F.w F.n i F.TPB S1.frame.state.storage.baseSpace lv spc fmul mulEq
        exact this)
    have b : tD.frame.state.storage.peak ≤ F.TPB := by rw [stTD]; exact a
    exact b
  · have a : tR.scalars.peak ≤ F.SPB := le_cap _ _ _ _ _ rpu' sp
      (by rw [liveSD]; exact cap_live _ _ _ baseOK spb 9 (by omega))
    have b : tD.scalars.peak ≤ F.SPB := le_cap _ _ _ _ _ dpu' a
      (by rw [liveS3]; exact cap_live _ _ _ baseOK spb 2 (by omega))
    have c : tR.frame.state.storage.peak ≤ F.TPB := le_cap1 _ _ _ _ peakR' st
      (by
        have := cap_space S1.frame.state.liveSpace L0 F.w F.n i F.TPB S1.frame.state.storage.baseSpace lv spc fmul mulEq
        exact this)
    have d : tR.peak ≤ F.SPB+F.TPB := le_cap _ _ _ _ _ rqu' op (by omega)
    have e : tD.peak ≤ F.SPB+F.TPB := le_cap _ _ _ _ _ dqu' d (by rw [stTD]; omega)
    exact e
  · omega
  · omega
  · exact frameD
  · exact liveTR
  · exact shapeR.memory.trans (entered.shape.memory.symm)
  · exact shapeR.bindings.trans (entered.shape.bindings.symm)
  · exact ctxR
  · exact bndR
  · omega
  · exact workR'
  · exact hRsp
  · exact hRo

-- After the inner loop: row `i` is complete; only the loop counter update remains.
structure Mid (F : Fixed) (scope lc Wb Tb : Nat) (S : NState) (i : Nat) : Prop where
  shape : Sh6 S F.P F.B F.K F.n F.w i F.V F.vsc F.R F.sc scope F.rw
  ctx : Ctx S F.R F.sc F.w
  bnd : Bnd S.frame.state F.sc
  rows : RowsOK S.frame.state F.R F.n F.w F.items F.V F.vbuf i ((tableRow F.items i).take F.n) F.n
  live : S.frame.state.liveSpace = lc
  space : lc+1-S.frame.state.storage.baseSpace ≤ F.TPB
  scalarWork : S.scalars.work ≤ Wb
  storageWork : S.frame.state.storage.work = Tb
  scalarPeak : S.scalars.peak ≤ F.SPB
  storagePeak : S.frame.state.storage.peak ≤ F.TPB
  outerPeak : S.peak ≤ F.SPB+F.TPB

theorem take_cells (P : List Cell) (a b c d e f : Cell) :
    (P ++ [a,b,c,d,e,f]).take (P.length+5) = P ++ [a,b,c,d,e] := by
  have h : P.take (P.length+5) = P := List.take_of_length_le (by omega)
  simp [List.take_append,h]

theorem mid_scalar (a b e sp : Nat) (ha : a ≤ sp) (hb : b ≤ sp) (he : e ≤ sp) : max (max a b) e ≤ sp := by
  omega

theorem mid_peak (a b c d sp tp : Nat) (ha : a ≤ sp+tp) (hb : b ≤ sp+tp) (hc : c ≤ sp) (hd : d ≤ tp) :
    max (max a b) (c+d) ≤ sp+tp := by omega

theorem mid_storage (a l base tp : Nat) (ha : a ≤ tp) (h : l+1-base ≤ tp) : max a (l-base) ≤ tp := by omega

theorem leave_mid1 (F : Fixed) (ok : FixedOK F) {scope lc W T W' T' i : Nat} {tR tL : NState}
    (shapeR : Sh6 tR F.P F.B F.K F.n F.w i F.V F.vsc F.R F.sc (scope+1) F.rw)
    (ctxR : Ctx tR F.R F.sc F.w) (bndR : Bnd tR.frame.state F.sc) (scopeLe : F.sc ≤ scope+1)
    (hR : tR.scalars.peak ≤ F.SPB) (hRo : tR.peak ≤ F.SPB+F.TPB)
    (outerBind : tR.frame.bindings = [vbind F.V F.vsc,rbind F.R F.sc])
    (inner : InnerInv F lc (scope+2) i W' T' 4 tL F.n F.n) :
    tR.leave tL none = some (tR.left tL) ∧ Mid F (scope+1) lc (tL.scalars.work+1) (tL.frame.state.storage.work) (tR.left tL) i := by
  have spb := ok.spb
  have baseOK := ok.base
  have innerShape := inner.shape
  have take : tL.scalars.memory.take tR.scalars.memory.length = tR.scalars.memory := by
    rw [innerShape.memory,shapeR.memory]
    have : (F.P ++ [⟨u64,F.K⟩,⟨i32,F.n⟩,⟨i32,F.w⟩,⟨i32,F.w⟩,⟨i32,i⟩] : List Cell).length = F.P.length+5 := by simp
    rw [this]
    exact take_cells _ _ _ _ _ _ _
  have fits : tR.scalars.memory.length ≤ tL.scalars.memory.length := by
    rw [innerShape.memory,shapeR.memory]; simp
  have lengthTake : (tL.scalars.memory.take tR.scalars.memory.length).length = tR.scalars.memory.length := by
    rw [take]
  have liveR : liveS tR = F.P.length+5-F.B+5 := liveS_sh6 shapeR
  refine ⟨?_,?_⟩
  · apply leave_scalar tR tL none (by simp) fits (by rw [take]) inner.ctx.graph.valid
    rw [shapeR.scope]
    exact inner.bnd.fresh scopeLe
  · have same := noopRetired_same tL.frame
    refine ⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,⟨?_,?_,?_,?_,?_⟩,same.bnd inner.bnd,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa using shapeR.slots
    · rw [left_memory,take]; exact shapeR.memory
    · rw [left_bindings]; exact shapeR.bindings
    · rw [left_baseMemory]; exact shapeR.base
    · rw [left_scope]; exact shapeR.scope
    · rw [left_frameBindings,innerShape.frameBindings,outerBind]; simp
    · rw [left_rootWritable]; exact innerShape.writable
    · simp [NState.vectorSlot,shapeR.slots,mainSlots]
    · rw [left_frameBindings,innerShape.frameBindings,outerBind]; simp [rbind]
    · rw [left_state]; exact same.rootGraph inner.ctx.graph
    · rw [left_rootWritable,left_state]; exact inner.ctx.lengths
    · rw [left_rootWritable]; exact inner.ctx.flag
    · rw [left_state]
      simpa using same.rows (by simpa using inner.rows)
    · rw [left_state,same.liveSpace]; exact inner.live
    · exact inner.space
    · rw [left_work]; exact Nat.le_refl _
    · rw [left_state]; rfl
    · rw [left_scalar_peak,lengthTake]
      have e : tR.scalars.memory.length-tR.scalars.baseMemory+tR.scalars.bindings.length+0 ≤ F.SPB := by
        have := liveR; unfold liveS at this; rw [this]; exact cap_live _ _ _ baseOK spb 0 (by omega)
      exact mid_scalar _ _ _ _ hR inner.scalarPeak e
    · rw [left_state]
      show max tL.frame.state.storage.peak (tL.frame.state.liveSpace-tL.frame.state.storage.baseSpace) ≤ F.TPB
      rw [inner.live]
      exact mid_storage _ _ _ _ inner.storagePeak inner.space
    · rw [left_peak]
      have e : tR.scalars.memory.length-tR.scalars.baseMemory+tR.scalars.bindings.length+0 ≤ F.SPB := by
        have := liveR; unfold liveS at this; rw [this]; exact cap_live _ _ _ baseOK spb 0 (by omega)
      have hs : (tR.left tL).scalars.peak ≤ F.SPB := by
        rw [left_scalar_peak,lengthTake]; exact mid_scalar _ _ _ _ hR inner.scalarPeak e
      have ht : (noopRetired tL.frame).state.storage.peak ≤ F.TPB := by
        show max tL.frame.state.storage.peak (tL.frame.state.liveSpace-tL.frame.state.storage.baseSpace) ≤ F.TPB
        rw [inner.live]; exact mid_storage _ _ _ _ inner.storagePeak inner.space
      exact mid_peak _ _ _ _ _ _ hRo inner.outerPeak hs ht


theorem leave_mid2 (F : Fixed) (ok : FixedOK F) {scope lc Wb Tb : Nat} {i : Nat} {S1 L1 : NState}
    (outerShape : Sh6 S1 F.P F.B F.K F.n F.w i F.V F.vsc F.R F.sc scope F.rw) (scopeLe : F.sc ≤ scope)
    (hS : S1.scalars.peak ≤ F.SPB) (hSo : S1.peak ≤ F.SPB+F.TPB)
    (inner : Mid F (scope+1) lc Wb Tb L1 i) :
    S1.leave L1 none = some (S1.left L1) ∧ Mid F scope lc (Wb+1) Tb (S1.left L1) i := by
  have spb := ok.spb
  have baseOK := ok.base
  have innerShape := inner.shape
  have take : L1.scalars.memory.take S1.scalars.memory.length = S1.scalars.memory := by
    rw [innerShape.memory,outerShape.memory]; exact List.take_length
  have fits : S1.scalars.memory.length ≤ L1.scalars.memory.length := by
    rw [innerShape.memory,outerShape.memory]; simp
  have lengthTake : (L1.scalars.memory.take S1.scalars.memory.length).length = S1.scalars.memory.length := by
    rw [take]
  have liveS1 : liveS S1 = F.P.length+5-F.B+5 := liveS_sh6 outerShape
  have sameBind : L1.frame.bindings = S1.frame.bindings := by
    rw [innerShape.frameBindings,outerShape.frameBindings]
  refine ⟨?_,?_⟩
  · apply leave_scalar S1 L1 none (by simp) fits (by rw [take]) inner.ctx.graph.valid
    rw [outerShape.scope]
    exact inner.bnd.fresh scopeLe
  · have same := noopRetired_same L1.frame
    have e : S1.scalars.memory.length-S1.scalars.baseMemory+S1.scalars.bindings.length+0 ≤ F.SPB := by
      have := liveS1; unfold liveS at this; rw [this]; exact cap_live _ _ _ baseOK spb 0 (by omega)
    have hs : (S1.left L1).scalars.peak ≤ F.SPB := by
      rw [left_scalar_peak,lengthTake]; exact mid_scalar _ _ _ _ hS inner.scalarPeak e
    have ht : (noopRetired L1.frame).state.storage.peak ≤ F.TPB := by
      show max L1.frame.state.storage.peak (L1.frame.state.liveSpace-L1.frame.state.storage.baseSpace) ≤ F.TPB
      rw [inner.live]
      exact mid_storage _ _ _ _ inner.storagePeak inner.space
    refine ⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,⟨?_,?_,?_,?_,?_⟩,same.bnd inner.bnd,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa using outerShape.slots
    · rw [left_memory,take]; exact outerShape.memory
    · rw [left_bindings]; exact outerShape.bindings
    · rw [left_baseMemory]; exact outerShape.base
    · rw [left_scope]; exact outerShape.scope
    · rw [left_frameBindings,sameBind]; simpa using outerShape.frameBindings
    · rw [left_rootWritable]; exact innerShape.writable
    · simp [NState.vectorSlot,outerShape.slots,mainSlots]
    · rw [left_frameBindings,sameBind,outerShape.frameBindings]; simp [rbind]
    · rw [left_state]; exact same.rootGraph inner.ctx.graph
    · rw [left_rootWritable,left_state]; exact inner.ctx.lengths
    · rw [left_rootWritable]; exact inner.ctx.flag
    · rw [left_state]; simpa using same.rows inner.rows
    · rw [left_state,same.liveSpace]; exact inner.live
    · exact inner.space
    · rw [left_work]; have := inner.scalarWork; omega
    · rw [left_state]; exact inner.storageWork
    · exact hs
    · exact ht
    · rw [left_peak]; exact mid_peak _ _ _ _ _ _ hSo inner.outerPeak hs ht

theorem finish_outer (F : Fixed) (ok : FixedOK F) {scope L0 W0 T0 lc Wb Tb i : Nat} {S : NState}
    (iw : i < F.w) (hlc : lc = L0+F.w+1+F.n*(i+1)) (space : L0+F.w+F.n*F.w+3 ≤ F.TPB)
    (work : Wb+4 ≤ W0+i*(60*F.n+200)) (storage : Tb = T0+i*(2*F.n+1))
    (mid : Mid F scope lc Wb Tb S i) :
    ∃ t, assignI.run S = some ⟨t,none,false⟩ ∧ OuterInv F scope L0 W0 T0 0 t (i+1) := by
  have nSmall := ok.nSmall
  have wSmall := ok.wSmall
  have spb := ok.spb
  have baseOK := ok.base
  obtain ⟨t,run,shape,frame,gl,gu,gpl,gpu,ql,qu,live⟩ := assignI_step S mid.shape (by omega)
  have fstate : t.frame.state = S.frame.state := by rw [frame]
  have liveS6 := liveS_sh6 mid.shape
  have a : t.scalars.peak ≤ F.SPB := le_cap _ _ _ _ _ gpu mid.scalarPeak
    (by rw [liveS6]; exact cap_live _ _ _ baseOK spb 3 (by omega))
  have b : t.frame.state.storage.peak ≤ F.TPB := by rw [fstate]; exact mid.storagePeak
  refine ⟨t,run,shape,⟨?_,?_,?_,?_,?_⟩,?_,?_,?_,space,?_,?_,a,b,?_⟩
  · simp [NState.vectorSlot,shape.slots,mainSlots]
  · rw [frame]; exact mid.ctx.binding
  · rw [fstate]; exact mid.ctx.graph
  · rw [frame]; exact mid.ctx.lengths
  · rw [frame]; exact mid.ctx.flag
  · rw [fstate]; exact mid.bnd
  · rw [fstate]; exact rowsOK_advance ok.nEq iw mid.rows
  · rw [fstate,mid.live,hlc]
  · have h : t.scalars.work ≤ W0+i*(60*F.n+200) :=
      Nat.le_trans gu (Nat.le_trans (Nat.add_le_add_right mid.scalarWork 4) work)
    show t.scalars.work ≤ W0+(i+1-1)*(60*F.n+200)+0
    simpa using h
  · show t.frame.state.storage.work = T0+(i+1-1)*(2*F.n+1)
    simp only [Nat.add_sub_cancel]
    rw [fstate,mid.storageWork,storage]
  · exact le_cap _ _ _ _ _ qu mid.outerPeak (Nat.add_le_add a b)

abbrev outerBody : Command :=
  .sequence
    (.scope (.sequence (.primitive reserveStmt)
      (.sequence (.scope (.sequence (.primitive declJ) (.sequence innerWhile (.primitive .skip)))) (.primitive .skip))))
    (.sequence (.primitive assignI) (.primitive .skip))

theorem iter_store (i n : Nat) (hi : 1 ≤ i) : (i-1)*(2*n+1)+1+2*n = i*(2*n+1) := by
  obtain ⟨k,rfl⟩ : ∃ k, i = k+1 := ⟨i-1,by omega⟩
  simp only [Nat.add_sub_cancel,Nat.succ_mul]
  omega

theorem iter_work (i n : Nat) (hi : 1 ≤ i) : (i-1)*(60*n+200)+60*n+25 ≤ i*(60*n+200) := by
  obtain ⟨k,rfl⟩ : ∃ k, i = k+1 := ⟨i-1,by omega⟩
  simp only [Nat.add_sub_cancel,Nat.succ_mul]
  omega

theorem outer_body (F : Fixed) (ok : FixedOK F) {scope L0 W0 T0 i : Nat} {S1 : NState}
    (hi : 1 ≤ i) (iw : i < F.w) (scopeLe : F.sc ≤ scope)
    (inv : OuterInv F scope L0 W0 T0 4 S1 i) :
    RunsTo outerBody S1 fun step => step.returned = none ∧ step.breaking = false ∧
      OuterInv F scope L0 W0 T0 0 step.state (i+1) := by
  obtain ⟨tR,tD,runR,runD,shapeR,innerInv,dwork,dstore,frameD,liveR,memR,bindR,ctxR,bndR,rwork,rstore,hRsp,hRo⟩ :=
    prepare_inner F ok (L0+F.w+1+F.n*(i+1)) rfl hi iw inv
  have loop := inner_loop F ok (LC := L0+F.w+1+F.n*(i+1)) (scope := scope+2) hi iw (by omega) (Nat.zero_le _) innerInv
  apply RunsTo.seq
  apply RunsTo.scopeSimple
  apply RunsTo.seq
  apply RunsTo.primitive runR
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.seqSkip
  apply RunsTo.scopeSimple
  apply RunsTo.seq
  apply RunsTo.primitive runD
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.seqSkip
  refine loop.mono ?_
  intro step ⟨noReturn,notBreaking,tail⟩
  refine ⟨noReturn,notBreaking,?_⟩
  obtain ⟨leave1,mid1⟩ := leave_mid1 F ok (W := 0) (T := 0) shapeR ctxR bndR (by omega) hRsp hRo
    shapeR.frameBindings tail
  obtain ⟨leave2,mid2⟩ := leave_mid2 F ok inv.shape scopeLe inv.scalarPeak inv.outerPeak mid1
  have swS1 := inv.scalarWork
  have stS1 := inv.storageWork
  have swT := tail.scalarWork
  have stT := tail.storageWork
  have arithW := iter_work i F.n hi
  have arithS := iter_store i F.n hi
  obtain ⟨t,run,final⟩ := finish_outer F ok (W0 := W0) (T0 := T0) (lc := L0+F.w+1+F.n*(i+1))
    (Wb := step.state.scalars.work+2) (Tb := step.state.frame.state.storage.work) iw rfl inv.space
    (by omega) (by omega) (by simpa using mid2)
  refine ⟨rfl,rfl,tR.left step.state,leave1,rfl,rfl,rfl,rfl,S1.left (tR.left step.state),leave2,rfl,rfl,?_⟩
  apply RunsTo.seqSkip
  exact RunsTo.primitive run ⟨rfl,rfl,rfl,rfl,final⟩

abbrev outerWhile : Command := .whileLoop outerCond outerBody

theorem outer_loop (F : Fixed) (ok : FixedOK F) {scope L0 W0 T0 i0 : Nat} {S : NState}
    (scopeLe : F.sc ≤ scope) (hi0 : 1 ≤ i0) (ile : i0 ≤ F.w) (inv : OuterInv F scope L0 W0 T0 0 S i0) :
    RunsTo outerWhile S fun step => step.returned = none ∧ step.breaking = false ∧
      OuterInv F scope L0 W0 T0 4 step.state F.w := by
  have nSmall := ok.nSmall
  have wSmall := ok.wSmall
  refine RunsTo.whileGhost (fun g t => ∃ i, g = F.w-i ∧ 1 ≤ i ∧ i ≤ F.w ∧ OuterInv F scope L0 W0 T0 0 t i) _ ?_
    F.w (F.w-i0) S (by omega) ⟨i0,rfl,hi0,ile,inv⟩
  intro g t ⟨i,hg,hi,hle,tinv⟩
  obtain ⟨ei,ew,en⟩ := Sh6.value t tinv.shape (by omega) (by omega) (by omega)
  have value : outerCond.denote (envOf t) = some (if (i : Int) < (F.w : Int) then 1 else 0) :=
    denote_lt (envOf t) 6 4 i32 i F.w ei ew
  obtain ⟨u,hu,good⟩ := scalar_eval outerCond t _ outerCond_scalar value
  have self := release_self good.1.1
  have ticked := tinv.tick F ok good
  refine ⟨u,_,hu,?_,?_⟩
  · intro zero
    have notLt : ¬ i < F.w := by
      intro h
      have : ((i : Int) < (F.w : Int)) := by omega
      simp [this] at zero
    have eq : i = F.w := by omega
    subst eq
    rw [self]
    exact ⟨rfl,rfl,ticked⟩
  · intro nonzero
    have lt : i < F.w := by
      by_cases h : i < F.w
      · exact h
      · have : ¬ ((i : Int) < (F.w : Int)) := by omega
        simp [this] at nonzero
    rw [self]
    refine (outer_body F ok hi lt scopeLe ticked).mono ?_
    intro step ⟨noReturn,notBreaking,post⟩
    exact ⟨noReturn,notBreaking,F.w-(i+1),by omega,i+1,rfl,by omega,by omega,post⟩

-- After `ret` is constructed and row 0 is assigned: locals K n W w, vectors v and ret.
structure ShRet (S : NState) (P : List Cell) (B : Nat) (K : Int) (n w : Nat) (V vsc R sc scope : Nat)
    (rw : List Bool) : Prop where
  slots : S.slots = mainSlots.take 6
  memory : S.scalars.memory = P ++ [⟨u64,K⟩,⟨i32,n⟩,⟨i32,w⟩,⟨i32,w⟩]
  bindings : S.scalars.bindings = [⟨P.length,true⟩,⟨P.length+1,false⟩,⟨P.length+2,false⟩,⟨P.length+3,false⟩]
  base : S.scalars.baseMemory = B
  scope : S.scope = scope
  frameBindings : S.frame.bindings = [vbind V vsc,rbind R sc]
  writable : S.frame.rootWritable = rw

structure RetInv (F : Fixed) (scope L0 Wr Tr : Nat) (S : NState) : Prop where
  shape : ShRet S F.P F.B F.K F.n F.w F.V F.vsc F.R F.sc scope F.rw
  ctx : Ctx S F.R F.sc F.w
  bnd : Bnd S.frame.state F.sc
  rows : RowsOK S.frame.state F.R F.n F.w F.items F.V F.vbuf 1 [] 0
  live : S.frame.state.liveSpace = L0+F.w+1+F.n
  space : L0+F.w+F.n*F.w+3 ≤ F.TPB
  scalarWork : S.scalars.work ≤ Wr
  storageWork : S.frame.state.storage.work = Tr
  scalarPeak : S.scalars.peak ≤ F.SPB
  storagePeak : S.frame.state.storage.peak ≤ F.TPB
  outerPeak : S.peak ≤ F.SPB+F.TPB

structure Done (F : Fixed) (scope L0 Wd Td : Nat) (S : NState) : Prop where
  shape : ShRet S F.P F.B F.K F.n F.w F.V F.vsc F.R F.sc scope F.rw
  ctx : Ctx S F.R F.sc F.w
  bnd : Bnd S.frame.state F.sc
  rows : RowsOK S.frame.state F.R F.n F.w F.items F.V F.vbuf F.w [] 0
  live : S.frame.state.liveSpace = L0+F.w+1+F.n*F.w
  scalarWork : S.scalars.work ≤ Wd
  storageWork : S.frame.state.storage.work = Td
  scalarPeak : S.scalars.peak ≤ F.SPB
  storagePeak : S.frame.state.storage.peak ≤ F.TPB
  outerPeak : S.peak ≤ F.SPB+F.TPB

abbrev declI1 : NStmt := .declare i32 true (.literal i32 1)

theorem declI_step (S : NState) {P B K n w V vsc R sc scope rw}
    (shape : ShRet S P B K n w V vsc R sc scope rw) :
    ∃ t, declI1.run S = some ⟨t,none,false⟩ ∧ Sh6 t P B K n w 1 V vsc R sc scope rw ∧
      t.frame = S.frame ∧ S.scalars.work ≤ t.scalars.work ∧ t.scalars.work ≤ S.scalars.work+2 ∧
      S.scalars.peak ≤ t.scalars.peak ∧ t.scalars.peak ≤ max S.scalars.peak (liveS S+2) ∧
      S.peak ≤ t.peak ∧ t.peak ≤ max S.peak (t.scalars.peak+t.frame.state.storage.peak) := by
  have valid : i32.valid (1 : Int) = true := by simp [Ty.valid]
  obtain ⟨t,run,frame,sl,sc',me,bi,ba,gl,gu,gpl,gpu,ql,qu⟩ := declare_good (.literal i32 1) i32 true S 1 1
    (by simp [NExpr.scalarOnly]) (by simp [NExpr.denote,valid]) (Ty.convert_of_valid _ _ valid)
  have memLength : S.scalars.memory.length = P.length+4 := by simp [shape.memory]
  have bindLength : S.scalars.bindings.length = 4 := by simp [shape.bindings]
  refine ⟨t,run,⟨?_,?_,?_,?_,?_,?_,?_⟩,frame,gl,?_,gpl,?_,ql,qu⟩
  · rw [sl,bindLength,shape.slots]; simp [mainSlots]
  · rw [me,shape.memory]; simp
  · rw [bi,memLength,shape.bindings]; simp
  · rw [ba]; exact shape.base
  · rw [sc']; exact shape.scope
  · rw [frame]; exact shape.frameBindings
  · rw [frame]; exact shape.writable
  · simpa [NExpr.nodes] using gu
  · simpa [NExpr.nodes] using gpu

theorem liveS_shRet {S : NState} {P B K n w V vsc R sc scope rw}
    (shape : ShRet S P B K n w V vsc R sc scope rw) : liveS S = P.length+4-B+4 := by
  obtain ⟨_,memory,bindings,base,_,_,_⟩ := shape
  simp [liveS,memory,bindings,base]

theorem take_cells4 (P : List Cell) (a b c d e : Cell) :
    (P ++ [a,b,c,d,e]).take (P.length+4) = P ++ [a,b,c,d] := by
  have h : P.take (P.length+4) = P := List.take_of_length_le (by omega)
  simp [List.take_append,h]

abbrev loopsPhase : Command :=
  .scope (.sequence (.primitive declI1) (.sequence outerWhile (.primitive .skip)))

theorem loops_phase (F : Fixed) (ok : FixedOK F) {scope L0 Wr Tr : Nat} (scopeLe : F.sc ≤ scope)
    (hw : 1 ≤ F.w) {S : NState} (inv : RetInv F scope L0 Wr Tr S) :
    RunsTo loopsPhase S fun step => step.returned = none ∧ step.breaking = false ∧
      Done F scope L0 (Wr+2+(F.w-1)*(60*F.n+200)+5) (Tr+(F.w-1)*(2*F.n+1)) step.state := by
  have spb := ok.spb
  have baseOK := ok.base
  have shape2 : ShRet {S with scope := S.scope+1} F.P F.B F.K F.n F.w F.V F.vsc F.R F.sc (scope+1) F.rw :=
    ⟨inv.shape.slots,inv.shape.memory,inv.shape.bindings,inv.shape.base,by simp [inv.shape.scope],
      inv.shape.frameBindings,inv.shape.writable⟩
  obtain ⟨tI,runI,shapeI,frameI,wl,wu,pl,pu,ql,qu⟩ := declI_step {S with scope := S.scope+1} shape2
  have liveS0 : liveS S = F.P.length+4-F.B+4 := liveS_shRet inv.shape
  have fstate : tI.frame.state = S.frame.state := by rw [frameI]
  have sp1 : tI.scalars.peak ≤ F.SPB := le_cap _ _ _ _ _ pu inv.scalarPeak
    (by
      have : liveS ({S with scope := S.scope+1} : NState) = F.P.length+4-F.B+4 := liveS0
      rw [this]; omega)
  have outerI : OuterInv F (scope+1) L0 tI.scalars.work tI.frame.state.storage.work 0 tI 1 := by
    refine ⟨shapeI,⟨?_,?_,?_,?_,?_⟩,?_,?_,?_,inv.space,?_,?_,sp1,?_,?_⟩
    · simp [NState.vectorSlot,shapeI.slots,mainSlots]
    · rw [frameI]; exact inv.ctx.binding
    · rw [fstate]; exact inv.ctx.graph
    · rw [frameI]; exact inv.ctx.lengths
    · rw [frameI]; exact inv.ctx.flag
    · rw [fstate]; exact inv.bnd
    · rw [fstate]; exact inv.rows
    · rw [fstate,inv.live]; simp
    · simp
    · simp
    · rw [fstate]; exact inv.storagePeak
    · have a : tI.frame.state.storage.peak ≤ F.TPB := by rw [fstate]; exact inv.storagePeak
      exact le_cap _ _ _ _ _ qu inv.outerPeak (Nat.add_le_add sp1 a)
  have loop := outer_loop F ok (scope := scope+1) (by omega) (Nat.le_refl 1) hw outerI
  apply RunsTo.scopeSimple
  apply RunsTo.seq
  apply RunsTo.primitive runI
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.seqSkip
  refine loop.mono ?_
  intro step ⟨noReturn,notBreaking,tail⟩
  refine ⟨noReturn,notBreaking,?_⟩
  have take : step.state.scalars.memory.take S.scalars.memory.length = S.scalars.memory := by
    rw [tail.shape.memory,inv.shape.memory]
    have : (F.P ++ [⟨u64,F.K⟩,⟨i32,F.n⟩,⟨i32,F.w⟩,⟨i32,F.w⟩] : List Cell).length = F.P.length+4 := by simp
    rw [this]
    exact take_cells4 _ _ _ _ _ _
  have fits : S.scalars.memory.length ≤ step.state.scalars.memory.length := by
    rw [tail.shape.memory,inv.shape.memory]; simp
  have lengthTake : (step.state.scalars.memory.take S.scalars.memory.length).length = S.scalars.memory.length := by
    rw [take]
  have leaveEq : S.leave step.state none = some (S.left step.state) :=
    leave_scalar S step.state none (by simp) fits (by rw [take]) tail.ctx.graph.valid
      (by rw [inv.shape.scope]; exact tail.bnd.fresh scopeLe)
  have same := noopRetired_same step.state.frame
  have sameBind : step.state.frame.bindings = S.frame.bindings := by
    rw [tail.shape.frameBindings,inv.shape.frameBindings]
  have e : S.scalars.memory.length-S.scalars.baseMemory+S.scalars.bindings.length+0 ≤ F.SPB := by
    have := liveS_shRet inv.shape; unfold liveS at this; rw [this]; omega
  have hs : (S.left step.state).scalars.peak ≤ F.SPB := by
    rw [left_scalar_peak,lengthTake]; exact mid_scalar _ _ _ _ inv.scalarPeak tail.scalarPeak e
  have ht : (noopRetired step.state.frame).state.storage.peak ≤ F.TPB := by
    show max step.state.frame.state.storage.peak
      (step.state.frame.state.liveSpace-step.state.frame.state.storage.baseSpace) ≤ F.TPB
    rw [tail.live]
    exact mid_storage _ _ _ _ tail.storagePeak (by have := tail.space; omega)
  have swS := inv.scalarWork
  have sw1 := tail.scalarWork
  have stT := tail.storageWork
  have stS := inv.storageWork
  have stI : tI.frame.state.storage.work = Tr := by rw [fstate]; exact stS
  have wu' : tI.scalars.work ≤ S.scalars.work+2 := wu
  refine ⟨rfl,rfl,S.left step.state,leaveEq,rfl,rfl,?_⟩
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,⟨?_,?_,?_,?_,?_⟩,same.bnd tail.bnd,?_,?_,?_,?_,hs,ht,?_⟩
  · simpa using inv.shape.slots
  · rw [left_memory,take]; exact inv.shape.memory
  · rw [left_bindings]; exact inv.shape.bindings
  · rw [left_baseMemory]; exact inv.shape.base
  · rw [left_scope]; exact inv.shape.scope
  · rw [left_frameBindings,sameBind]; simpa using inv.shape.frameBindings
  · rw [left_rootWritable]; exact tail.shape.writable
  · simp [NState.vectorSlot,inv.shape.slots,mainSlots]
  · rw [left_frameBindings,sameBind,inv.shape.frameBindings]; simp [rbind]
  · rw [left_state]; exact same.rootGraph tail.ctx.graph
  · rw [left_rootWritable,left_state]; exact tail.ctx.lengths
  · rw [left_rootWritable]; exact tail.ctx.flag
  · rw [left_state]; simpa using same.rows tail.rows
  · rw [left_state,same.liveSpace]; exact tail.live
  · rw [left_work]; omega
  · rw [left_state]; show step.state.frame.state.storage.work = _; omega
  · rw [left_peak]; exact mid_peak _ _ _ _ _ _ inv.outerPeak tail.outerPeak hs ht

end Proofs.DoublingNested
