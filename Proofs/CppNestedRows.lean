import Proofs.CppNestedEval

namespace Proofs.CppNestedRows
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedConstruct
open Proofs.CppNestedFacts

-- A constructed vector of integer vectors: one root whose buffer lists its
-- `w` rows, row `k` having owner `R+1+k`. The forest facts never change.
structure RootGraph (T : State) (R : Nat) (ty : Ty) (w sc : Nat) : Prop where
  valid : T.wellFormed = true
  tag : T.forest.lookup R = some (rootTag ty sc R w)
  buffer : ∃ buffer, T.storage.lookup R = some buffer ∧ buffer.epoch = 0 ∧
    buffer.items = (rowIds R w).map Value.child

theorem rowIds_get (R w k : Nat) (inside : k < w) : (rowIds R w)[k]? = some (R+1+k) := by
  simp [rowIds,List.getElem?_map,List.getElem?_range,inside]

theorem root_object (f : Frame) (R : Nat) (ty : Ty) (w sc : Nat) (g : RootGraph f.state R ty w sc) :
    ∃ buffer, f.object R (.vector (.integer ty)) = some (buffer,rootTag ty sc R w) ∧
      f.state.storage.lookup R = some buffer ∧ buffer.epoch = 0 ∧
      buffer.items = (rowIds R w).map Value.child := by
  obtain ⟨buffer,found,epoch,items⟩ := g.buffer
  exact ⟨buffer,object_runs f R _ buffer _ g.valid found g.tag rfl,found,epoch,items⟩

theorem row_object (f : Frame) (R : Nat) (ty : Ty) (w sc k : Nat) (g : RootGraph f.state R ty w sc)
    (inside : k < w) :
    ∃ buffer, f.object (R+1+k) (.integer ty) = some (buffer,⟨.integer ty,some R,none,[]⟩) ∧
      f.state.storage.lookup (R+1+k) = some buffer := by
  obtain ⟨root,rootObject,rootFound,_,items⟩ := root_object f R ty w sc g
  have facts := rows_facts f.state R (rootTag ty sc R w) root ty g.valid g.tag rootFound rfl
  obtain ⟨childBuffer,tagFound,_,found⟩ :=
    facts.2.2.2 (R+1+k) ((mem_rowIds R w (R+1+k)).mpr ⟨k,inside,rfl⟩)
  exact ⟨childBuffer,object_runs f (R+1+k) _ childBuffer _ g.valid found tagFound rfl,found⟩

theorem row_tag (f : Frame) (R : Nat) (ty : Ty) (w sc k : Nat) (g : RootGraph f.state R ty w sc)
    (inside : k < w) : f.state.forest.lookup (R+1+k) = some ⟨.integer ty,some R,none,[]⟩ := by
  obtain ⟨root,_,rootFound,_,_⟩ := root_object f R ty w sc g
  have facts := rows_facts f.state R (rootTag ty sc R w) root ty g.valid g.tag rootFound rfl
  obtain ⟨childBuffer,tagFound,_,_⟩ := facts.2.2.2 (R+1+k) ((mem_rowIds R w (R+1+k)).mpr ⟨k,inside,rfl⟩)
  exact tagFound

def rowBinding (R : Nat) (ty : Ty) (k : Nat) : Binding :=
  ⟨R+1+k,.integer ty,true,.child ⟨R,0,k⟩⟩

-- Root permission: rows inherit the root's maximum permission.
theorem maximum_root (f : Frame) (R : Nat) (ty : Ty) (w sc : Nat) (g : RootGraph f.state R ty w sc)
    (lengths : f.rootWritable.length = f.state.forest.objects.length)
    (flag : f.rootWritable[R]? = some true) : f.maximum R = some true := by
  exact maximum_runs f R R true lengths (CppVectorOwnership.root_runs f.state.forest R _ g.tag rfl) flag

theorem maximum_row (f : Frame) (R : Nat) (ty : Ty) (w sc k : Nat) (g : RootGraph f.state R ty w sc)
    (lengths : f.rootWritable.length = f.state.forest.objects.length)
    (flag : f.rootWritable[R]? = some true) (inside : k < w) : f.maximum (R+1+k) = some true := by
  obtain ⟨root,_,rootFound,_,items⟩ := root_object f R ty w sc g
  have facts := rows_facts f.state R (rootTag ty sc R w) root ty g.valid g.tag rootFound rfl
  obtain ⟨childBuffer,tagFound,_,_⟩ := facts.2.2.2 (R+1+k) ((mem_rowIds R w (R+1+k)).mpr ⟨k,inside,rfl⟩)
  have rooted : f.state.forest.rootOwner (R+1+k) = some R := by
    rw [CppVectorOwnership.child_runs f.state.forest (R+1+k) R ⟨.integer ty,some R,none,[]⟩ tagFound rfl (by omega)]
    exact CppVectorOwnership.root_runs f.state.forest R _ g.tag rfl
  exact maximum_runs f (R+1+k) R true lengths rooted flag

theorem child_row (f : Frame) (rb R : Nat) (ty : Ty) (w sc k : Nat) (g : RootGraph f.state R ty w sc)
    (binding : f.bindings[rb]? = some ⟨R,.vector (.integer ty),true,.root sc⟩)
    (lengths : f.rootWritable.length = f.state.forest.objects.length)
    (flag : f.rootWritable[R]? = some true) (inside : k < w) :
    f.child rb (.integer ty) k = some (f.addBinding (rowBinding R ty k)) := by
  obtain ⟨root,rootObject,rootFound,epoch,items⟩ := root_object f R ty w sc g
  have resolved : f.resolve rb (.vector (.integer ty)) = some (⟨R,.vector (.integer ty),true,.root sc⟩,root) :=
    resolve_root f rb _ _ sc root (rootTag ty sc R w) true binding rfl rfl rootObject rfl rfl
      (maximum_root f R ty w sc g lengths flag) (fun _ => rfl)
  have facts := rows_facts f.state R (rootTag ty sc R w) root ty g.valid g.tag rootFound rfl
  have sizeOK : (k : Int).toNat < root.items.length := by
    simp [items,rowIds_length]; exact inside
  have address : CppVector.elementRef root (accepts (.vector (.integer ty))) k =
      some ⟨R,0,k⟩ := by
    have valid : root.Valid (accepts (.vector (.integer ty))) := by simpa [rootTag] using facts.2.1
    have := CppVector.elementRef_runs root (accepts (.vector (.integer ty))) k valid (by omega) sizeOK
    simpa [facts.1,epoch] using this
  have lookup : root.items[k]? = some (Value.child (R+1+k)) := by
    simp [items,List.getElem?_map,rowIds_get R w k inside]
  have read : readRef root (accepts (.vector (.integer ty))) ⟨R,0,k⟩ =
      some ⟨root,Value.child (R+1+k),1,root.capacity+2⟩ := by
    have valid : root.Valid (accepts (.vector (.integer ty))) := by simpa [rootTag] using facts.2.1
    have := CppVector.readRef_runs root (accepts (.vector (.integer ty))) k _ valid lookup
    simpa [facts.1,epoch] using this
  obtain ⟨rowBuffer,rowObject,_⟩ := row_object f R ty w sc k g inside
  exact child_runs f rb (.integer ty) k _ root ⟨R,0,k⟩ _ (R+1+k) rowBuffer _ resolved address read rfl rowObject rfl

theorem resolve_row (f : Frame) (cb R : Nat) (ty : Ty) (w sc k : Nat) (g : RootGraph f.state R ty w sc)
    (binding : f.bindings[cb]? = some (rowBinding R ty k))
    (lengths : f.rootWritable.length = f.state.forest.objects.length)
    (flag : f.rootWritable[R]? = some true) (inside : k < w) :
    ∃ buffer, f.resolve cb (.integer ty) = some (rowBinding R ty k,buffer) ∧
      f.state.storage.lookup (R+1+k) = some buffer := by
  obtain ⟨root,rootObject,rootFound,epoch,items⟩ := root_object f R ty w sc g
  have facts := rows_facts f.state R (rootTag ty sc R w) root ty g.valid g.tag rootFound rfl
  have valid : root.Valid (accepts (.vector (.integer ty))) := by simpa [rootTag] using facts.2.1
  have lookup : root.items[k]? = some (Value.child (R+1+k)) := by
    simp [items,List.getElem?_map,rowIds_get R w k inside]
  have read : readRef root (accepts (.vector (.integer ty))) ⟨R,0,k⟩ =
      some ⟨root,Value.child (R+1+k),1,root.capacity+2⟩ := by
    have := CppVector.readRef_runs root (accepts (.vector (.integer ty))) k _ valid lookup
    simpa [facts.1,epoch] using this
  obtain ⟨rowBuffer,rowObject,found⟩ := row_object f R ty w sc k g inside
  refine ⟨rowBuffer,?_,found⟩
  exact resolve_child f cb (.integer ty) (rowBinding R ty k) ⟨R,0,k⟩ root (rootTag ty sc R w) _
    (R+1+k) rowBuffer _ true binding rfl rfl rfl rootObject read rfl rowObject
    (maximum_row f R ty w sc k g lengths flag inside) (fun _ => rfl)

-- Generic committed integer-buffer operations (any integer vector binding).
theorem buffer_facts (f : Frame) (owner : Nat) (ty : Ty) (buffer : Buffer Value) (tag : Tag)
    (object : f.object owner (.integer ty) = some (buffer,tag)) :
    f.state.wellFormed = true ∧ buffer.owner = owner ∧ buffer.Valid (accepts (.integer ty)) ∧
      f.state.forest.lookup owner = some tag ∧ tag.element = .integer ty := by
  obtain ⟨valid,found,tagFound,element⟩ := object_buffer f owner _ buffer tag object
  obtain ⟨stored,foundAgain,owns,payload⟩ := wellFormed_pair f.state owner tag valid tagFound
  have same : stored = buffer := by
    rw [found] at foundAgain
    exact (Option.some.inj foundAgain).symm
  subst same
  refine ⟨valid,owns,?_,tagFound,element⟩
  have h := payload.1
  rwa [element] at h

theorem append_ok (f : Frame) (slot : Nat) (ty : Ty) (x : Int) (binding : Binding) (buffer : Buffer Value)
    (tag : Tag) (resolved : f.resolve slot (.integer ty) = some (binding,buffer))
    (writable : binding.writable = true) (object : f.object binding.owner (.integer ty) = some (buffer,tag))
    (accepted : ty.valid x = true) (room : buffer.items.length < buffer.capacity) :
    f.append slot ty x = some (f.updated binding.owner buffer
      ⟨{buffer with items := buffer.items ++ [Value.integer x]},(),2,buffer.capacity+2⟩) := by
  obtain ⟨valid,owns,bufferValid,tagFound,element⟩ := buffer_facts f binding.owner ty buffer tag object
  obtain ⟨_,found,_,_⟩ := object_buffer f binding.owner _ buffer tag object
  have appended : CppVector.appendReserved buffer (accepts (.integer ty)) binding.writable (.integer x) =
      some ⟨{buffer with items := buffer.items ++ [Value.integer x]},(),2,buffer.capacity+2⟩ := by
    rw [writable]
    exact CppVector.append_runs buffer _ _ bufferValid (by simpa [accepts] using accepted) room
  rw [CppNestedOps.append_runs f slot ty x binding buffer _ resolved appended]
  have newValid := CppVector.append_preserves_valid buffer (accepts (.integer ty)) (.integer x) bufferValid
    (by simpa [accepts] using accepted) room
  exact commit_runs f binding.owner (.integer ty) buffer tag _ valid object tagFound found
    (by simpa using owns) (by simp [payloadOK,element,newValid])
    (by simp) (by simp)

theorem read_ok (f : Frame) (slot : Nat) (ty : Ty) (index : Nat) (x : Int) (binding : Binding)
    (buffer : Buffer Value) (tag : Tag) (maximum : Bool)
    (found : f.bindings[slot]? = some binding) (bindingElement : binding.element = .integer ty)
    (resolved : f.resolve slot (.integer ty) = some (binding,buffer))
    (object : f.object binding.owner (.integer ty) = some (buffer,tag))
    (max : f.maximum binding.owner = some maximum) (permission : binding.writable = true → maximum = true)
    (item : buffer.items[index]? = some (Value.integer x)) :
    ∃ reference, f.elementRef slot ty index = some reference ∧ f.read reference = some x := by
  obtain ⟨valid,owns,bufferValid,tagFound,element⟩ := buffer_facts f binding.owner ty buffer tag object
  have inside : index < buffer.items.length := (List.getElem?_eq_some_iff.mp item).1
  have captured : CppVector.elementRef buffer (accepts (.integer ty)) index =
      some ⟨buffer.owner,buffer.epoch,index⟩ := by
    have := CppVector.elementRef_runs buffer (accepts (.integer ty)) index bufferValid (by omega)
      (by simpa using inside)
    simpa using this
  have reference : f.elementRef slot ty index =
      some ⟨slot,ty,binding.writable,⟨buffer.owner,buffer.epoch,index⟩⟩ := by
    simp [Frame.elementRef,resolved,captured]
  refine ⟨_,reference,?_⟩
  have grant := grant_runs f ⟨slot,ty,binding.writable,⟨buffer.owner,buffer.epoch,index⟩⟩ binding found
    (by simp [owns]) (by simpa using bindingElement) (fun h => h) maximum max permission
  have read := CppVector.readRef_runs buffer (accepts (.integer ty)) index (Value.integer x) bufferValid item
  have object' : f.object buffer.owner (.integer ty) = some (buffer,tag) := by rw [owns]; exact object
  exact read_runs f _ binding buffer tag _ x grant object' (by simpa using read) rfl

theorem reserve_grow_ok (f : Frame) (slot : Nat) (ty : Ty) (requested : Nat) (binding : Binding)
    (buffer : Buffer Value) (tag : Tag) (resolved : f.resolve slot (.integer ty) = some (binding,buffer))
    (writable : binding.writable = true) (object : f.object binding.owner (.integer ty) = some (buffer,tag))
    (limit : requested ≤ buffer.limit) (grow : buffer.capacity < requested) :
    f.reserve slot (.integer ty) requested = some (f.updated binding.owner buffer
      ⟨{buffer with capacity := requested,epoch := buffer.epoch+1},(),buffer.items.length+1,
        buffer.capacity+requested+2⟩) := by
  obtain ⟨valid,owns,bufferValid,tagFound,element⟩ := buffer_facts f binding.owner ty buffer tag object
  obtain ⟨_,found,_,_⟩ := object_buffer f binding.owner _ buffer tag object
  have reserved : CppVector.reserve buffer (accepts (.integer ty)) binding.writable requested =
      some ⟨{buffer with capacity := requested,epoch := buffer.epoch+1},(),buffer.items.length+1,
        buffer.capacity+requested+2⟩ := by
    rw [writable]
    exact CppVector.reserve_grow buffer _ requested bufferValid limit grow
  rw [CppNestedVectorBindings.reserve_runs f slot (.integer ty) requested binding buffer _ resolved reserved]
  have newValid := CppVector.reserve_preserves_valid buffer (accepts (.integer ty)) requested bufferValid limit grow
  exact commit_runs f binding.owner (.integer ty) buffer tag _ valid object tagFound found
    (by simpa using owns) (by simp [payloadOK,element,newValid]) (by simp <;> omega) (by simp <;> omega)

theorem reserve_keep_ok (f : Frame) (slot : Nat) (ty : Ty) (requested : Nat) (binding : Binding)
    (buffer : Buffer Value) (tag : Tag) (resolved : f.resolve slot (.integer ty) = some (binding,buffer))
    (writable : binding.writable = true) (object : f.object binding.owner (.integer ty) = some (buffer,tag))
    (fits : requested ≤ buffer.capacity) :
    f.reserve slot (.integer ty) requested = some (f.updated binding.owner buffer
      ⟨buffer,(),1,buffer.capacity+1⟩) := by
  obtain ⟨valid,owns,bufferValid,tagFound,element⟩ := buffer_facts f binding.owner ty buffer tag object
  obtain ⟨_,found,_,_⟩ := object_buffer f binding.owner _ buffer tag object
  have reserved : CppVector.reserve buffer (accepts (.integer ty)) binding.writable requested =
      some ⟨buffer,(),1,buffer.capacity+1⟩ := by
    rw [writable]
    exact CppVector.reserve_keep buffer _ requested bufferValid fits
  rw [CppNestedVectorBindings.reserve_runs f slot (.integer ty) requested binding buffer _ resolved reserved]
  exact commit_runs f binding.owner (.integer ty) buffer tag _ valid object tagFound found
    (by simpa using owns) (by simp [payloadOK,element,bufferValid]) (by simp) (by simp)

theorem assign_ok (f : Frame) (target source : Nat) (ty : Ty) (range : CppVectorRange.IteratorRange)
    (first last : Nat) (destination origin : Binding) (targetBuffer sourceBuffer : Buffer Value) (tag : Tag)
    (resolvedTarget : f.resolve target (.integer ty) = some (destination,targetBuffer))
    (resolvedSource : f.resolve source (.integer ty) = some (origin,sourceBuffer))
    (writable : destination.writable = true)
    (targetObject : f.object destination.owner (.integer ty) = some (targetBuffer,tag))
    (sourceObject : ∃ sourceTag, f.object origin.owner (.integer ty) = some (sourceBuffer,sourceTag))
    (distinct : targetBuffer.owner ≠ sourceBuffer.owner)
    (rangeShape : range = ⟨sourceBuffer.owner,sourceBuffer.epoch,first,last⟩)
    (ownerSame : sourceBuffer.owner = origin.owner)
    (ordered : first ≤ last) (bounded : last ≤ sourceBuffer.items.length)
    (limit : last-first ≤ targetBuffer.limit) :
    f.assign target source ty range = some (f.updated destination.owner targetBuffer
      (CppVectorRange.assignResult targetBuffer sourceBuffer first last)) := by
  obtain ⟨valid,owns,targetValid,tagFound,element⟩ :=
    buffer_facts f destination.owner ty targetBuffer tag targetObject
  obtain ⟨sourceTag,sourceObject⟩ := sourceObject
  obtain ⟨_,_,sourceValid,_,_⟩ := buffer_facts f origin.owner ty sourceBuffer sourceTag sourceObject
  obtain ⟨_,found,_,_⟩ := object_buffer f destination.owner _ targetBuffer tag targetObject
  have assigned : CppVectorRange.assignRange targetBuffer sourceBuffer (accepts (.integer ty))
      destination.writable range = some (CppVectorRange.assignResult targetBuffer sourceBuffer first last) := by
    rw [writable,rangeShape]
    exact CppVectorRange.assignRange_runs targetBuffer sourceBuffer _ first last targetValid sourceValid
      distinct ordered bounded limit
  rw [CppNestedOps.assign_runs f target source ty range destination origin targetBuffer sourceBuffer _
    resolvedTarget resolvedSource (by rw [rangeShape]; exact ownerSame) assigned]
  have newValid := CppVectorRange.assign_preserves_valid targetBuffer sourceBuffer (accepts (.integer ty))
    first last targetValid sourceValid ordered bounded limit
  exact commit_runs f destination.owner (.integer ty) targetBuffer tag _ valid targetObject tagFound found
    (by simpa [CppVectorRange.assign_owner] using owns) (by simp [payloadOK,element]; exact newValid)
    (by simp [CppVectorRange.assignResult]; split <;> omega)
    (by simp [CppVectorRange.assignResult]; split <;> omega)

theorem iterator_whole (f : Frame) (slot : Nat) (ty : Ty) (binding : Binding) (buffer : Buffer Value)
    (resolved : f.resolve slot (.integer ty) = some (binding,buffer))
    (valid : buffer.Valid (accepts (.integer ty))) :
    f.iteratorRange slot slot ty false true =
      some ⟨buffer.owner,buffer.epoch,0,buffer.items.length⟩ := by
  have range := CppVectorRange.rangeBetween_runs buffer (accepts (.integer ty)) 0 (buffer.items.length : Int)
    valid (by omega) (by omega) (by simp)
  simp [Frame.iteratorRange,resolved]
  simpa using range

-- A caller root vector `v` bound in the frame.
theorem resolve_vroot (f : Frame) (vb V vsc : Nat) (ty : Ty) (wV maximum : Bool) (vBuffer : Buffer Value)
    (vbinding : f.bindings[vb]? = some ⟨V,.integer ty,wV,.root vsc⟩) (valid : f.state.wellFormed = true)
    (vtag : f.state.forest.lookup V = some ⟨.integer ty,none,some vsc,[]⟩)
    (vfound : f.state.storage.lookup V = some vBuffer)
    (lengths : f.rootWritable.length = f.state.forest.objects.length)
    (vflag : f.rootWritable[V]? = some maximum) (vpermission : wV = true → maximum = true) :
    f.resolve vb (.integer ty) = some (⟨V,.integer ty,wV,.root vsc⟩,vBuffer) ∧
      f.object V (.integer ty) = some (vBuffer,⟨.integer ty,none,some vsc,[]⟩) ∧
      f.maximum V = some maximum := by
  have vobject : f.object V (.integer ty) = some (vBuffer,⟨.integer ty,none,some vsc,[]⟩) :=
    object_runs f V _ vBuffer _ valid vfound vtag rfl
  have vrooted : f.state.forest.rootOwner V = some V := CppVectorOwnership.root_runs _ V _ vtag rfl
  have vmax : f.maximum V = some maximum := maximum_runs f V V maximum lengths vrooted vflag
  exact ⟨resolve_root f vb _ _ vsc vBuffer _ maximum vbinding rfl rfl vobject rfl rfl vmax vpermission,
    vobject,vmax⟩

-- Replacing a row buffer by another valid buffer keeps the whole state well formed.
theorem row_update_valid (f : Frame) (R : Nat) (ty : Ty) (w sc k : Nat) (g : RootGraph f.state R ty w sc)
    (inside : k < w) (old newBuffer : Buffer Value) (result : Result Value Unit)
    (found : f.state.storage.lookup (R+1+k) = some old) (resultBuffer : result.buffer = newBuffer)
    (owns : newBuffer.owner = R+1+k) (valid : newBuffer.Valid (accepts (.integer ty))) :
    (f.updated (R+1+k) old result).state.wellFormed = true := by
  obtain ⟨stored,object,foundAgain⟩ := row_object f R ty w sc k g inside
  have sameBuffer : stored = old := by
    rw [found] at foundAgain
    exact (Option.some.inj foundAgain).symm
  subst sameBuffer
  obtain ⟨_,_,_,tagFound,element⟩ := buffer_facts f (R+1+k) ty stored _ object
  have bound := CppVectorStore.lookup_bound f.state.storage (R+1+k) stored found
  have payload : payloadOK ⟨.integer ty,some R,none,[]⟩ result.buffer := by
    rw [resultBuffer]
    simp [payloadOK,valid]
  exact updated_wellFormed f (R+1+k) stored _ result g.valid tagFound bound (by rw [resultBuffer]; exact owns) payload

theorem rootGraph_updated (f : Frame) (R : Nat) (ty : Ty) (w sc : Nat) (g : RootGraph f.state R ty w sc)
    (owner : Nat) (old : Buffer Value) (result : Result Value Unit) (different : owner ≠ R)
    (valid : (f.updated owner old result).state.wellFormed = true) :
    RootGraph (f.updated owner old result).state R ty w sc := by
  obtain ⟨buffer,found,epoch,items⟩ := g.buffer
  refine ⟨valid,g.tag,buffer,?_,epoch,items⟩
  rw [CppNestedOps.updated_lookup_other f owner R old result different]
  exact found

theorem sum_update (f g : Nat → Nat) (L m : Nat) (inside : m < L) (same : ∀ i, i ≠ m → g i = f i) :
    ((List.range L).map g).sum + f m = ((List.range L).map f).sum + g m := by
  induction L with
  | zero => omega
  | succ L ih =>
    rw [List.range_succ]
    simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    by_cases earlier : m < L
    · have := ih earlier
      have h := same L (by omega)
      omega
    · have equal : m = L := by omega
      subst equal
      have sums : ((List.range m).map g).sum = ((List.range m).map f).sum := by
        congr 1
        apply List.map_congr_left
        intro i member
        exact same i (by have := List.mem_range.mp member; omega)
      omega

-- Replacing one buffer changes the abstract live space by that node's footprint difference.
theorem liveSpace_update (T T' : State) (owner : Nat) (inside : owner < T.storage.objects.length)
    (lengths : T'.storage.objects.length = T.storage.objects.length) (forest : T'.forest = T.forest)
    (other : ∀ o, o ≠ owner → T'.storage.lookup o = T.storage.lookup o) :
    T'.liveSpace + T.nodeSpace owner = T.liveSpace + T'.nodeSpace owner := by
  unfold State.liveSpace
  rw [lengths]
  apply sum_update _ _ _ owner inside
  intro o different
  simp [State.nodeSpace,forest,other o different]

theorem nodeSpace_row (T : State) (ty : Ty) (R k : Nat) (buffer : Buffer Value)
    (tag : T.forest.lookup (R+1+k) = some ⟨.integer ty,some R,none,[]⟩)
    (found : T.storage.lookup (R+1+k) = some buffer) : T.nodeSpace (R+1+k) = buffer.capacity := by
  simp [State.nodeSpace,tag,found]

end Proofs.CppNestedRows
