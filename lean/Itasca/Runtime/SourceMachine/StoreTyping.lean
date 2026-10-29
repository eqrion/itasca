import Itasca.Runtime.SourceMachine.Core.Typing
import Itasca.Runtime.Spec.Typing.HostTyping

/-! Bridges from the source machine's component certificates to the generated
instance/store judgments. Export conditions are explicit source metadata. -/
namespace Itasca.Runtime.Abs

/-- The external namespace used by the generated module-instance judgment. -/
def moduleAddresses (m : moduleinst) : List externaddr :=
  m.GLOBALS.map externaddr.GLOBAL ++ (m.MEMS.map externaddr.MEM ++
    (m.TABLES.map externaddr.TABLE ++ m.FUNCS.map externaddr.FUNC))

private theorem paired_left {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (paired : List.Forall₂ R xs ys) {x : α} (member : x ∈ xs) : ∃ y, R x y := by
  obtain ⟨index, bound, rfl⟩ := List.mem_iff_getElem.mp member
  have other : index < ys.length := by rw [← paired.length_eq]; exact bound
  exact ⟨ys[index], paired.get bound other⟩

theorem externaddr_type_wf {s : store} {address : externaddr} {ty : externtype}
    (typed : Externaddr_ok s address ty) : wf_externtype ty := by
  cases typed <;> assumption

private theorem disjoint_of_nodup {α : Type} [BEq α] [LawfulBEq α]
    {xs : List α} (distinct : xs.Nodup) : disjoint_ α xs = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.nodup_cons] at distinct
    simp [disjoint_, distinct.1, ih distinct.2]

/-- Every module address denotes a source external with a type. -/
theorem ModuleBindings.address_typed {s : store} {m : moduleinst} {C : context}
    (bindings : ModuleBindings s m C) (storeWf : wf_store s)
    {address : externaddr} (member : address ∈ moduleAddresses m) :
    ∃ ty, Externaddr_ok s address ty := by
  simp only [moduleAddresses, List.mem_append, List.mem_map] at member
  rcases member with ⟨a, present, rfl⟩ | ⟨a, present, rfl⟩ | ⟨a, present, rfl⟩ | ⟨a, present, rfl⟩
  · obtain ⟨ty, typed⟩ := paired_left bindings.globals present
    exact ⟨.GLOBAL ty, typed⟩
  · obtain ⟨ty, typed⟩ := paired_left bindings.mems present
    exact ⟨.MEM ty, typed⟩
  · obtain ⟨ty, typed⟩ := paired_left bindings.tables present
    exact ⟨.TABLE ty, typed⟩
  · obtain ⟨ty, fn, found, same⟩ := paired_left bindings.funcs present
    refine ⟨.FUNC ty, ?_⟩
    rw [← same]
    exact .func s a fn (List.getElem?_eq_some_iff.mp found).1
      (by simp [List.getElem!_eq_getElem?_getD, found]) storeWf (.externtype_case_0 _)

/-- Export typing follows from module membership and the actual bindings. -/
theorem ModuleBindings.exports_typed {s : store} {m : moduleinst} {C : context}
    (bindings : ModuleBindings s m C) (storeWf : wf_store s) (moduleWf : wf_moduleinst m)
    (members : ∀ entry ∈ m.EXPORTS, entry.ADDR ∈ moduleAddresses m) :
    Forall (Exportinst_ok s) m.EXPORTS := by
  have sourceSyntax : Forall wf_exportinst m.EXPORTS := by cases moduleWf; assumption
  intro entry member
  obtain ⟨ty, typed⟩ := bindings.address_typed storeWf (members entry member)
  cases entry with
  | MKexportinst exportName address =>
    exact .mk_Exportinst_ok s exportName address ty typed storeWf (externaddr_type_wf typed) (sourceSyntax _ member)

/-- A module's checked address maps plus its export metadata recover the full
source judgment, including modules with no exports or external namespace. -/
theorem ModuleBindings.moduleinst_ok {s : store} {m : moduleinst} {C : context}
    (bindings : ModuleBindings s m C) (storeWf : wf_store s) (moduleWf : wf_moduleinst m)
    (locals : C.LOCALS = []) (labels : C.LABELS = []) (result : C.RETURN = none)
    (distinct : (m.EXPORTS.map exportinst.NAME).Nodup)
    (members : ∀ entry ∈ m.EXPORTS, entry.ADDR ∈ moduleAddresses m) :
    Moduleinst_ok s m C := by
  cases m with
  | MKmoduleinst types funcs globals tables mems elems datas exports =>
    cases C with
    | MKcontext contextTypes contextFuncs contextGlobals contextTables contextMems contextElems contextDatas contextLocals contextLabels contextReturn =>
      dsimp only at locals labels result
      subst contextLocals; subst contextLabels; subst contextReturn
      have typesEq := bindings.types
      dsimp only at typesEq
      subst contextTypes
      apply Moduleinst_ok.mk_Moduleinst_ok s types funcs globals tables mems elems datas exports
        contextFuncs contextGlobals contextTables contextMems contextElems contextDatas
      · intro ty member; cases ty with | mk_functype params results => cases params; cases results; constructor
      · exact bindings.globals.length_eq
      · exact fun _ member => List.forall₂_zip bindings.globals member
      · exact bindings.funcs.length_eq
      · intro pair member
        obtain ⟨fn, found, same⟩ := List.forall₂_zip bindings.funcs member
        rw [← same]
        exact .func s pair.1 fn (List.getElem?_eq_some_iff.mp found).1
          (by simp [List.getElem!_eq_getElem?_getD, found]) storeWf (.externtype_case_0 _)
      · exact bindings.mems.length_eq
      · exact fun _ member => List.forall₂_zip bindings.mems member
      · exact bindings.tables.length_eq
      · exact fun _ member => List.forall₂_zip bindings.tables member
      · exact bindings.exports_typed storeWf moduleWf members
      · exact bindings.datas.length_eq
      · intro address member
        obtain ⟨_, entry, found, _⟩ := paired_left bindings.datas member
        exact (List.getElem?_eq_some_iff.mp found).1
      · intro pair member
        obtain ⟨entry, found, typed⟩ := List.forall₂_zip bindings.datas member
        simpa [List.getElem!_eq_getElem?_getD, found] using typed
      · exact bindings.elems.length_eq
      · intro address member
        obtain ⟨_, entry, found, _⟩ := paired_left bindings.elems member
        exact (List.getElem?_eq_some_iff.mp found).1
      · intro pair member
        obtain ⟨entry, found, typed⟩ := List.forall₂_zip bindings.elems member
        simpa [List.getElem!_eq_getElem?_getD, found] using typed
      · simpa only [Map] using disjoint_of_nodup distinct
      · intro entry member
        have present := members entry member
        have entryWf : wf_exportinst entry := by
          have wf : Forall wf_exportinst exports := by cases moduleWf; assumption
          exact wf entry member
        apply Exportinst_in.mk_Exportinst_in
        · have positive := List.length_pos_of_mem present
          simpa only [moduleAddresses, Map, List.append_assoc] using positive
        · simpa only [moduleAddresses, Map, List.append_assoc, List.contains_iff_mem] using present
        · exact entryWf
      · exact storeWf
      · exact moduleWf
      · exact bindings.wf
      · intro ty member; constructor
      · intro ty member; constructor
      · intro ty member
        have wf : Forall wf_memtype contextMems := by cases bindings.wf; assumption
        exact .externtype_case_3 _ (wf ty member)
      · intro ty member
        have wf : Forall wf_tabletype contextTables := by cases bindings.wf; assumption
        exact .externtype_case_2 _ (wf ty member)

/-- Assemble the genuine generated store judgment from the independently
checked component and function-instance judgments. -/
theorem StoreContentsTyped.store_ok {s : store} (contents : StoreContentsTyped s)
    (storeWf : wf_store s)
    (functions : ∀ fn ∈ s.FUNCS, Funcinst_ok s fn fn.TYPE) : Store_ok s := by
  apply Store_ok.mk_Store_ok s s.GLOBALS (s.GLOBALS.map globalinst.TYPE)
    s.MEMS (s.MEMS.map meminst.TYPE) s.TABLES (s.TABLES.map tableinst.TYPE)
    s.FUNCS (s.FUNCS.map funcinst.TYPE) s.DATAS (s.DATAS.map (fun _ => datatype.OK))
    s.ELEMS (s.ELEMS.map eleminst.TYPE)
  · simp
  · exact fun _ member => List.forall₂_zip
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr contents.globals)) member
  · simp
  · exact fun _ member => List.forall₂_zip
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr contents.memories)) member
  · simp
  · exact fun _ member => List.forall₂_zip
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr contents.tables)) member
  · simp
  · exact fun _ member => List.forall₂_zip
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr functions)) member
  · simp
  · exact fun _ member => List.forall₂_zip
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr contents.data)) member
  · simp
  · exact fun _ member => List.forall₂_zip
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr contents.elements)) member
  · rfl
  · exact storeWf
  · intro ty member
    obtain ⟨memory, rawMember, rfl⟩ := List.mem_map.mp member
    cases contents.memories memory rawMember <;> assumption
  · intro ty member
    obtain ⟨table, rawMember, rfl⟩ := List.mem_map.mp member
    cases contents.tables table rawMember <;> assumption
  · exact storeWf

end Itasca.Runtime.Abs
