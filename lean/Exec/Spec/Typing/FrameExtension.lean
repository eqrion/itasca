import Exec.Spec.ExtensionTyping
import Exec.Spec.Typing.ConfigTyping

/-! Store extension preserves retained module environments and frame typing.
Host return and trap can therefore retain the ambient typed source frame. -/
namespace Exec.Spec

private theorem paired_mono {α β : Type} {p q : α → β → Prop} {xs : List α} {ys : List β}
    (typed : Forall₂ p xs ys) (preserves : ∀ x y, p x y → q x y) : Forall₂ q xs ys :=
  fun pair member => preserves _ _ (typed pair member)

theorem val_ok_extend {s t : store} (extension : Extend_store s t)
    {value : val} {ty : valtype} (typed : Val_ok s value ty) : Val_ok t value ty := by
  have fresh := (extend_store_wf extension).2
  cases typed with
  | numtype nt value _ wf => exact .numtype _ _ _ fresh wf
  | vectype vt value _ wf => exact .vectype _ _ _ fresh wf
  | reftype value rt typed _ => exact .reftype _ _ _ (ref_ok_extend extension typed) fresh

theorem exportinst_ok_extend {s t : store} (extension : Extend_store s t)
    {entry : exportinst} (typed : Exportinst_ok s entry) : Exportinst_ok t entry := by
  cases typed with
  | mk_Exportinst_ok name address type typed _ typeWf entryWf =>
    exact .mk_Exportinst_ok _ _ _ _ (externaddr_ok_extend extension typed)
      (extend_store_wf extension).2 typeWf entryWf

/-- All old module maps and exports remain valid after committed callback
mutation, object creation, segment dropping, or Wasm growth. -/
theorem moduleinst_ok_extend {s t : store} (extension : Extend_store s t)
    {module : moduleinst} {context : _root_.context} (typed : Moduleinst_ok s module context) :
    Moduleinst_ok t module context := by
  have fresh := (extend_store_wf extension).2
  obtain ⟨_,_,_,_,dataGrowth,elemGrowth⟩ := extend_store_objects extension
  cases typed with
  | mk_Moduleinst_ok types funcs globals tables mems elems datas exports fts gts tts mts ets dts
      typesOk glength globalsOk flength funcsOk mlength memsOk tlength tablesOk exportsOk
      dlength dbounds datasOk elength ebounds elemsOk names membership _ moduleWf contextWf
      globalsWf funcsWf memsWf tablesWf =>
    apply Moduleinst_ok.mk_Moduleinst_ok
    · exact typesOk
    · exact glength
    · exact paired_mono globalsOk (fun _ _ h => externaddr_ok_extend extension h)
    · exact flength
    · exact paired_mono funcsOk (fun _ _ h => externaddr_ok_extend extension h)
    · exact mlength
    · exact paired_mono memsOk (fun _ _ h => externaddr_ok_extend extension h)
    · exact tlength
    · exact paired_mono tablesOk (fun _ _ h => externaddr_ok_extend extension h)
    · exact fun entry member => exportinst_ok_extend extension (exportsOk entry member)
    · exact dlength
    · exact fun address member => (dbounds address member).trans_le dataGrowth.1
    · intro pair member
      exact datainst_ok_extend extension (dataGrowth.2 pair.1 (dbounds _ (List.of_mem_zip member).1))
        (datasOk pair member)
    · exact elength
    · exact fun address member => (ebounds address member).trans_le elemGrowth.1
    · intro pair member
      exact eleminst_ok_extend extension (elemGrowth.2 pair.1 (ebounds _ (List.of_mem_zip member).1))
        (elemsOk pair member)
    · exact names
    · exact membership
    · exact fresh
    · exact moduleWf
    · exact contextWf
    · exact globalsWf
    · exact funcsWf
    · exact memsWf
    · exact tablesWf

/-- A suspended frame retains the same local and module context after extension. -/
theorem frame_ok_extend {s t : store} (extension : Extend_store s t)
    {frame : _root_.frame} {context : _root_.context} (typed : Frame_ok s frame context) :
    Frame_ok t frame context := by
  cases typed with
  | mk_Frame_ok values module types context moduleOk length valuesOk _ contextWf frameWf localsWf =>
    exact .mk_Frame_ok _ _ _ _ _ (moduleinst_ok_extend extension moduleOk) length
      (paired_mono valuesOk (fun _ _ h => val_ok_extend extension h))
      (extend_store_wf extension).2 contextWf frameWf localsWf

/-- A typed post-call store plus extension preserves the ambient source state. -/
theorem state_ok_extend {s t : store} {frame : _root_.frame} {context : _root_.context}
    (extension : Extend_store s t) (typedStore : Store_ok t)
    (typed : State_ok ⟨s,frame⟩ context) : State_ok ⟨t,frame⟩ context := by
  cases typed with
  | mk_State_ok _ _ context _ frameOk contextWf stateWf =>
    have frameWf : wf_frame frame := by cases stateWf; assumption
    exact .mk_State_ok _ _ _ typedStore (frame_ok_extend extension frameOk) contextWf
      (.state_case_0 _ _ (extend_store_wf extension).2 frameWf)

end Exec.Spec
