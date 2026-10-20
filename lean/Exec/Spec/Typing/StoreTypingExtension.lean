import Exec.Spec.Typing.StoreComponentTyping
import Exec.Spec.Typing.AdminExtension

/-! Existing instances and frame environments remain semantically typed under
source store extension, independently of post-store typing. -/

namespace Exec.Spec
open SpecExt

theorem globalinst_typing_extend {s t : store} (extension : Extend_store s t)
    {object : globalinst} {type : globaltype} (typed : Globalinst_ok s object type) : Globalinst_ok t object type := by
  cases typed with
  | mk_Globalinst_ok mutable type value typeOk valueTyped _ objectWf =>
    exact .mk_Globalinst_ok _ _ _ _ typeOk (val_ok_extend extension valueTyped)
      (extend_store_wf extension).2 objectWf

theorem meminst_typing_extend {s t : store} (extension : Extend_store s t)
    {object : meminst} {type : memtype} (typed : Meminst_ok s object type) : Meminst_ok t object type := by
  cases typed with
  | mk_Meminst_ok count maximum bytes typeOk length _ objectWf typeWf =>
    exact .mk_Meminst_ok _ _ _ _ typeOk length (extend_store_wf extension).2 objectWf typeWf

theorem tableinst_typing_extend {s t : store} (extension : Extend_store s t)
    {object : tableinst} {type : tabletype} (typed : Tableinst_ok s object type) : Tableinst_ok t object type := by
  cases typed with
  | mk_Tableinst_ok count maximum type refs typeOk refsTyped length _ objectWf typeWf =>
    exact .mk_Tableinst_ok _ _ _ _ _ typeOk (fun value member => ref_ok_extend extension (refsTyped value member))
      length (extend_store_wf extension).2 objectWf typeWf

theorem funcinst_typing_extend {s t : store} (extension : Extend_store s t)
    {object : funcinst} {type : functype} (typed : Funcinst_ok s object type) : Funcinst_ok t object type := by
  cases typed with
  | mk_Funcinst_ok type module fn context typeOk moduleTyped bodyTyped _ contextWf objectWf =>
    exact .mk_Funcinst_ok _ _ _ _ _ typeOk (moduleinst_ok_extend extension moduleTyped) bodyTyped
      (extend_store_wf extension).2 contextWf objectWf
  | host type module identity typeOk _ objectWf =>
    exact .host _ _ _ _ typeOk (extend_store_wf extension).2 objectWf

theorem datainst_typing_extend {s t : store} (extension : Extend_store s t)
    {object : datainst} {type : datatype} (typed : Datainst_ok s object type) : Datainst_ok t object type := by
  cases typed with
  | mk_Datainst_ok bytes length _ objectWf =>
    exact .mk_Datainst_ok _ _ length (extend_store_wf extension).2 objectWf

theorem eleminst_typing_extend {s t : store} (extension : Extend_store s t)
    {object : eleminst} {type : elemtype} (typed : Eleminst_ok s object type) : Eleminst_ok t object type := by
  cases typed with
  | mk_Eleminst_ok type refs refsTyped length _ =>
    exact .mk_Eleminst_ok _ _ _ (fun value member => ref_ok_extend extension (refsTyped value member))
      length (extend_store_wf extension).2

theorem resultsTyped_extend {s t : store} (extension : Extend_store s t)
    {types : List valtype} {values : List val} (typed : ResultsTyped s types values) : ResultsTyped t types values := by
  induction typed with
  | nil => exact .nil
  | cons value tail ih => exact .cons (val_ok_extend extension value) ih

theorem FrameEnvironment.extend {s t : store} (extension : Extend_store s t)
    {frame : _root_.frame} {context : _root_.context} (environment : FrameEnvironment s frame context) :
    FrameEnvironment t frame context :=
  ⟨moduleinst_ok_extend extension environment.moduleTyped,resultsTyped_extend extension environment.locals⟩

end Exec.Spec
