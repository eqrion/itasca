import Itasca.Runtime.Store.Initialization.ElementValues
import Itasca.Runtime.Store.Api.GlobalEffects
import Itasca.Runtime.Store.Initialization.DataEffects
import Itasca.Runtime.Store.Invariant.BindingTyping
import Itasca.Runtime.Compiler.Local.Source.SourceSlice
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca

private theorem maps_two {α β γ δ : Type} (values : List α) (f : α → β) (g : α → γ) (pair : β → γ → δ) :
    Map₂ pair (values.map f) (values.map g) = values.map (fun x => pair (f x) (g x)) := by
  induction values with
  | nil => rfl
  | cons head tail ih => simpa only [Map₂, List.map_cons, List.ap, List.zipWith_cons_cons] using congrArg (pair (f head) (g head) :: ·) ih

private theorem maps_three {α β γ δ ε : Type} (values : List α) (f : α → β) (g : α → γ) (h : α → δ)
    (triple : β → γ → δ → ε) :
    Map₃ triple (values.map f) (values.map g) (values.map h) = values.map (fun x => triple (f x) (g x) (h x)) := by
  induction values with
  | nil => rfl
  | cons head tail ih => simpa only [Map₃, List.map_cons, List.ap, List.zipWith_cons_cons] using congrArg (triple (f head) (g head) (h head) :: ·) ih

theorem GlobalSourceValues.types {s inst sources values}
    (related : GlobalSourceValues s inst sources values) :
    (values.map decodeGlobal).map globalinst.TYPE = sources.map (fun original => Translate.globalType original.gtype) := by
  induction related with
  | nil => rfl
  | cons current rest ih => simp only [List.map_cons, decode_global_type_source, current.1, ih]

theorem GlobalSourceValues.evaluations {s inst sources values}
    (related : GlobalSourceValues s inst sources values) :
    List.Forall₂ (fun expression value => Eval_expr ⟨s, ⟨[], inst⟩⟩ expression ⟨s, ⟨[], inst⟩⟩ [value])
      (sources.map fun original => ModuleConstants.expression original.init)
      ((values.map decodeGlobal).map globalinst.VALUE) := by
  induction related with
  | nil => exact .nil
  | cons current rest ih => exact .cons current.2 ih

theorem GlobalSourceValues.syntax {s inst sources values}
    (related : GlobalSourceValues s inst sources values) :
    sources.map ModuleConstants.global = Map₂ (fun expression ty => global.GLOBAL ty expression)
      (sources.map fun original => ModuleConstants.expression original.init)
      ((values.map decodeGlobal).map globalinst.TYPE) := by
  rw [related.types, maps_two]
  rfl

theorem ElementSourceSegments.types {s inst sources values}
    (related : ElementSourceSegments s inst sources values) :
    (values.map decodeElement).map eleminst.TYPE = sources.map (fun original => Translate.referenceType original.elem) := by
  induction related with
  | nil => rfl
  | cons current rest ih => simp only [List.map_cons, decodeElement, decode_elem_type_source, current.1, ih]

theorem ElementSourceValues.evaluations {s inst ty sources values}
    (related : ElementSourceValues s inst ty sources values) :
    List.Forall₂ (fun expression value => Eval_expr ⟨s, ⟨[], inst⟩⟩ expression ⟨s, ⟨[], inst⟩⟩ [val_ref value])
      (sources.map ModuleConstants.expression) (values.map (decodeRef ty)) := by
  induction related with
  | nil => exact .nil
  | cons current rest ih =>
    apply List.Forall₂.cons _ ih
    simpa only [ref_val_eq] using current

theorem ElementSourceSegments.evaluations {s inst sources values}
    (related : ElementSourceSegments s inst sources values) :
    List.Forall₂ (fun expressions references => List.Forall₂
      (fun expression reference => Eval_expr ⟨s, ⟨[], inst⟩⟩ expression ⟨s, ⟨[], inst⟩⟩ [val_ref reference])
      expressions references)
      (sources.map fun original => original.init.val.map ModuleConstants.expression)
      ((values.map decodeElement).map eleminst.REFS) := by
  induction related with
  | nil => exact .nil
  | cons current rest ih =>
    apply List.Forall₂.cons _ ih
    simpa only [decodeElement, current.1] using current.2.evaluations

theorem ElementSourceSegments.syntax {s inst sources values}
    (related : ElementSourceSegments s inst sources values) :
    (sources.map ModuleEnv.rawElement).map ModuleElaboration.element =
      Map₃ (fun mode expressions ty => elem.ELEM ty expressions mode)
        (sources.map fun original => ModuleSegments.elementMode original.mode)
        (sources.map fun original => original.init.val.map ModuleConstants.expression)
        ((values.map decodeElement).map eleminst.TYPE) := by
  rw [related.types, maps_three]
  simp only [List.map_map, Function.comp_def, ModuleElaboration.element, ModuleEnv.rawElement]

theorem source_data_payload_syntax (sources : List Itasca.module.Data) :
    (sources.map ModuleData.raw).map ModuleData.translate =
      Map₂ data.DATA ((sources.map sourceDataPayload).map datainst.BYTES)
        (sources.map fun original => ModuleSegments.dataMode original.mode) := by
  simp only [List.map_map, Function.comp_def, sourceDataPayload]
  rw [maps_two]
  rfl
end Itasca.Runtime.Store

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca

theorem GlobalSourceValues.raw_evaluations {s inst sources values}
    (related : GlobalSourceValues s inst sources values) :
    List.Forall₂ (fun original value => Eval_expr ⟨s, ⟨[], inst⟩⟩
      (ModuleConstants.expression original.init) ⟨s, ⟨[], inst⟩⟩ [value])
      sources ((values.map decodeGlobal).map globalinst.VALUE) :=
  List.forall₂_map_left_iff.mp related.evaluations

theorem ElementSourceSegments.raw_evaluations {s inst sources values}
    (related : ElementSourceSegments s inst sources values) :
    List.Forall₂ (fun original references => List.Forall₂
      (fun expression reference => Eval_expr ⟨s, ⟨[], inst⟩⟩ (ModuleConstants.expression expression)
        ⟨s, ⟨[], inst⟩⟩ [val_ref reference]) original.init references)
      (sources.map ModuleEnv.rawElement) ((values.map decodeElement).map eleminst.REFS) := by
  apply List.forall₂_map_left_iff.mpr
  exact (List.forall₂_map_left_iff.mp related.evaluations).imp
    (fun _ _ current => List.forall₂_map_left_iff.mp current)
end Itasca.Runtime.Store
