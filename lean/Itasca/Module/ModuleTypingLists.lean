import Itasca.Module.ModuleIndexSpaces

open Aeneas Aeneas.Std

namespace Itasca.ModuleElaboration

theorem forall₂_generated {α β : Type} {R : α → β → Prop} {xs ys}
    (h : List.Forall₂ R xs ys) : Forall₂ R xs ys := by
  induction h with
  | nil => simp [Forall₂]
  | cons hp _ ih => simpa [Forall₂] using And.intro hp ih

theorem forall₂_map {α β γ : Type} (xs : List α) (f : α → β) (g : α → γ)
    (R : β → γ → Prop) (h : ∀ a ∈ xs, R (f a) (g a)) :
    List.Forall₂ R (xs.map f) (xs.map g) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (h x (by simp)) (ih (by intro a ha; exact h a (by simp [ha])))

theorem forall₂_left {α β : Type} {R : α → β → Prop} {xs ys}
    (h : List.Forall₂ R xs ys) (P : α → Prop) (hp : ∀ a b, R a b → P a) : Forall P xs := by
  induction h with
  | nil => simp [Forall]
  | cons hr _ ih => simpa [Forall] using And.intro (hp _ _ hr) ih

theorem forall₂_right {α β : Type} {R : α → β → Prop} {xs ys}
    (h : List.Forall₂ R xs ys) (P : β → Prop) (hp : ∀ a b, R a b → P b) : Forall P ys := by
  induction h with
  | nil => simp [Forall]
  | cons hr _ ih => simpa [Forall] using And.intro (hp _ _ hr) ih

theorem functions_typed {env indices codes} (h : List.Forall₂ (CodeEntry.Typed env) indices codes)
    (C : context) (hc : CodeEntry.ModuleContext env C) :
    List.Forall₂ (fun ft f => Func_ok C f ft)
      (indices.map (functionType env.types.val)) (List.zipWith CodeEntry.function indices codes) := by
  induction h with
  | nil => exact .nil
  | cons hp _ ih =>
    apply List.Forall₂.cons _ ih
    simpa [functionType_lookup hp.type_lt] using hp.func_ok C hc

theorem exports_typed {env entries xts}
    (h : List.Forall₂ (ModuleExternals.ExportResolves env) entries xts)
    (hn : ∀ entry ∈ entries, wf_name (ModuleBinary.nameOfBytes entry.name.val))
    (C : context) (hc : CodeEntry.ModuleContext env C) :
    List.Forall₂ (Export_ok C) (entries.map (fun e => exportDecl (ModuleEnv.rawExport e)))
      (xts.map ModuleExternals.externalType) := by
  induction h with
  | nil => exact .nil
  | cons hp _ ih =>
    exact .cons (export_typed hp (hn _ (by simp)) C hc)
      (ih (by intro e he; exact hn e (by simp [he])))

theorem Func_ok.wf {C f ft} (h : Func_ok C f ft) : wf_func f := by cases h; assumption
theorem Global_ok.wf {C g gt} (h : Global_ok C g gt) : wf_global g := by cases h; assumption
theorem Table_ok.wf {C t tt} (h : Table_ok C t tt) : wf_table t := by cases h; assumption
theorem Mem_ok.wf {C m mt} (h : Mem_ok C m mt) : wf_mem m := by cases h; assumption
theorem Elem_ok.wf {C e rt} (h : Elem_ok C e rt) : wf_elem e := by cases h; assumption
theorem Data_ok.wf {C d} (h : Data_ok C d) : wf_data d := by cases h; assumption
theorem Import_ok.wf {C i xt} (h : Import_ok C i xt) : wf_import i := by cases h; assumption
theorem Export_ok.wf {C e xt} (h : Export_ok C e xt) : wf_export e := by cases h; assumption
theorem Export_ok.type_wf {C e xt} (h : Export_ok C e xt) : wf_externtype xt := by cases h; assumption
theorem Start_ok.wf {C s} (h : Start_ok C s) : wf_start s := by cases h; assumption

end Itasca.ModuleElaboration
