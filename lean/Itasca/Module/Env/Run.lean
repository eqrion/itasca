import Itasca.Module.Env.Effects
import Itasca.Module.Sections.Tail
import Itasca.Module.Readers.Header

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

/-- An ordered history of decoded sections. The judgments record bytes and
semantic changes rather than calls to the extracted parser. -/
inductive Run (data : Slice U8) (initial : module.Env) (decls : Declarations)
    (start : Usize) (initialId : U8) : module.Env → Declarations → Usize → U8 →
      (profile : optParam ValidationProfile .Wasm1) → Prop where
  | nil {profile} : Run (profile := profile) data initial decls start initialId initial decls start initialId
  | custom {profile} {before beforeDecls pos last next} :
      Run (profile := profile) data initial decls start initialId before beforeDecls pos last →
      ModuleBinary.At (fun (_ : Unit) => ModuleBinary.CustomEncoding) data pos () next →
      Run (profile := profile) data initial decls start initialId before beforeDecls next last
  | step {profile} {before beforeDecls pos last id first next after afterDecls} :
      Run (profile := profile) data initial decls start initialId before beforeDecls pos last →
      last.val < (ModuleBinary.sectionRank id).val →
      ModuleBinary.SectionHeader data pos id first next →
      Effect (profile := profile) data first before beforeDecls id next after afterDecls →
      Run (profile := profile) data initial decls start initialId after afterDecls next (ModuleBinary.sectionRank id)

theorem Run.phase {profile} {data initial decls start initialId after afterDecls next id}
    (h : Run (profile := profile) data initial decls start initialId after afterDecls next id)
    (hp : Phase initialId.val decls) : Phase id.val afterDecls := by
  induction h with
  | nil => exact hp
  | custom _ _ ih => exact ih
  | step _ horder _ he ih => exact he.phase ih horder

theorem Run.span {profile} {data initial decls start initialId after afterDecls next id}
    (h : Run (profile := profile) data initial decls start initialId after afterDecls next id)
    (hstart : start.val ≤ data.length) : start.val ≤ next.val ∧ next.val ≤ data.length := by
  induction h with
  | nil => exact ⟨le_rfl, hstart⟩
  | custom _ hb ih => have := hb.span; omega
  | step _ _ hh _ ih => have := hh.span; omega

theorem Run.id_bounds {profile} {data initial decls start initialId after afterDecls next id}
    (h : Run (profile := profile) data initial decls start initialId after afterDecls next id)
    (hstart : initialId.val ≤ 10) : initialId.val ≤ id.val ∧ id.val ≤ 10 := by
  induction h with
  | nil => exact ⟨le_rfl, hstart⟩
  | custom _ _ ih => exact ih
  | step _ ho _ he ih => have := he.id_range; omega

end Itasca.ModuleEnv
