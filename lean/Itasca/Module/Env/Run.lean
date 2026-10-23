import Itasca.Module.Env.Effects
import Itasca.Module.Sections.Tail
import Itasca.Module.Readers.Header

/-!
# Ordered section runs

`Run` is the history of sections decoded by the environment loop, each with its byte span and
`Effect`, in strictly increasing section order. Custom sections may appear between them.
`Run.phase`, `Run.span` and `Run.id_bounds` give the phase, byte-span and rank facts of a run.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

/-- An ordered history of decoded sections from the initial environment and declarations to the
final ones, ending at position `next` after a section of rank `id`. It records bytes and semantic
changes rather than calls to the extracted parser. -/
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

/-- A run keeps the declarations in phase, ending at the last section's rank. -/
theorem Run.phase {profile} {data initial decls start initialId after afterDecls next id}
    (h : Run (profile := profile) data initial decls start initialId after afterDecls next id)
    (hp : Phase initialId.val decls) : Phase id.val afterDecls := by
  induction h with
  | nil => exact hp
  | custom _ _ ih => exact ih
  | step _ horder _ he ih => exact he.phase ih horder

/-- A run advances the position within the input. -/
theorem Run.span {profile} {data initial decls start initialId after afterDecls next id}
    (h : Run (profile := profile) data initial decls start initialId after afterDecls next id)
    (hstart : start.val ≤ data.length) : start.val ≤ next.val ∧ next.val ≤ data.length := by
  induction h with
  | nil => exact ⟨le_rfl, hstart⟩
  | custom _ hb ih => have := hb.span; omega
  | step _ _ hh _ ih => have := hh.span; omega

end Itasca.ModuleEnv
