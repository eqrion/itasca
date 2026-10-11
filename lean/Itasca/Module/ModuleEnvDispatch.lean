import Itasca.Module.ModuleEnvTrace

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary ModuleSections ModuleEnv

/-- Every recognized declaration section terminates, preserves allocation bounds,
and returns its exact independent byte/semantic transition on success. -/
@[step]
theorem module.decode_env_section.spec (data : Slice U8) (pos : Usize) (id : U8)
    (env : module.Env) (before : Declarations) (hb : Bounded env pos.val) :
    module.decode_env_section data pos id env ⦃ r => match r.1 with
      | .Ok next => ∃ after, Effect data pos env before id next r.2 after ∧ Bounded r.2 next.val
      | .Err _ => True ⦄ := by
  unfold module.decode_env_section
  split
  · apply WP.spec_mono (module.decode_type_section.spec data pos env hb.types)
    rintro ⟨r, result⟩ hp
    cases r with
    | Err e => trivial
    | Ok next =>
      obtain ⟨added, hadd, hbytes, hv, hs⟩ := hp
      refine ⟨_, .types hadd hbytes hv, ?_⟩
      have hold := hb.mono hbytes.span.1
      rw [hadd.1]
      cases hold
      constructor <;> assumption
  · apply WP.spec_mono (module.decode_import_section.spec data pos env hb)
    rintro ⟨r, result⟩ hp
    cases r with
    | Err e => trivial
    | Ok next =>
      obtain ⟨added, hadd, hbytes, hbound⟩ := hp
      refine ⟨_, .imports hadd hbytes, ?_⟩
      exact hbound
  · apply WP.spec_mono (module.decode_function_section.spec data pos env hb.funcs hb.funcIndices)
    rintro ⟨r, result⟩ hp
    cases r with
    | Err e => trivial
    | Ok next =>
      obtain ⟨indices, signatures, hadd, hbytes, hs, hi⟩ := hp
      refine ⟨_, .functions hadd hbytes, ?_⟩
      have hold := hb.mono hbytes.span.1
      rw [hadd.1]
      cases hold
      constructor <;> assumption
  · apply WP.spec_mono (module.decode_table_section.spec data pos env hb.tables)
    rintro ⟨r, result⟩ hp
    cases r with
    | Err e => trivial
    | Ok next =>
      obtain ⟨added, hadd, hbytes, hv, hs, hc⟩ := hp
      refine ⟨_, .tables hadd hbytes hv hc, ?_⟩
      have hold := hb.mono hbytes.span.1
      rw [hadd.1]
      cases hold
      constructor <;> assumption
  · apply WP.spec_mono (module.decode_memory_section.spec data pos env hb.memories)
    rintro ⟨r, result⟩ hp
    cases r with
    | Err e => trivial
    | Ok next =>
      obtain ⟨added, hadd, hbytes, hv, hs, hc⟩ := hp
      refine ⟨_, .memories hadd hbytes hv hc, ?_⟩
      have hold := hb.mono hbytes.span.1
      rw [hadd.1]
      cases hold
      constructor <;> assumption
  · apply WP.spec_mono (module.decode_global_section.spec data pos env hb.globals hb.globalTypes)
    rintro ⟨r, result⟩ hp
    cases r with
    | Err e => trivial
    | Ok next =>
      obtain ⟨added, hadd, hbytes, hv, hs, ht⟩ := hp
      refine ⟨_, .globals hadd hbytes hv, ?_⟩
      have hold := hb.mono hbytes.span.1
      rw [hadd.1]
      cases hold
      constructor <;> assumption
  · apply WP.spec_mono (module.decode_export_section.spec data pos env hb)
    rintro ⟨r, result⟩ hp
    cases r with
    | Err e => trivial
    | Ok next =>
      obtain ⟨added, hadd, hbytes, hbound⟩ := hp
      refine ⟨_, .exports hadd hbytes, ?_⟩
      exact hbound
  · apply WP.spec_mono (module.decode_start_section.spec data pos env )
    rintro ⟨r, result⟩ hp
    cases r with
    | Err e => trivial
    | Ok next =>
      obtain ⟨idx, hbytes, he, hi⟩ := hp
      refine ⟨_, .start he hbytes hi, ?_⟩
      have hold := hb.mono hbytes.span.1
      rw [he]
      cases hold
      constructor <;> assumption
  · apply WP.spec_mono (module.decode_element_section.spec data pos env hb.elements)
    rintro ⟨r, result⟩ hp
    cases r with
    | Err e => trivial
    | Ok next =>
      obtain ⟨added, hadd, hbytes, hv, hs⟩ := hp
      refine ⟨_, .elements hadd hbytes hv, ?_⟩
      have hold := hb.mono hbytes.span.1
      rw [hadd.1]
      cases hold
      constructor <;> assumption
  ·
    simp

end Itasca
