import Itasca.Module.Env.Run

/-!
# Section dispatch soundness

Specification of `metadata.decode_env_section`, which dispatches on a section id to the per-section
decoders. `metadata.decode_env_section.profile_spec` shows that every recognized section terminates,
preserves the `Bounded` invariant, and on success yields the `Effect` of its section. The
completeness counterpart is in `Module/Env/DispatchComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary ModuleSections ModuleEnv

/-- `metadata.decode_env_section` terminates for every section id, preserves `Bounded`, and on
success returns the `Effect` that relates the section's bytes to the resulting environment. -/
@[step]
theorem metadata.decode_env_section.profile_spec (data : Slice U8) (pos : Usize) (id : U8)
    (env : metadata.Env) (before : Declarations) (profile : ValidationProfile) (hb : Bounded env pos.val) :
    metadata.decode_env_section data pos id env profile ⦃ r => match r.1 with
      | .Ok next => ∃ after, Effect (profile := profile) data pos env before id next r.2 after ∧ Bounded r.2 next.val
      | .Err _ => True ⦄ := by
  unfold metadata.decode_env_section
  split
  · apply WP.spec_mono (metadata.decode_type_section.profile_spec data pos env profile hb.types)
    rintro ⟨r, result⟩ hp
    cases r with
    | Err e => trivial
    | Ok next =>
      obtain ⟨added, hadd, hbytes, hv, hs⟩ := hp
      refine ⟨_, .types hadd hbytes (by intro ft hm; exact ⟨(Profile.funcTypeAdmissible_iff profile ft).mpr (hv ft hm).1, (hv ft hm).2⟩), ?_⟩
      have hold := hb.mono hbytes.span.1
      rw [hadd.1]
      cases hold
      constructor <;> assumption
  · apply WP.spec_mono (metadata.decode_import_section.spec data pos env hb profile)
    rintro ⟨r, result⟩ hp
    cases r with
    | Err e => trivial
    | Ok next =>
      obtain ⟨added, hadd, hbytes, hbound⟩ := hp
      refine ⟨_, .imports hadd hbytes, ?_⟩
      exact hbound
  · apply WP.spec_mono (metadata.decode_function_section.spec data pos env hb.funcs hb.funcIndices)
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
  · apply WP.spec_mono (metadata.decode_table_section.spec data pos env hb.tables profile)
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
  · apply WP.spec_mono (metadata.decode_memory_section.spec data pos env hb.memories)
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
  · apply WP.spec_mono (metadata.decode_global_section.spec data pos env hb.globals hb.globalTypes hb.declaredFuncs profile)
    rintro ⟨r, result⟩ hp
    cases r with
    | Err e => trivial
    | Ok next =>
      obtain ⟨added, hadd, hbytes, hv, hs, ht, href⟩ := hp
      refine ⟨_, .globals hadd hbytes hv, ?_⟩
      have hold := hb.mono hbytes.span.1
      rw [hadd.1]
      cases hold
      constructor <;> assumption
  · apply WP.spec_mono (metadata.decode_export_section.spec data pos env hb)
    rintro ⟨r, result⟩ hp
    cases r with
    | Err e => trivial
    | Ok next =>
      obtain ⟨added, hadd, hbytes, hbound⟩ := hp
      refine ⟨_, .exports hadd hbytes, ?_⟩
      exact hbound
  · apply WP.spec_mono (metadata.decode_start_section.spec data pos env )
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
  · apply WP.spec_mono (metadata.decode_element_section.profile_spec data pos env profile hb.elements hb.declaredFuncs)
    rintro ⟨r, result⟩ hp
    cases r with
    | Err e => trivial
    | Ok next =>
      obtain ⟨added, hadd, hbytes, hv, hs, href⟩ := hp
      refine ⟨_, .elements hadd hbytes hv, ?_⟩
      have hold := hb.mono hbytes.span.1
      rw [hadd.1]
      cases hold
      constructor <;> assumption
  · apply WP.spec_mono (metadata.decode_data_count.spec data pos env profile)
    rintro ⟨r, result⟩ hp
    cases r with
    | Err e => trivial
    | Ok next =>
      obtain ⟨count, hbytes, he, hprofile⟩ := hp
      refine ⟨_, .dataCount hprofile he hbytes, ?_⟩
      have hold := hb.mono hbytes.span.1
      rw [he]
      cases hold
      constructor <;> assumption
  · simp

end Itasca
