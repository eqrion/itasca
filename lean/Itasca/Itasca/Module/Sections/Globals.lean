import Itasca.Module.Sections.Headers

/-! ## Global -/

section

/-!
# Global section parser

Soundness of `metadata.decode_global_section` and its loop. `GlobalsAdded` says the environment
gains the decoded globals, their types and the function references their initializers declare.
The span is a `VecEncoding GlobalEncoding` and each initializer is `Module.Constants.Valid` at its
global's type. Completeness is in `Module/Sections/DeclarationsComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Constants

/-- Constant validity is preserved when globals are appended after the imported ones. -/
theorem Valid.append_globals {env result e t} (h : Valid env e t)
    (suffix : List metadata.Global)
    (hglobals : result.globals.val = env.globals.val ++ suffix)
    (hcount : result.num_imported_globals = env.num_imported_globals)
    (hfuncs : result.funcs.val.length = env.funcs.val.length) : Valid result e t := by
  cases h with
  | i32 value => exact .i32 value
  | i64 value => exact .i64 value
  | f32 value => exact .f32 value
  | f64 value => exact .f64 value
  | v128 low high => exact .v128 low high
  | refNull ty => exact .refNull ty
  | refFunc idx hi => exact .refFunc idx (by simpa [hfuncs] using hi)
  | globalGet idx gt hi hgt himport hconst =>
    have hi' : idx.val < result.globals.val.length := by simp [hglobals]; omega
    exact Valid.globalGet idx gt hi'
      (by simpa only [hglobals, List.getElem_append_left hi] using hgt)
      (by simpa [hcount] using himport) hconst

end Itasca.Module.Constants

namespace Itasca.Module.Sections

/-- `result` is `env` with the globals `added` appended to the globals and global types, and the
function references of their initializers appended to the declared functions. Nothing else
changes. -/
def GlobalsAdded (env result : metadata.CodeMetadata) (added : List Binary.Global) : Prop :=
  result = { env with globals := result.globals, funcs := result.funcs } ∧
  result.globals.val = env.globals.val ++ added.map (fun g => ⟨g.gtype, some g.init, false⟩) ∧
  Module.References.Added env { env with funcs := result.funcs }
    (added.flatMap fun g => Module.References.initializer g.init)

/-- A global type and an initializer span in sequence form a `GlobalEncoding`. -/
theorem global_encoded {data start pos next gt init}
    (hg : Binary.At Binary.GlobalTypeEncoding data start gt pos)
    (hi : Binary.At Binary.ConstEncoding data pos init next) :
    Binary.At Binary.GlobalEncoding data start ⟨gt, init⟩ next := by
  obtain ⟨gbytes, hg, hs⟩ := hg
  obtain ⟨ibytes, hi, his⟩ := hi
  exact ⟨gbytes ++ ibytes, Binary.GlobalEncoding.reader_parts.mpr ⟨gbytes, ibytes, hg, hi, rfl⟩, hs.append his⟩

end Itasca.Module.Sections

namespace Itasca

open Binary Module.Sections

/-- The global loop adds `count` globals forming a `Rep GlobalEncoding` span, with valid
initializers. -/
@[step]
theorem metadata.decode_global_section_loop.spec (data : Slice U8) (env : metadata.CodeMetadata)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hglobals : env.globals.val.length ≤ start.val)
    :
    metadata.decode_global_section_loop data env count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ added, added.length = count.val ∧ GlobalsAdded env r.2 added ∧
          At (Rep GlobalEncoding) data start added next ∧
          (∀ g ∈ added, Module.Constants.Valid r.2 g.init g.gtype.valtype) ∧
          r.2.globals.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  unfold metadata.decode_global_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ added, added.length = s.2.2.val ∧
      GlobalsAdded env s.1 added ∧ At (Rep GlobalEncoding) data start added s.2.1 ∧
      (∀ g ∈ added, Module.Constants.Valid s.1 g.init g.gtype.valtype) ∧
      s.1.globals.val.length ≤ s.2.1.val)
  · rintro ⟨current, pos, i⟩ ⟨hi, added, hlen, henv, hbytes, hvalid, hglobals⟩
    dsimp only at hi hlen henv hbytes hvalid hglobals
    unfold metadata.decode_global_section_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : i.val = count.val := by scalar_tac
      exact ⟨added, by omega, henv, hbytes, hvalid, hglobals⟩
    · rename_i hmore
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (metadata.decode_global_type.spec data pos)
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        obtain ⟨gt, middle⟩ := pair
        have hprogress : pos.val < middle.val := by
          obtain ⟨bytes, he, hs⟩ := hp
          obtain rfl := GlobalTypeEncoding.reader_bytes.mp he
          have := hs.length
          simp only [List.length_cons, List.length_nil] at this
          omega
        obtain ⟨r, hc, hconst⟩ := WP.spec_imp_exists (metadata.decode_const_expr.spec data middle current gt.valtype)
        cases r with
        | Err e => simp [hc, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok pair =>
          obtain ⟨init, next⟩ := pair
          obtain ⟨hcb, hcv⟩ := hconst
          have hs := hcb.span
          have cap : current.globals.val.length < Usize.max := by scalar_tac
          have validIndex : ∀ idx ∈ Module.References.initializer init, idx.val < current.funcs.val.length := by
            generalize gt.valtype = ty at hcv
            cases hcv <;> simp_all [Module.References.initializer]
          simp [hc, core.result.Result.Insts.CoreOpsTry.branch]
          step with metadata.declare_initializer.spec current init validIndex as ⟨marked, hm⟩
          have hg : marked.globals = current.globals := by rw [hm.fields]
          have hcount : marked.num_imported_globals = current.num_imported_globals := by rw [hm.fields]
          have hfn : marked.funcs.val.length = current.funcs.val.length := by simp [hm.funcs]
          have hroom : marked.globals.val.length < Usize.max := hg ▸ cap
          step as ⟨globals, hpush⟩
          step as ⟨j,hj⟩
          let entry : Binary.Global := ⟨gt, init⟩
          let desc : metadata.Global := ⟨gt, some init, false⟩
          refine ⟨by scalar_tac, ⟨added ++ [entry], by simp [hlen,hj], ?_, hbytes.snoc (global_encoded hp hcb), ?_, ?_⟩, by scalar_tac⟩
          · refine ⟨?_, ?_, ?_⟩
            · rw [hm.fields, henv.1]
            · simp [hpush, hg, henv.2.1, List.append_assoc, entry]
            · have update : Module.References.Added { env with funcs := current.funcs }
                    { env with funcs := marked.funcs } (Module.References.initializer init) :=
                ⟨rfl, hm.funcs⟩
              simpa [entry] using henv.2.2.trans update
          · intro g hmem
            have transport {v ty} (hv : Module.Constants.Valid current v ty) :
                Module.Constants.Valid { marked with globals := globals } v ty :=
              hv.append_globals [desc] (by simpa [hg,desc] using hpush) hcount hfn
            rcases List.mem_append.mp hmem with hmem | hmem
            · exact transport (hvalid g hmem)
            · obtain rfl := List.mem_singleton.mp hmem
              exact transport hcv
          · simp [hpush,hg]; omega
  · exact ⟨by simp, [], by simp, ⟨by cases env; rfl, by simp, Module.References.Added.refl _⟩,
      ⟨[], .nil, Body.Scalar.BytesAt.nil data start hstart⟩, by simp, hglobals⟩

/-- `metadata.decode_global_section` adds the globals of a `VecEncoding GlobalEncoding` span, with
valid initializers. -/
@[step]
theorem metadata.decode_global_section.spec (data : Slice U8) (pos : Usize) (env : metadata.CodeMetadata)
    (hglobals : env.globals.val.length ≤ pos.val)
    :
    metadata.decode_global_section data pos env ⦃ r => match r.1 with
      | .Ok next => ∃ added, GlobalsAdded env r.2 added ∧
          At (VecEncoding GlobalEncoding) data pos added next ∧
          (∀ g ∈ added, Module.Constants.Valid r.2 g.init g.gtype.valtype) ∧
          r.2.globals.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e => simp [metadata.decode_global_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨count, start⟩ := pair
    have hs := hc.span
    obtain ⟨⟨r, result⟩, hloop, hp⟩ := WP.spec_imp_exists
      (metadata.decode_global_section_loop.spec data env count start hs.2.2 (by omega))
    simp [metadata.decode_global_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok next =>
      obtain ⟨added, hlen, henv, hb, ht, hg⟩ := hp
      exact ⟨added, henv, At.vector hc hb hlen, ht, hg⟩

end Itasca

end
