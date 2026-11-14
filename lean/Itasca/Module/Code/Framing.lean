import Itasca.Binary.Wasm1.DeclaredReferences
import Itasca.Module.Code.Encoding
import Itasca.Contracts
import Itasca.Visitor.Total
import Itasca.Support.Result
import Itasca.Module.Code.LocalsComplete

/-!
Sections, each formerly its own module: Entry, EntryWitness, ReachedEntry, Framing.
-/

/-! ## Entry -/

section

/-!
# Code entry validation

For any visitor with total callbacks, `metadata.validate_code_entry_with.pipeline_of_body_total`
reduces termination to body termination and records successful calls as a `CodeEntry.Witness`.
The profile entry proofs combine these witnesses with body soundness.
-/

open Aeneas Aeneas.Std

namespace Itasca.CodeEntry

/-- The data of a successful run of the entry validator at `index`, from `start` to `finish`. It
records the size header, the locals bytes and bound, the context handed to the visitor, the
function-start callback and the body validation on the body slice. -/
structure Witness {V : Type} (visitor : code.OpVisitor V) (data : Slice U8)
    (env : metadata.Env) (index start finish : Usize) (v v' : V)
     where
  typeIdx : U32
  ft : wasm_types.FuncType
  groups : List (U32 × wasm_types.ValueType)
  ctx : code.Context
  content : Usize
  bodyStart : Usize
  body : Slice U8
  size : U32
  startedState : V
  index_lt : index.val < env.func_type_indices.val.length
  index_type : env.func_type_indices.val[index.val] = typeIdx
  type_lt : typeIdx.val < env.types.val.length
  function_type : env.types.val[typeIdx.val] = ft
  header : Leb128.Decoded data start size content
  extent : finish.val = content.val + size.val
  locals_bytes : ModuleBinary.At (ModuleBinary.VecEncoding ModuleBinary.LocalEncoding)
    data content groups bodyStart
  locals_bound : (ModuleLocals.declared groups).length ≤ limits.MAX_LOCALS.val
  context_locals : ctx.locals.val = ft.params.val ++ ModuleLocals.declared groups
  context_results : ctx.results.val = ft.results.val
  body_bytes : Wasm1.BytesAt data bodyStart body.val finish
  function_start : visitor.on_function_start v ctx typeIdx bodyStart finish = .ok (.Ok (), startedState)
  body_accepted : code.validate_body_with visitor body env ctx typeIdx startedState =
    .ok (.Ok (), v')

/-- Parameter counts bounded by the maximum module size give `Bounds`. -/
theorem Bounds.of_module_bound (env : metadata.Env)
    (h : ∀ ft ∈ env.types.val, ft.params.val.length ≤ limits.MAX_MODULE_BYTES.val) : Bounds env := by
  intro ft hm
  have := h ft hm
  have hcap : limits.MAX_MODULE_BYTES.val + limits.MAX_LOCALS.val ≤ Usize.max := by
    simp only [limits.MAX_MODULE_BYTES, limits.MAX_LOCALS]
    scalar_tac
  omega

end CodeEntry

/-- Given a body operation that terminates, `metadata.validate_code_entry_with` terminates and each
successful call has a `CodeEntry.Witness`. Rejecting callbacks are ordinary module errors. -/
theorem metadata.validate_code_entry_with.pipeline_of_body_total {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (data : Slice U8) (pos : Usize)
    (env : metadata.Env) (index : Usize) (v : V) (hbound : CodeEntry.Bounds env)

    (hbody : ∀ body ctx typeIdx started,
      ∃ r, code.validate_body_with visitor body env ctx typeIdx started = .ok r) :
    metadata.validate_code_entry_with visitor data pos env index v ⦃ r =>
      ∀ finish, r.1 = .Ok finish →
        Nonempty (CodeEntry.Witness visitor data env index pos finish v r.2 ) ⦄ := by
  unfold metadata.validate_code_entry_with
  dsimp only
  split
  · simp
  · rename_i hindex
    have hi : index.val < env.func_type_indices.val.length := by scalar_tac
    obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
    rw [hr]
    cases r with
    | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          error.Error.Insts.CoreConvertFromOpError.from]
    | Ok pair =>
        obtain ⟨size, content⟩ := pair
        have hs := hp.span
        simp [core.result.Result.Insts.CoreOpsTry.branch]
        step
        obtain ⟨r, hh, hhpost⟩ := WP.spec_imp_exists (metadata.have_bytes.spec data content n hs.2.2)
        rw [hh]
        cases r with
        | Err e =>
            simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok u =>
            cases u
            have hbytes := hhpost.1.mp rfl
            simp
            step
            obtain ⟨r, hl, hlpost⟩ := WP.spec_imp_exists (metadata.decode_locals.spec data content )
            rw [hl]
            cases r with
            | Err e =>
                simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok pair =>
                obtain ⟨declared, bodyStart⟩ := pair
                obtain ⟨groups, hg, hd, hcap⟩ := hlpost
                simp
                split
                · simp
                · rename_i hbodyStart
                  step
                  step
                  split
                  · simp
                  · rename_i htype
                    have hti : type_idx.val < env.types.val.length := by scalar_tac
                    step
                    have hftmem : ft ∈ env.types.val := by
                      rw [ft_post]
                      exact List.getElem_mem _
                    have hparams := hbound ft hftmem
                    have hroom : ft.params.val.length + declared.val.length ≤ Usize.max := by omega
                    obtain ⟨v1, hv1, v1_post⟩ := WP.spec_imp_exists
                      (metadata.build_func_locals.spec (alloc.vec.Vec.deref ft.params)
                        (alloc.vec.Vec.deref declared) (by simpa [alloc.vec.Vec.deref] using hroom))
                    obtain ⟨v2, hv2, v2_post⟩ := WP.spec_imp_exists
                      (metadata.copy_value_types.spec (alloc.vec.Vec.deref ft.results))
                    rw [hv1]
                    simp only [bind_ok]
                    rw [hv2]
                    simp only [bind_ok]
                    obtain ⟨reply, started, hstart⟩ := hvisitor.on_function_start v
                      ⟨v1, v2⟩ type_idx bodyStart «end»
                    rw [hstart]
                    cases reply with
                    | Err e => simp
                    | Ok u =>
                        cases u
                        simp
                        step as ⟨s3, s3_post⟩
                        obtain ⟨⟨result, finished⟩, hb⟩ := hbody s3 ⟨v1, v2⟩ type_idx started
                        rw [hb]
                        cases result with
                        | Err e => simp
                        | Ok u =>
                            cases u
                            simp
                            refine ⟨{
                              typeIdx := type_idx, ft := ft, groups := groups, ctx := ⟨v1, v2⟩
                              content := content, bodyStart := bodyStart, body := s3, size := size
                              startedState := started, index_lt := hi, index_type := type_idx_post.symm
                              type_lt := hti, function_type := ?_, header := hp, extent := ?_
                              locals_bytes := hg, locals_bound := ?_, context_locals := ?_
                              context_results := ?_, body_bytes := ?_, function_start := hstart
                              body_accepted := hb }⟩
                            · simpa [t_post] using ft_post.symm
                            · scalar_tac
                            · simpa [hd] using hcap
                            · simpa [alloc.vec.Vec.deref, hd] using v1_post
                            · simpa [alloc.vec.Vec.deref] using v2_post
                            · exact ModuleBinary.slice_bytes (by scalar_tac) (by scalar_tac) s3_post

end Itasca

end

/-! ## EntryWitness -/

section

/-!
# Code entry witnesses

`metadata.validate_code_entry_with.witness_profile` extracts a `CodeEntry.Witness` from any
successful call of `metadata.validate_code_entry_with`, for either profile. The witness records the
actual visitor calls and parser results. Other executions of the visitor need not terminate.
`metadata.validate_code_entry_with.witness` is the Wasm 1.0 form.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- A successful `metadata.validate_code_entry_with` call gives a `CodeEntry.Witness` of its visitor
calls and parser results. Other executions of the visitor need not terminate. -/
theorem metadata.validate_code_entry_with.witness_profile {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (pos : Usize) (env : metadata.Env) (index finish : Usize)
    (v v' : V) (hbound : CodeEntry.Bounds env)
    (h : metadata.validate_code_entry_with visitor data pos env index v = .ok (.Ok finish, v')) :
    Nonempty (CodeEntry.Witness visitor data env index pos finish v v' ) := by
  unfold metadata.validate_code_entry_with at h
  dsimp only at h
  by_cases hi : index ≥ alloc.vec.Vec.len env.func_type_indices
  · simp [hi] at h
  rw [if_neg hi] at h
  have hindex : index.val < env.func_type_indices.val.length := by scalar_tac
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  rw [hr] at h
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from] at h
  | Ok pair =>
    obtain ⟨size, content⟩ := pair
    have hspan := hp.span
    simp [core.result.Result.Insts.CoreOpsTry.branch, lift] at h
    obtain ⟨r, hr, hh⟩ := WP.spec_imp_exists
      (metadata.have_bytes.spec data content (UScalar.cast .Usize size) hspan.2.2)
    rw [hr] at h
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
    | Ok u =>
      cases u
      have hbytes := hh.1.mp rfl
      obtain ⟨last, hlast, hlastval⟩ := WP.spec_imp_exists
        (UScalar.add_spec (x := content) (y := UScalar.cast .Usize size) (by scalar_tac))
      simp [hlast] at h
      obtain ⟨r, hr, hl⟩ := WP.spec_imp_exists (metadata.decode_locals.spec data content )
      rw [hr] at h
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      | Ok pair =>
        obtain ⟨declared, bodyStart⟩ := pair
        obtain ⟨groups, hg, hd, hcap⟩ := hl
        simp at h
        by_cases hbeyond : last.val < bodyStart.val
        · simp [hbeyond] at h
        rw [if_neg hbeyond] at h
        have hget : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32)
            env.func_type_indices index ⦃ idx => idx = env.func_type_indices.val[index.val] ⦄ := by
          step*
        obtain ⟨typeIdx, hget, htypeIdx⟩ := WP.spec_imp_exists hget
        have hget : env.func_type_indices.index_usize index = .ok typeIdx := by simpa using hget
        simp [hget] at h
        by_cases htype : env.types.val.length ≤ typeIdx.val
        · simp [htype] at h
        rw [if_neg htype] at h
        have htype_lt : typeIdx.val < env.types.val.length := by omega
        have hget : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice wasm_types.FuncType)
            env.types (UScalar.cast .Usize typeIdx) ⦃ ft => ft = env.types.val[typeIdx.val] ⦄ := by
          step*
        obtain ⟨ft, hget, hft⟩ := WP.spec_imp_exists hget
        have hget : env.types.index_usize (UScalar.cast .Usize typeIdx) = .ok ft := by simpa using hget
        simp only [hget, bind_ok] at h
        have hmem : ft ∈ env.types.val := by rw [hft]; exact List.getElem_mem _
        have hparams := hbound ft hmem
        obtain ⟨locals, hlocals, hlocalsval⟩ := WP.spec_imp_exists
          (metadata.build_func_locals.spec (alloc.vec.Vec.deref ft.params)
            (alloc.vec.Vec.deref declared) (by simpa [alloc.vec.Vec.deref] using (show
              ft.params.val.length + declared.val.length ≤ Usize.max from by omega)))
        obtain ⟨results, hresults, hresultsval⟩ := WP.spec_imp_exists
          (metadata.copy_value_types.spec (alloc.vec.Vec.deref ft.results))
        simp only [hlocals, hresults, bind_ok] at h
        obtain ⟨⟨reply, started⟩, hstart, ht⟩ := ResultFacts.bind_ok_inv _ _ _ h
        cases reply with
        | Err e => simp at ht
        | Ok u =>
          cases u
          all_goals
            try dsimp only at ht
            have hslice : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
                data ⟨bodyStart, last⟩ ⦃ body => body.val = data.val.slice bodyStart.val last.val ⦄ := by
              step*
            obtain ⟨body, hbody, hbodyval⟩ := WP.spec_imp_exists hslice
            have hbody : core.slice.index.SliceIndexRangeUsizeSlice.index
                ⟨bodyStart, last⟩ data = .ok body := by simpa using hbody
            simp [hbody, Std.bind_assoc] at ht
            obtain ⟨⟨reply, ended⟩, hrun, ht⟩ := ResultFacts.bind_ok_inv _ _ _ ht
            cases reply with
            | Err e => simp at ht
            | Ok u =>
              cases u
              have he : last = finish ∧ ended = v' := by simpa using ht
              obtain ⟨rfl, rfl⟩ := he
              refine ⟨{
                typeIdx := typeIdx, ft := ft, groups := groups, ctx := ⟨locals, results⟩
                content := content, bodyStart := bodyStart, body := body, size := size
                startedState := started, index_lt := hindex, index_type := htypeIdx.symm
                type_lt := htype_lt, function_type := hft.symm, header := hp
                extent := ?_, locals_bytes := hg, locals_bound := ?_
                context_locals := ?_, context_results := ?_, body_bytes := ?_
                function_start := hstart, body_accepted := hrun }⟩
              · scalar_tac
              · simpa [hd] using hcap
              · simpa [alloc.vec.Vec.deref, hd] using hlocalsval
              · simpa [alloc.vec.Vec.deref] using hresultsval
              · exact ModuleBinary.slice_bytes (by omega) (by scalar_tac) hbodyval

end Itasca

end

/-! ## ReachedEntry -/

section

namespace Itasca
open Aeneas Aeneas.Std
namespace CodeEntry

/-- Decoded entry metadata before the function-start callback. No body or callback acceptance is assumed. -/
structure Prepared (data : Slice U8) (env : metadata.Env) (index start : Usize)
     where
  finish : Usize
  typeIdx : U32
  ft : wasm_types.FuncType
  groups : List (U32 × wasm_types.ValueType)
  ctx : code.Context
  content : Usize
  bodyStart : Usize
  body : Slice U8
  size : U32
  index_lt : index.val < env.func_type_indices.val.length
  index_type : env.func_type_indices.val[index.val] = typeIdx
  type_lt : typeIdx.val < env.types.val.length
  function_type : env.types.val[typeIdx.val] = ft
  header : Leb128.Decoded data start size content
  extent : finish.val = content.val + size.val
  locals_bytes : ModuleBinary.At (ModuleBinary.VecEncoding ModuleBinary.LocalEncoding)
    data content groups bodyStart
  locals_bound : (ModuleLocals.declared groups).length ≤ limits.MAX_LOCALS.val
  context_locals : ctx.locals.val = ft.params.val ++ ModuleLocals.declared groups
  context_results : ctx.results.val = ft.results.val
  body_bytes : Wasm1.BytesAt data bodyStart body.val finish

end CodeEntry

/-- Entry parsing and local-vector construction return on malformed bytes.
Only the actual prepared function-start and body calls need normal-return proofs. -/
theorem metadata.validate_code_entry_with.total_on {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (pos : Usize) (env : metadata.Env) (index : Usize) (v : V)
    (hbound : CodeEntry.Bounds env)
    (start : ∀ prepared : CodeEntry.Prepared data env index pos ,
      visitor.on_function_start v prepared.ctx prepared.typeIdx prepared.bodyStart prepared.finish ⦃ _ => True ⦄)
    (bodyTotal : ∀ (prepared : CodeEntry.Prepared data env index pos ) started,
      visitor.on_function_start v prepared.ctx prepared.typeIdx prepared.bodyStart prepared.finish = .ok (.Ok (),started) →
      code.validate_body_with visitor prepared.body env prepared.ctx prepared.typeIdx started ⦃ _ => True ⦄) :
    metadata.validate_code_entry_with visitor data pos env index v ⦃ _ => True ⦄ := by
  unfold metadata.validate_code_entry_with
  dsimp only
  split
  · simp
  · rename_i hindex
    have hi : index.val < env.func_type_indices.val.length := by scalar_tac
    obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
    rw [hr]
    cases r with
    | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          error.Error.Insts.CoreConvertFromOpError.from]
    | Ok pair =>
        obtain ⟨size, content⟩ := pair
        have hs := hp.span
        simp [core.result.Result.Insts.CoreOpsTry.branch]
        step
        obtain ⟨r, hh, hhpost⟩ := WP.spec_imp_exists (metadata.have_bytes.spec data content n hs.2.2)
        rw [hh]
        cases r with
        | Err e =>
            simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok u =>
            cases u
            have hbytes := hhpost.1.mp rfl
            simp
            step
            obtain ⟨r, hl, hlpost⟩ := WP.spec_imp_exists (metadata.decode_locals.spec data content )
            rw [hl]
            cases r with
            | Err e =>
                simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok pair =>
                obtain ⟨declared, bodyStart⟩ := pair
                obtain ⟨groups, hg, hd, hcap⟩ := hlpost
                simp
                split
                · simp
                · rename_i hbodyStart
                  step
                  step
                  split
                  · simp
                  · rename_i htype
                    have hti : type_idx.val < env.types.val.length := by scalar_tac
                    step
                    have hftmem : ft ∈ env.types.val := by
                      rw [ft_post]
                      exact List.getElem_mem _
                    have hparams := hbound ft hftmem
                    have hroom : ft.params.val.length + declared.val.length ≤ Usize.max := by omega
                    obtain ⟨v1, hv1, v1_post⟩ := WP.spec_imp_exists
                      (metadata.build_func_locals.spec (alloc.vec.Vec.deref ft.params)
                        (alloc.vec.Vec.deref declared) (by simpa [alloc.vec.Vec.deref] using hroom))
                    obtain ⟨v2, hv2, v2_post⟩ := WP.spec_imp_exists
                      (metadata.copy_value_types.spec (alloc.vec.Vec.deref ft.results))
                    rw [hv1]
                    simp only [bind_ok]
                    rw [hv2]
                    simp only [bind_ok]
                    have hslice : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
                        data ⟨bodyStart, «end»⟩ ⦃ body => body.val = data.val.slice bodyStart.val «end».val ⦄ := by
                      step*
                    obtain ⟨body,sliced,bodyValue⟩ := WP.spec_imp_exists hslice
                    have sliced : core.slice.index.SliceIndexRangeUsizeSlice.index
                        ⟨bodyStart,«end»⟩ data = .ok body := by simpa using sliced
                    let prepared : CodeEntry.Prepared data env index pos := {
                      finish := «end», typeIdx := type_idx, ft := ft, groups := groups, ctx := ⟨v1,v2⟩
                      content := content, bodyStart := bodyStart, body := body, size := size
                      index_lt := hi, index_type := type_idx_post.symm, type_lt := hti
                      function_type := by simpa [t_post] using ft_post.symm
                      header := hp, extent := by scalar_tac, locals_bytes := hg
                      locals_bound := by simpa [hd] using hcap
                      context_locals := by simpa [alloc.vec.Vec.deref,hd] using v1_post
                      context_results := by simpa [alloc.vec.Vec.deref] using v2_post
                      body_bytes := ModuleBinary.slice_bytes (by scalar_tac) (by scalar_tac) bodyValue }
                    obtain ⟨⟨reply,started⟩,hstart,_⟩ := WP.spec_imp_exists (start prepared)
                    dsimp only [prepared] at hstart
                    rw [hstart]
                    cases reply with
                    | Err error => simp
                    | Ok acceptedUnit =>
                      cases acceptedUnit
                      obtain ⟨⟨reply,ended⟩,run,_⟩ := WP.spec_imp_exists (bodyTotal prepared started hstart)
                      dsimp only [prepared] at run
                      simp only [bind_ok,sliced]
                      simp only [Std.bind_assoc,Std.uncurry,bind_ok]
                      rw [run]
                      cases reply <;> simp

end Itasca

end

/-! ## Framing -/

section

/-!
# Code entry framing

Specification of `metadata.code_entry_extent`, which reads a code entry's declared size and returns
the content start and entry end. `metadata.code_entry_extent.spec` gives `ModuleCode.Extent` on
success, `metadata.code_entry_extent.complete` shows it accepts any entry with such an extent, and
`metadata.code_entry_extent.frames` shows a successful `metadata.validate_code_entry` ends at the
same boundary.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- `metadata.code_entry_extent` returns an `Extent` of the entry on success. -/
@[step]
theorem metadata.code_entry_extent.spec (data : Slice U8) (pos : Usize) :
    metadata.code_entry_extent data pos ⦃ r => match r with
      | .Ok (content, finish) => ModuleCode.Extent data pos content finish
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  rw [metadata.code_entry_extent, hr]
  cases r with
  | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
      obtain ⟨size, content⟩ := pair
      have hs := hp.span
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      step
      obtain ⟨r, hh, hhpost⟩ := WP.spec_imp_exists (metadata.have_bytes.spec data content n hs.2.2)
      rw [hh]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok u =>
          cases u
          have hb := hhpost.1.mp rfl
          simp
          step
          exact ⟨size, hp, by scalar_tac, by scalar_tac⟩

/-- `metadata.code_entry_extent` returns the content start and end of any entry with that `Extent`. -/
theorem metadata.code_entry_extent.complete (data : Slice U8) (pos first next : Usize)
    (h : ModuleCode.Extent data pos first next) :
    metadata.code_entry_extent data pos = .ok (.Ok (first, next)) := by
  obtain ⟨count, hc, hn, hb⟩ := h
  have hs : metadata.code_entry_extent data pos ⦃ r => r = .Ok (first, next) ⦄ := by
    simp [metadata.code_entry_extent, reader.read_u32_leb.complete data pos count first hc,
      core.result.Result.Insts.CoreOpsTry.branch]
    step
    rw [metadata.have_bytes.complete data first n (by scalar_tac)]
    simp only [bind_ok]
    step*
    congr 3
    apply UScalar.eq_of_val_eq
    scalar_tac
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hs
  exact hr

end Itasca

end
