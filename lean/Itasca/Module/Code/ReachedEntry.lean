import Itasca.Module.Code.Entry

namespace Itasca
open Aeneas Aeneas.Std
namespace CodeEntry

/-- Decoded entry metadata before the function-start callback. No body or callback acceptance is assumed. -/
structure Prepared (data : Slice U8) (env : module.Env) (index start : Usize)
    (profile : ValidationProfile) where
  finish : Usize
  typeIdx : U32
  ft : types.FuncType
  groups : List (U32 × types.ValueType)
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
  locals_allowed : ∀ group ∈ groups, ModuleBinary.ValueTypeAllowed profile group.2
  context_locals : ctx.locals.val = ft.params.val ++ ModuleLocals.declared groups
  context_results : ctx.results.val = ft.results.val
  body_bytes : Wasm1.BytesAt data bodyStart body.val finish

end CodeEntry

/-- Entry parsing and local-vector construction return on malformed bytes.
Only the actual prepared function-start and body calls need normal-return proofs. -/
theorem module.validate_code_entry_with.total_on {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (pos : Usize) (env : module.Env) (index : Usize) (v : V)
    (hbound : CodeEntry.Bounds env) (profile : ValidationProfile)
    (start : ∀ prepared : CodeEntry.Prepared data env index pos profile,
      visitor.on_function_start v prepared.ctx prepared.typeIdx prepared.bodyStart prepared.finish ⦃ _ => True ⦄)
    (bodyTotal : ∀ (prepared : CodeEntry.Prepared data env index pos profile) started,
      visitor.on_function_start v prepared.ctx prepared.typeIdx prepared.bodyStart prepared.finish = .ok (.Ok (),started) →
      CodeEntry.runBody visitor profile prepared.body env prepared.ctx prepared.typeIdx started ⦃ _ => True ⦄) :
    module.validate_code_entry_with visitor data pos env index profile v ⦃ _ => True ⦄ := by
  unfold module.validate_code_entry_with
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
        obtain ⟨r, hh, hhpost⟩ := WP.spec_imp_exists (module.have_bytes.spec data content n hs.2.2)
        rw [hh]
        cases r with
        | Err e =>
            simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok u =>
            cases u
            have hbytes := hhpost.1.mp rfl
            simp
            step
            obtain ⟨r, hl, hlpost⟩ := WP.spec_imp_exists (module.decode_locals.spec data content profile)
            rw [hl]
            cases r with
            | Err e =>
                simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok pair =>
                obtain ⟨declared, bodyStart⟩ := pair
                obtain ⟨groups, hg, hd, hcap, hallowed⟩ := hlpost
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
                      (module.build_func_locals.spec (alloc.vec.Vec.deref ft.params)
                        (alloc.vec.Vec.deref declared) (by simpa [alloc.vec.Vec.deref] using hroom))
                    obtain ⟨v2, hv2, v2_post⟩ := WP.spec_imp_exists
                      (module.copy_value_types.spec (alloc.vec.Vec.deref ft.results))
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
                    let prepared : CodeEntry.Prepared data env index pos profile := {
                      finish := «end», typeIdx := type_idx, ft := ft, groups := groups, ctx := ⟨v1,v2⟩
                      content := content, bodyStart := bodyStart, body := body, size := size
                      index_lt := hi, index_type := type_idx_post.symm, type_lt := hti
                      function_type := by simpa [t_post] using ft_post.symm
                      header := hp, extent := by scalar_tac, locals_bytes := hg
                      locals_bound := by simpa [hd] using hcap
                      locals_allowed := hallowed
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
                      cases profile <;> simp only [CodeEntry.runBody] at run
                      all_goals
                        simp only [bind_ok,sliced]
                        simp only [Std.bind_assoc,Std.uncurry,bind_ok]
                        rw [run]
                        cases reply <;> simp

end Itasca
