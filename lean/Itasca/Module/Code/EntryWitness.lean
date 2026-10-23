import Itasca.Module.Code.Entry
import Itasca.Support.Result

/-!
# Code entry witnesses

`module.validate_code_entry_with.witness_profile` extracts a `CodeEntry.Witness` from any
successful call of `module.validate_code_entry_with`, for either profile. The witness records the
actual visitor calls and parser results. Other executions of the visitor need not terminate.
`module.validate_code_entry_with.witness` is the Wasm 1.0 form.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- A successful `module.validate_code_entry_with` call gives a `CodeEntry.Witness` of its visitor
calls and parser results. Other executions of the visitor need not terminate. -/
theorem module.validate_code_entry_with.witness_profile {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (pos : Usize) (env : module.Env) (index finish : Usize)
    (v v' : V) (hbound : CodeEntry.Bounds env) (profile : ValidationProfile)
    (h : module.validate_code_entry_with visitor data pos env index profile v = .ok (.Ok finish, v')) :
    Nonempty (CodeEntry.Witness visitor data env index pos finish v v' profile) := by
  unfold module.validate_code_entry_with at h
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
      (module.have_bytes.spec data content (UScalar.cast .Usize size) hspan.2.2)
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
      obtain ⟨r, hr, hl⟩ := WP.spec_imp_exists (module.decode_locals.spec data content profile)
      rw [hr] at h
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      | Ok pair =>
        obtain ⟨declared, bodyStart⟩ := pair
        obtain ⟨groups, hg, hd, hcap, hallowed⟩ := hl
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
        have hget : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice types.FuncType)
            env.types (UScalar.cast .Usize typeIdx) ⦃ ft => ft = env.types.val[typeIdx.val] ⦄ := by
          step*
        obtain ⟨ft, hget, hft⟩ := WP.spec_imp_exists hget
        have hget : env.types.index_usize (UScalar.cast .Usize typeIdx) = .ok ft := by simpa using hget
        simp only [hget, bind_ok] at h
        have hmem : ft ∈ env.types.val := by rw [hft]; exact List.getElem_mem _
        have hparams := hbound ft hmem
        obtain ⟨locals, hlocals, hlocalsval⟩ := WP.spec_imp_exists
          (module.build_func_locals.spec (alloc.vec.Vec.deref ft.params)
            (alloc.vec.Vec.deref declared) (by simpa [alloc.vec.Vec.deref] using (show
              ft.params.val.length + declared.val.length ≤ Usize.max from by omega)))
        obtain ⟨results, hresults, hresultsval⟩ := WP.spec_imp_exists
          (module.copy_value_types.spec (alloc.vec.Vec.deref ft.results))
        simp only [hlocals, hresults, bind_ok] at h
        obtain ⟨⟨reply, started⟩, hstart, ht⟩ := ResultFacts.bind_ok_inv _ _ _ h
        cases reply with
        | Err e => simp at ht
        | Ok u =>
          cases u
          cases profile
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
                extent := ?_, locals_bytes := hg, locals_bound := ?_, locals_allowed := hallowed
                context_locals := ?_, context_results := ?_, body_bytes := ?_
                function_start := hstart, body_accepted := hrun }⟩
              · scalar_tac
              · simpa [hd] using hcap
              · simpa [alloc.vec.Vec.deref, hd] using hlocalsval
              · simpa [alloc.vec.Vec.deref] using hresultsval
              · exact ModuleBinary.slice_bytes (by omega) (by scalar_tac) hbodyval

end Itasca
