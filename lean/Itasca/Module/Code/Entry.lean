import Itasca.Binary.Wasm1.DeclaredReferences
import Itasca.Module.Code.Context
import Itasca.Module.Code.Encoding
import Itasca.Contracts
import Itasca.Visitor.Total

/-!
# Code entry validation

Soundness of `module.validate_code_entry` and `module.validate_code_entry_with`. For any visitor
with total callbacks they terminate, and `module.validate_code_entry_with.pipeline_of_body_total`
decomposes a successful call into a `CodeEntry.Witness`. `Witness.validated` discharges the body
call with the body soundness theorem to give `CodeEntry.Validated`, an independent `CodeEncoding`
and a `Typed` certificate. `module.validate_code_entry.spec` is the resulting Wasm 1.0 statement.
-/

open Aeneas Aeneas.Std

namespace Itasca.CodeEntry

/-- The data of a successful run of the entry validator at `index`, from `start` to `finish`. It
records the size header, the locals bytes and bound, the context handed to the visitor, the
function-start callback and the body validation on the body slice. -/
structure Witness {V : Type} (visitor : code.OpVisitor V) (data : Slice U8)
    (env : module.Env) (index start finish : Usize) (v v' : V)
    (profile : ValidationProfile) where
  typeIdx : U32
  ft : types.FuncType
  groups : List (U32 × types.ValueType)
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
  locals_allowed : ∀ group ∈ groups, ModuleBinary.ValueTypeAllowed profile group.2
  context_locals : ctx.locals.val = ft.params.val ++ ModuleLocals.declared groups
  context_results : ctx.results.val = ft.results.val
  body_bytes : Wasm1.BytesAt data bodyStart body.val finish
  function_start : visitor.on_function_start v ctx typeIdx bodyStart finish = .ok (.Ok (), startedState)
  body_accepted : code.validate_body_with visitor body env ctx typeIdx profile startedState =
    .ok (.Ok (), v')

/-- Parameter counts bounded by the maximum module size give `Bounds`. -/
theorem Bounds.of_module_bound (env : module.Env)
    (h : ∀ ft ∈ env.types.val, ft.params.val.length ≤ limits.MAX_MODULE_BYTES.val) : Bounds env := by
  intro ft hm
  have := h ft hm
  have hcap : limits.MAX_MODULE_BYTES.val + limits.MAX_LOCALS.val ≤ Usize.max := by
    simp only [limits.MAX_MODULE_BYTES, limits.MAX_LOCALS]
    scalar_tac
  omega

end CodeEntry

/-- Given a body operation that terminates, `module.validate_code_entry_with` terminates and each
successful call has a `CodeEntry.Witness`. Rejecting callbacks are ordinary module errors. -/
theorem module.validate_code_entry_with.pipeline_of_body_total {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (data : Slice U8) (pos : Usize)
    (env : module.Env) (index : Usize) (v : V) (hbound : CodeEntry.Bounds env)
    (profile : ValidationProfile)
    (hbody : ∀ body ctx typeIdx started,
      ∃ r, code.validate_body_with visitor body env ctx typeIdx profile started = .ok r) :
    module.validate_code_entry_with visitor data pos env index profile v ⦃ r =>
      ∀ finish, r.1 = .Ok finish →
        Nonempty (CodeEntry.Witness visitor data env index pos finish v r.2 profile) ⦄ := by
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
                              locals_bytes := hg, locals_bound := ?_, locals_allowed := hallowed, context_locals := ?_
                              context_results := ?_, body_bytes := ?_, function_start := hstart
                              body_accepted := hb }⟩
                            · simpa [t_post] using ft_post.symm
                            · scalar_tac
                            · simpa [hd] using hcap
                            · simpa [alloc.vec.Vec.deref, hd] using v1_post
                            · simpa [alloc.vec.Vec.deref] using v2_post
                            · exact ModuleBinary.slice_bytes (by scalar_tac) (by scalar_tac) s3_post

end Itasca
