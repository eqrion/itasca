import Itasca.Binary.Wasm1.DeclaredReferences
import Itasca.Module.Code.Context
import Itasca.Module.Code.Encoding
import Itasca.Wasm1.ProfileSoundness
import Itasca.Profile.BodyExecution

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

/-- Parameters plus the maximum local count fit in a `Usize` for every function type. The
environment decoder supplies this. The validator accepts arbitrary environments, but concatenating
parameters and locals cannot be total for a caller-built vector already at machine capacity. -/
def Bounds (env : module.Env) : Prop :=
  ∀ ft ∈ env.types.val, ft.params.val.length + limits.MAX_LOCALS.val ≤ Usize.max

/-- The data of a successful run of the entry validator at `index`, from `start` to `finish`. It
records the size header, the locals bytes and bound, the context handed to the visitor, the
function-start callback and the body validation on the body slice. -/
structure Witness {V : Type} (visitor : code.OpVisitor V) (data : Slice U8)
    (env : module.Env) (index start finish : Usize) (v v' : V)
    (profile : ValidationProfile := .Wasm1) where
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
  body_accepted : runBody visitor profile body env ctx typeIdx startedState = .ok (.Ok (), v')

/-- Entry `index` of the code section has an independent `CodeEncoding` from `start` to `finish`
and a `Typed` certificate within the local bound. This is the form used for code-section
composition and has no validation-call premise. -/
def Validated (data : Slice U8) (env : module.Env) (index start finish : Usize) : Prop :=
  ∃ entry, ModuleBinary.At ModuleBinary.CodeEncoding data start entry finish ∧
    ∃ hi : index.val < env.func_type_indices.val.length,
      Typed env env.func_type_indices.val[index.val] entry ∧
      entry.declared.length ≤ limits.MAX_LOCALS.val

/-- A result list of length at most one is the results of some block type. -/
theorem blockType_of_length (results : List types.ValueType) (h : results.length ≤ 1) :
    ∃ bt, results = Control.results bt := by
  cases results with
  | nil => exact ⟨.Empty, rfl⟩
  | cons t rest =>
    cases rest with
    | nil => exact ⟨.Value t, rfl⟩
    | cons t' rest => simp at h

/-- A `Witness` gives a `Validated` entry. The body soundness theorem discharges the body call, and
the same instruction tree appears in the entry's byte encoding and typing certificate. -/
theorem Witness.validated {V : Type} {visitor : code.OpVisitor V} {data env index start finish v v'}
    (w : Witness visitor data env index start finish v v')
    (hresults : ∀ ft ∈ env.types.val, ft.results.val.length ≤ 1) :
    Validated data env index start finish := by
  have hftmem : w.ft ∈ env.types.val := by
    rw [← w.function_type]
    exact List.getElem_mem _
  obtain ⟨bt, hbt⟩ := blockType_of_length w.ft.results.val (hresults _ hftmem)
  have hr : w.ctx.results.val = Control.results bt := w.context_results.trans hbt
  obtain ⟨ops, hbytes, htyped, hprofile⟩ := code.validate_body_with.wasm1_sound visitor
    w.body env w.ctx bt hr w.startedState v' w.body_accepted
  refine ⟨⟨w.groups, ops⟩, ModuleBinary.codeEncoding_of_parts w.header w.extent
    w.locals_bytes w.body_bytes hbytes, w.index_lt, ?_, w.locals_bound⟩
  rw [w.index_type]
  refine ⟨w.type_lt, ?_, ?_, w.locals_allowed, hbytes.declared _⟩
  · rw [w.function_type]
    unfold Wasm1.FunctionTyped at htyped
    rw [body_context w.context_locals w.context_results hbt] at htyped
    simpa only [instructionType, Control.resultTypes, ← hbt, ModuleBinary.Code.declared,
      ModuleLocals.declared] using htyped
  · rw [w.function_type]
    rw [body_context w.context_locals w.context_results hbt] at hprofile
    exact hprofile

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
      ∃ r, CodeEntry.runBody visitor profile body env ctx typeIdx started = .ok r) :
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
                        cases profile
                        all_goals
                          simp only [CodeEntry.runBody] at hbody
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

/-- `module.validate_code_entry_with.pipeline_of_body_total` for Wasm 1.0. Only the body operation
depends on the selected profile. -/
theorem module.validate_code_entry_with.pipeline {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (data : Slice U8) (pos : Usize)
    (env : module.Env) (index : Usize) (v : V) (hbound : CodeEntry.Bounds env) :
    module.validate_code_entry_with visitor data pos env index .Wasm1 v ⦃ r =>
      ∀ finish, r.1 = .Ok finish → Nonempty (CodeEntry.Witness visitor data env index pos finish v r.2) ⦄ :=
  module.validate_code_entry_with.pipeline_of_body_total visitor hvisitor data pos env index v hbound
    .Wasm1 (fun body ctx _ started => code.validate_body_with.wasm_total visitor hvisitor body env ctx started)

/-- A successful Wasm 1.0 `module.validate_code_entry_with` call yields a `Validated` entry. -/
theorem module.validate_code_entry_with.spec {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (data : Slice U8) (pos : Usize)
    (env : module.Env) (index : Usize) (v : V) (hbound : CodeEntry.Bounds env)
    (hresults : ∀ ft ∈ env.types.val, ft.results.val.length ≤ 1) :
    module.validate_code_entry_with visitor data pos env index .Wasm1 v ⦃ r =>
      ∀ finish, r.1 = .Ok finish → CodeEntry.Validated data env index pos finish ⦄ := by
  apply WP.spec_mono (module.validate_code_entry_with.pipeline visitor hvisitor data pos env index v hbound)
  intro r h finish he
  obtain ⟨w⟩ := h finish he
  exact w.validated hresults

/-- Wasm 1.0 `module.validate_code_entry_with` terminates. -/
theorem module.validate_code_entry_with.total {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (data : Slice U8) (pos : Usize)
    (env : module.Env) (index : Usize) (v : V) (hbound : CodeEntry.Bounds env) :
    ∃ r, module.validate_code_entry_with visitor data pos env index .Wasm1 v = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists
    (module.validate_code_entry_with.pipeline visitor hvisitor data pos env index v hbound)
  exact ⟨r, hr⟩

/-- A successful Wasm 1.0 `module.validate_code_entry` call yields a `Validated` entry. -/
theorem module.validate_code_entry.spec (data : Slice U8) (pos : Usize)
    (env : module.Env) (index : Usize) (hbound : CodeEntry.Bounds env)
    (hresults : ∀ ft ∈ env.types.val, ft.results.val.length ≤ 1) :
    module.validate_code_entry data pos env index .Wasm1 ⦃ r =>
      ∀ finish, r = .Ok finish → CodeEntry.Validated data env index pos finish ⦄ := by
  obtain ⟨⟨r, v⟩, hr, hp⟩ := WP.spec_imp_exists (module.validate_code_entry_with.spec
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_total data pos env index () hbound hresults)
  simpa [module.validate_code_entry, hr] using hp

/-- Wasm 1.0 `module.validate_code_entry` terminates. -/
theorem module.validate_code_entry.total (data : Slice U8) (pos : Usize)
    (env : module.Env) (index : Usize) (hbound : CodeEntry.Bounds env) :
    ∃ r, module.validate_code_entry data pos env index .Wasm1 = .ok r := by
  obtain ⟨⟨r, v⟩, hr⟩ := module.validate_code_entry_with.total
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_total data pos env index () hbound
  exact ⟨r, by simp [module.validate_code_entry, hr]⟩

end Itasca
