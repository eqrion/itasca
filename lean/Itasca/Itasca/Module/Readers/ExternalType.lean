import Itasca.Module.CodeMetadata
import Itasca.Module.Readers.Syntax
import Mathlib.Data.List.Forall2

/-! External types resolved from the four Wasm index spaces. -/

open Aeneas Aeneas.Std

namespace Itasca.metadata.CodeMetadata

/-- Resolve a Wasm external index in the retained descriptors. A function requires
both the function index and the descriptor's type index to be in bounds. -/
def externalTypeAt (env : CodeMetadata) : ExportDesc → Option wasm_types.ExternType
  | .Func i => do
    let d ← env.funcs.val[i.val]?
    let ft ← env.types.val[d.type_index.val]?
    return .Func ft
  | .Table i => env.tables.val[i.val]?.map (fun d => .Table d.ty)
  | .Memory i => env.memories.val[i.val]?.map (fun d => .Memory d.ty)
  | .Global i => env.globals.val[i.val]?.map (fun d => .Global d.gtype)

/-- A descriptor lookup always returns. Success yields exactly the external type
at that index, and a missing descriptor yields a Rust error. -/
@[step] theorem extern_type.spec (env : CodeMetadata) (desc : ExportDesc) :
    env.extern_type desc ⦃ r => (match r with
      | .Ok xt => some xt
      | .Err _ => none) = externalTypeAt env desc ⦄ := by
  cases desc with
  | Func idx =>
    obtain ⟨o, ho, post⟩ := WP.spec_imp_exists (func_type.spec env idx)
    simp only [extern_type, ho, bind_ok]
    cases h : env.funcs.val[idx.val]? with
    | none =>
      simp [h] at post
      simp [post, externalTypeAt, h, core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | some fd =>
      simp [h] at post
      cases ht : env.types.val[fd.type_index.val]? with
      | none =>
        simp [post, ht, h, externalTypeAt, core.option.Option.ok_or,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | some ft =>
        obtain ⟨_, hc, rfl⟩ := WP.spec_imp_exists (metadata.copy_func_type.spec ft)
        simp [post, ht, h, externalTypeAt, core.option.Option.ok_or,
          core.result.Result.Insts.CoreOpsTry.branch, hc]
  | Table idx | Memory idx | Global idx =>
    unfold extern_type externalTypeAt
    step* <;> simp_all <;> simp (disch := scalar_tac) [List.getElem?_eq_getElem, List.getElem?_eq_none]

end Itasca.metadata.CodeMetadata

namespace Itasca.Module.Externals

/-- The external type of a named export is determined solely by its descriptor. -/
def ExportResolves (env : metadata.CodeMetadata) (e : metadata.Export) (xt : wasm_types.ExternType) : Prop :=
  env.externalTypeAt e.desc = some xt

end Itasca.Module.Externals

namespace Itasca.metadata.ModuleMetadataArcCodeMetadata

/-- The export loop preserves order as it appends each resolved external type. -/
theorem export_types_loop.resolved (env : ModuleMetadata (alloc.sync.Arc CodeMetadata))
    (expected : List wasm_types.ExternType)
    (hresolve : List.Forall₂ (Module.Externals.ExportResolves env.code) env.exports.val expected)
    (out : alloc.vec.Vec wasm_types.ExternType) (i : Usize)
    (hi : i.val ≤ expected.length) (hout : out.val = expected.take i.val) :
    export_types_loop env out i ⦃ r => ∃ result, r = .Ok result ∧ result.val = expected ⦄ := by
  have hlen := hresolve.length_eq
  have hbound : expected.length ≤ Usize.max := by rw [← hlen]; scalar_tac
  unfold export_types_loop
  apply loop.spec_decr_nat (fun p => expected.length - p.2.val)
    (fun p => p.2.val ≤ expected.length ∧ p.1.val = expected.take p.2.val)
  · rintro ⟨v, j⟩ ⟨hj, hv⟩
    dsimp only at hj hv
    simp only [export_types_loop.body, alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, bind_ok]
    split
    · have hlt : j.val < env.exports.val.length := by scalar_tac
      have hlt' : j.val < expected.length := by omega
      have hcapacity : v.val.length < Usize.max := by
        simp only [hv, List.length_take, Nat.min_eq_left hj]
        omega
      have he := hresolve.get hlt hlt'
      change env.code.externalTypeAt env.exports.val[j.val].desc = some expected[j.val] at he
      step as ⟨e, heq⟩
      rw [heq]
      step as ⟨r, hr⟩
      rw [he] at hr
      cases r with
      | Err err => contradiction
      | Ok xt =>
        cases Option.some.inj hr
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step as ⟨out', hpush⟩
        step as ⟨next, hnext⟩
        refine ⟨by omega, ?_, by omega⟩
        rw [hpush, hnext, hv, List.take_succ_eq_append_getElem hlt']
    · have he : j.val = expected.length := by scalar_tac
      exact ⟨v, rfl, by simpa [he] using hv⟩
  · exact ⟨hi, hout⟩

/-- The export accessor returns all resolved types in export section order. -/
theorem export_types.resolved (env : ModuleMetadata (alloc.sync.Arc CodeMetadata))
    (expected : List wasm_types.ExternType)
    (hresolve : List.Forall₂ (Module.Externals.ExportResolves env.code) env.exports.val expected) :
    export_types env ⦃ r => ∃ result, r = .Ok result ∧ result.val = expected ⦄ := by
  simpa [export_types] using export_types_loop.resolved env expected hresolve
    (alloc.vec.Vec.new _) 0#usize (by simp) (by simp)

end Itasca.metadata.ModuleMetadataArcCodeMetadata
