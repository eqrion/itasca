import ItascaRust.Funs
import Itasca.Results.Definitions.Foundations

/-! Contracts for descriptor lookups shared by body validation and module reflection. -/

open Aeneas Aeneas.Std

namespace Itasca.metadata.CodeMetadata

/-- Resolve both Wasm index spaces, returning `none` for either failed lookup. -/
@[step] theorem func_type.spec (env : CodeMetadata) (idx : U32) :
    env.func_type idx ⦃ r => r = env.funcs.val[idx.val]?.bind
      (fun d => env.types.val[d.type_index.val]?) ⦄ := by
  unfold func_type
  step* <;> simp_all <;> simp (disch := scalar_tac) [List.getElem?_eq_getElem, List.getElem?_eq_none]

/-- Out-of-bounds functions cannot be referenced. -/
@[step] theorem declares_function.spec (env : CodeMetadata) (idx : U32) :
    env.declares_function idx ⦃ r => r =
      ((env.funcs.val[idx.val]?).map FuncDesc.can_ref_func).getD false ⦄ := by
  unfold declares_function
  step* <;> simp_all <;> simp (disch := scalar_tac) [List.getElem?_eq_getElem, List.getElem?_eq_none]

/-- Count the definitions following the import prefix. -/
@[step] theorem num_func_defs.spec (env : CodeMetadata)
    (h : env.num_imported_funcs.val ≤ env.funcs.val.length) :
    env.num_func_defs ⦃ n => n.val = env.funcs.val.length - env.num_imported_funcs.val ⦄ := by
  unfold num_func_defs
  step*

end Itasca.metadata.CodeMetadata

namespace Itasca

/-- Publishing the prefix preserves the code declarations and all module payloads. -/
@[step] theorem metadata.ModuleMetadataCodeMetadata.share.spec
    (decoded : metadata.ModuleMetadata metadata.CodeMetadata) :
    metadata.ModuleMetadataCodeMetadata.share decoded ⦃ published => published = decoded ⦄ := by
  cases decoded
  simp [metadata.ModuleMetadataCodeMetadata.share, alloc.sync.Arc.new]

/-- Every issued batch observes the same immutable code declarations. -/
@[step] theorem stream.share_code.spec (code : alloc.sync.Arc metadata.CodeMetadata) :
    stream.share_code code ⦃ shared => shared = code ⦄ := by simp [stream.share_code]

end Itasca

namespace Itasca.Translation.Environment

/-- A descriptor contributes its own Wasm function index precisely when flagged. -/
theorem mem_declaredReferences {env : metadata.CodeMetadata} {i : Nat} :
    WebAssembly.uN.mk_uN i ∈ declaredReferences env ↔
      ∃ d, env.funcs.val[i]? = some d ∧ d.can_ref_func = true := by
  simp only [declaredReferences, List.mem_filterMap]
  constructor
  · rintro ⟨⟨d, j⟩, hm, he⟩
    cases h : d.can_ref_func <;> simp [h] at he
    subst j
    exact ⟨d, List.mk_mem_zipIdx_iff_getElem?.mp hm, h⟩
  · rintro ⟨d, hd, flag⟩
    exact ⟨(d, i), List.mk_mem_zipIdx_iff_getElem?.mpr hd, by simp [flag]⟩

end Itasca.Translation.Environment

namespace Itasca.metadata.CodeMetadata

/-- The validator's declaration test decides membership in the Wasm reference context. -/
theorem declares_function.eq (env : CodeMetadata) (index : U32) :
    env.declares_function index = .ok (decide (WebAssembly.uN.mk_uN index.val ∈
      Translation.Environment.declaredReferences env)) := by
  obtain ⟨b, hb, rfl⟩ := WP.spec_imp_exists (declares_function.spec env index)
  rw [hb]
  congr 1
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff, Translation.Environment.mem_declaredReferences]
  cases h : env.funcs.val[index.val]? <;> simp

end Itasca.metadata.CodeMetadata

namespace Itasca.Translation.Environment

/-- A definition index skips the imported-function prefix in the descriptor vector. -/
theorem defined_descriptor (env : metadata.CodeMetadata) (i : Usize)
    (hi : i.val < (definedTypeIndices env).length) :
    ∃ (absolute : Usize) (fd : metadata.FuncDesc), (env.num_imported_funcs + i : Result Usize) = .ok absolute ∧
      env.funcs.index_usize absolute = .ok fd ∧ fd.type_index = (definedTypeIndices env)[i.val] := by
  have hlen : i.val < env.funcs.val.length - env.num_imported_funcs.val := by
    simpa [definedTypeIndices] using hi
  have hsum : env.num_imported_funcs.val + i.val < env.funcs.val.length := by omega
  obtain ⟨absolute, hsumOp, habs⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x := env.num_imported_funcs) (y := i) (by scalar_tac))
  obtain ⟨fd, hget, he⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec env.funcs absolute (by scalar_tac))
  exact ⟨absolute, fd, hsumOp, hget, by simp [he, definedTypeIndices, List.getElem_drop, habs]⟩

end Itasca.Translation.Environment
