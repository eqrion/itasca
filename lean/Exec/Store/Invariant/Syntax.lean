import Exec.Representation.StoreInvariant

/-! Syntactic well-formedness of the decoded store. The named source certificates
below are supplied by compilation: export-name syntax and source function syntax.
They contain no execution-correctness premise. `wf_store` is SpecTec syntax;
it is deliberately distinct from the semantic typing judgment `Store_ok`. -/
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Source syntax attached to one compiled instance and its ghost source bodies. -/
structure InstanceSyntax (code : CodeInterpretation) (index : Nat)
    (inst : runtime.store.ModuleInst) : Prop where
  exportNames : ∀ entry ∈ inst.module.module.env.exports.val,
    wf_name (decodeName entry.name.val)
  functionCodes : ∀ function, function < inst.module.module.env.func_type_indices.length →
    wf_funccode (code index inst.module function)

/-- Each retained instance carries its independently checked source syntax. -/
def StoreSyntax {M : Type} (code : CodeInterpretation) (s : runtime.store.Store M) : Prop :=
  ∀ index inst, s.instances.val[index]? = some inst → InstanceSyntax code index inst

theorem decodeWords_wf (ty : Itasca.types.ValueType) (lo hi : U64) :
    wf_val (decodeWords ty lo hi) := by
  cases ty with
  | I32 =>
    apply wf_val.val_case_0
    apply wf_num_.num__case_0 .I32 .I32 _ (by decide) ?_ rfl
    apply wf_uN.uN_case_0
    change 0 ≤ lo.val % 2^32 ∧ lo.val % 2^32 ≤ 4294967295
    have h := Nat.mod_lt lo.val (by decide : 0 < 2^32)
    omega
  | I64 =>
    apply wf_val.val_case_0
    apply wf_num_.num__case_0 .I64 .I64 _ (by decide) ?_ rfl
    apply wf_uN.uN_case_0
    change 0 ≤ lo.val ∧ lo.val ≤ 18446744073709551615
    scalar_tac
  | F32 =>
    apply wf_val.val_case_0
    exact .num__case_1 _ _ _ (SpecExt.Builtins.Float.floatOfBits_wf_32 _ (Nat.mod_lt _ (by decide))) rfl
  | F64 =>
    apply wf_val.val_case_0
    exact .num__case_1 _ _ _ (SpecExt.Builtins.Float.floatOfBits_wf_64 lo.val (by scalar_tac)) rfl
  | V128 =>
    apply wf_val.val_case_1 _ _ (by decide)
    apply wf_uN.uN_case_0
    change 0 ≤ lo.val + hi.val * 2^64 ∧ lo.val + hi.val * 2^64 ≤ 340282366920938463463374607431768211455
    scalar_tac
  | FuncRef =>
    simp only [decodeWords, decodeRef]
    split <;> constructor
  | ExternRef =>
    simp only [decodeWords, decodeRef]
    split <;> constructor

theorem decodeLimits_wf (length : Nat) (maximum : Option U32) (h : length ≤ U32.max) :
    wf_limits (decodeLimits length maximum) := by
  apply wf_limits.limits_case_0
  · apply wf_uN.uN_case_0
    change 0 ≤ length ∧ length ≤ 4294967295
    scalar_tac
  · cases maximum with
    | none => simp [Forall]
    | some bound =>
      intro value hvalue
      simp only [Option.map_some, Option.toList_some, List.mem_singleton] at hvalue
      subst value
      apply wf_uN.uN_case_0
      change 0 ≤ bound.val ∧ bound.val ≤ 4294967295
      scalar_tac

theorem decodeBytes_wf (bytes : List U8) : Forall wf_byte (decodeBytes bytes) := by
  intro value hvalue
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hvalue
  apply wf_byte.byte_case_0
  scalar_tac

theorem decodeInstance_wf {M : Type} (code : CodeInterpretation) (index : Nat)
    (s : runtime.store.Store M) (inst : runtime.store.ModuleInst) (h : InstanceSyntax code index inst) :
    wf_moduleinst (decodeInstance s inst) := by
  constructor
  intro entry hentry
  obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hentry
  unfold decodeExport
  exact .exportinst_case_ _ _ (h.exportNames raw hraw)

theorem decodeFunction_wf {M : Type} (code : CodeInterpretation)
    (s : runtime.store.Store M) (hsyntax : StoreSyntax code s)
    (function : runtime.store.FuncInst) (hshape : FunctionShape s function) :
    wf_funcinst (decodeFunction code s function) := by
  unfold decodeFunction
  dsimp only
  cases hc : function.code with
  | Host identity =>
    constructor
    · constructor
      change Forall wf_exportinst []
      simp [Forall]
    · constructor
  | Wasm instanceIndex functionIndex =>
    have h := hshape.2
    simp only [hc] at h
    obtain ⟨inst, hinst, hfunction⟩ := h
    simp only [hinst]
    constructor
    · exact decodeInstance_wf code instanceIndex.val s inst (hsyntax _ _ hinst)
    · exact (hsyntax _ _ hinst).functionCodes functionIndex.val hfunction

/-- Structural representation bounds and source syntax establish SpecTec's
syntactic store well-formedness. This theorem does not assert `Store_ok`. -/
theorem decodeStore_wf {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (shape : Shape view s) (hsyntax : StoreSyntax code s) :
    wf_store (decodeStore view code s) := by
  constructor
  · intro function hfunction
    obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hfunction
    exact decodeFunction_wf code s hsyntax raw (shape.functions raw hraw)
  · intro global hglobal
    obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hglobal
    exact .globalinst_case_ _ _ (decodeWords_wf raw.ty.valtype raw.lo raw.hi)
  · intro table htable
    obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp htable
    apply wf_tableinst.tableinst_case_
    apply wf_tabletype.tabletype_case_0
    exact decodeLimits_wf _ _ (shape.tables raw hraw).1
  · intro memory hmemory
    obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hmemory
    apply wf_meminst.meminst_case_
    · apply wf_memtype.memtype_case_0
      apply decodeLimits_wf
      have h := (shape.memories raw hraw).2.1
      scalar_tac
    · exact decodeBytes_wf _
  · intro data hdata
    obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hdata
    exact .datainst_case_ _ (decodeBytes_wf _)

end Itasca.Runtime.Store
