import Exec.Code.Module.InitializerTotal
import Exec.Code.Local.Capacity.SegmentBound
import Itasca.Module.Elab.Metadata

namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ModuleBinary

private theorem leb_nonempty {bytes value} (h : Itasca.Leb128.Encoding bytes value) :
    1 ≤ bytes.length := by
  obtain ⟨before, last, rfl, _⟩ := h
  simp

private theorem const_nonempty {value bytes} (h : ConstEncoding value bytes) :
    1 ≤ bytes.length := by
  cases h <;> simp

private theorem rep_count {α : Type} {R : α → List U8 → Prop} {values bytes}
    (h : Rep R values bytes) (positive : ∀ value bytes, R value bytes → 1 ≤ bytes.length) :
    values.length ≤ bytes.length := by
  induction h with
  | nil => simp
  | cons hx _ ih =>
    have := positive _ _ hx
    simp only [List.length_cons, List.length_append]
    omega

private theorem vec_count {α : Type} {R : α → List U8 → Prop} {values bytes}
    (h : VecEncoding R values bytes) (positive : ∀ value bytes, R value bytes → 1 ≤ bytes.length) :
    values.length + 1 ≤ bytes.length := by
  obtain ⟨count, entries, hc, hr, rfl⟩ := h
  have := leb_nonempty hc
  have := rep_count hr positive
  simp only [List.length_append]
  omega

private theorem element_cost {profile entry bytes}
    (h : ElementEncodingFor profile entry bytes) : entry.init.length + 3 ≤ 3 * bytes.length := by
  cases profile with
  | Wasm1 =>
    obtain ⟨_, _, _, table, offset, entries, rfl, _, _, he, rfl⟩ := h
    have := vec_count he (fun _ _ h => leb_nonempty h)
    simp only [List.length_map, List.length_append]
    omega
  | Wasm2 =>
    cases h with
    | activeIndices _ _ he | passiveIndices _ he | explicitIndices _ _ _ he | declarativeIndices _ he =>
      have := vec_count he (fun _ _ h => leb_nonempty h)
      simp only [List.length_map, List.length_append, List.length_singleton]
      omega
    | activeExpressions _ _ he | passiveExpressions _ he | explicitExpressions _ _ _ he | declarativeExpressions _ he =>
      have := vec_count he (fun _ _ h => const_nonempty h)
      simp only [List.length_append, List.length_singleton]
      omega

private theorem global_cost {entry bytes} (h : GlobalEncoding entry bytes) : 2 ≤ 3 * bytes.length := by
  obtain ⟨ty, expr, rfl, _, rfl⟩ := h
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

private theorem data_cost {profile entry bytes}
    (h : DataEncodingFor profile entry bytes) : 2 ≤ 3 * bytes.length := by
  have vec_positive {α : Type} {R : α → List U8 → Prop} {values bytes}
      (h : VecEncoding R values bytes) : 1 ≤ bytes.length := by
    obtain ⟨count, entries, hc, _, rfl⟩ := h
    have := leb_nonempty hc
    simp only [List.length_append]
    omega
  cases profile with
  | Wasm1 =>
    obtain ⟨_, _, memory, offset, entries, _, _, _, he, rfl⟩ := h
    have := vec_positive he
    simp only [List.length_append]
    omega
  | Wasm2 =>
    cases h with
    | active _ _ he | passive _ he =>
      have := vec_positive he
      simp only [List.length_append]
      omega

private theorem rep_cost {α : Type} {R : α → List U8 → Prop} {values bytes}
    (cost : α → Nat) (h : Rep R values bytes)
    (bounded : ∀ value bytes, R value bytes → cost value ≤ 3 * bytes.length) :
    (values.map cost).sum ≤ 3 * bytes.length := by
  induction h with
  | nil => simp
  | cons hx _ ih =>
    have := bounded _ _ hx
    simp only [List.map_cons, List.sum_cons, List.length_append]
    omega

private theorem padded_cost {α : Type} {R : α → List U8 → Prop} {id values bytes}
    (cost : α → Nat) (h : PaddedEncoding id (VecEncoding R) [] values bytes)
    (bounded : ∀ value bytes, R value bytes → cost value ≤ 3 * bytes.length) :
    (values.map cost).sum ≤ 3 * bytes.length := by
  obtain ⟨customs, sec, _, hs, rfl⟩ := h
  cases hs with
  | absent => simp
  | present hp =>
    obtain ⟨size, payload, _, ⟨count, entries, _, hr, rfl⟩, rfl⟩ := hp
    have := rep_cost cost hr bounded
    simp only [List.length_append, List.length_cons]
    omega

/-- The independently encoded declaration sections pay for all initializer-map
appends and the defined functions, including empty element segments. -/
theorem initializer_cost_bytes {R raw bytes profile}
    (encoding : ModuleEncodingWith R raw bytes profile) :
    raw.functions.length + 2 * raw.globals.length +
      (raw.elements.map (fun e => e.init.length + 3)).sum + 2 * raw.data.length ≤
      3 * bytes.length := by
  obtain ⟨types, imports, functions, tables, memories, globals, exports, start, elements, dataCount,
    codes, datas, customs, _, _, hf, _, _, hg, _, _, he, _, _, hd, _, rfl, _, _⟩ := encoding
  have hf := padded_cost (fun _ => 1) hf (fun _ _ h => by have := leb_nonempty h; omega)
  have hg := padded_cost (fun _ => 2) hg (fun _ _ h => global_cost h)
  have he := padded_cost (fun e => e.init.length + 3) he (fun _ _ h => element_cost h)
  have hd := padded_cost (fun _ => 2) hd (fun _ _ h => data_cost h)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_one] at hf hg hd
  simp only [List.length_append]
  omega

/-- Canonical metadata and the fixed module-byte cap discharge both numeric
headroom obligations before initializer lowering runs. No successful initializer
result is assumed. -/
theorem initializer_source_headroom {R raw bytes profile env tail}
    (encoding : ModuleEncodingWith R raw bytes profile)
    (matched : Itasca.ModuleElaboration.Matches env tail raw)
    (bounded : bytes.length ≤ Itasca.limits.MAX_MODULE_BYTES.val) :
    env.func_type_indices.val.length + initializerMappingCost ⟨env, tail⟩ + 1 ≤ Usize.max ∧
    5 * (env.elements.val.length + tail.data.val.length) + 1 ≤ Usize.max := by
  have cost := initializer_cost_bytes encoding
  have segments := segment_count_bytes encoding
  have costEq := congrArg (fun raw : Module => raw.functions.length + 2 * raw.globals.length +
    (raw.elements.map (fun e => e.init.length + 3)).sum + 2 * raw.data.length) matched.1
  have segmentEq := congrArg (fun raw : Module => raw.elements.length + raw.data.length) matched.1
  simp only [Itasca.ModuleElaboration.fromEnv, List.length_map, List.map_map,
    Function.comp_def, Itasca.ModuleEnv.rawElement] at costEq segmentEq
  rw [costEq] at cost
  rw [segmentEq] at segments
  have wordBound : U32.max ≤ Usize.max := by scalar_tac
  norm_num [Itasca.limits.MAX_MODULE_BYTES, U32.max_eq] at bounded wordBound
  dsimp only [initializerMappingCost, initializerElementCost]
  constructor <;> omega

end Exec.Code
