import Itasca.Module.Env.Representation

/-! Descriptor flags across the section parser's ordered updates. -/

open Aeneas Aeneas.Std
namespace Itasca.Module.Environment

open Module.Sections

private def markedAt (bits : List Bool) (i : Nat) := bits[i]? = some true

private theorem marked_append {xs : List Bool} {ys : List α} {n : Nat} :
    markedAt (xs ++ ys.map (fun _ => false)) n ↔ markedAt xs n := by
  unfold markedAt
  by_cases h : n < xs.length
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (by omega : xs.length ≤ n)]
    rw [List.getElem?_map]
    cases ys[n - xs.length]? <;> simp

private theorem marked_set {v : alloc.vec.Vec α} {idx : U32} {old new : α}
    {flag : α → Bool} (lookup : v.val[idx.val]? = some old) (on : flag new = true) (i : Nat) :
    markedAt ((v.set (UScalar.cast .Usize idx) new).val.map flag) i ↔
      markedAt (v.val.map flag) i ∨ idx.val = i := by
  have cast : (UScalar.cast .Usize idx).val = idx.val := by scalar_tac
  have bound := List.getElem?_eq_some_iff.mp lookup
  by_cases eq : idx.val = i
  · subst i
    simp [markedAt, alloc.vec.Vec.set_val_eq, cast, bound.1, on]
  · simp [markedAt, alloc.vec.Vec.set_val_eq, cast, List.getElem?_map, eq]

/-- The positions marked in each descriptor vector are exactly those named by the prefix.
The equivalences also exclude out-of-range indices. -/
private structure Marks (env : metadata.ModuleMetadata metadata.CodeMetadata) : Prop where
  funcs : ∀ i, markedAt (env.code.funcs.val.map metadata.FuncDesc.eager) i ↔
    ∃ idx : U32, idx.val = i ∧ (env.code.start = some idx ∨ ∃ e ∈ env.exports.val, e.desc = .Func idx)
  tables : ∀ i, markedAt (env.code.tables.val.map metadata.TableDesc.is_exported) i ↔
    ∃ idx : U32, idx.val = i ∧ ∃ e ∈ env.exports.val, e.desc = .Table idx
  memories : ∀ i, markedAt (env.code.memories.val.map metadata.MemoryDesc.is_exported) i ↔
    ∃ idx : U32, idx.val = i ∧ ∃ e ∈ env.exports.val, e.desc = .Memory idx
  globals : ∀ i, markedAt (env.code.globals.val.map metadata.Global.is_exported) i ↔
    ∃ idx : U32, idx.val = i ∧ ∃ e ∈ env.exports.val, e.desc = .Global idx

private theorem Marks.flags {env} (h : Marks env) : DescriptorFlags env := by
  constructor <;> intro i d hd <;> first
    | simpa [markedAt, List.getElem?_map, hd] using h.funcs i
    | simpa [markedAt, List.getElem?_map, hd] using h.tables i
    | simpa [markedAt, List.getElem?_map, hd] using h.memories i
    | simpa [markedAt, List.getElem?_map, hd] using h.globals i

private theorem export_marks {env result entry} (add : ExportAdded env result entry)
    (prev : Marks env) : Marks result := by
  obtain ⟨fields, exports, _, marked⟩ := add
  rw [fields]
  cases desc : entry.desc <;> simp only [Marked, desc] at marked <;>
    obtain ⟨d, lookup, update⟩ := marked <;> rw [update] <;> constructor <;> intro i
  all_goals
    dsimp only
    simp only [exports, List.mem_append, List.mem_singleton]
    first
      | rw [marked_set lookup rfl, prev.funcs]; grind
      | rw [marked_set lookup rfl, prev.tables]; grind
      | rw [marked_set lookup rfl, prev.memories]; grind
      | rw [marked_set lookup rfl, prev.globals]; grind
      | rw [prev.funcs]; grind
      | rw [prev.tables]; grind
      | rw [prev.memories]; grind
      | rw [prev.globals]; grind

private theorem marked_snoc (xs : List Bool) (i : Nat) :
    markedAt (xs ++ [false]) i ↔ markedAt xs i :=
  marked_append (ys := [()])

private theorem import_marks {env result entry} (add : ImportAdded env result entry)
    (prev : Marks env) : Marks result := by
  obtain ⟨_, update⟩ := add
  cases desc : entry.desc <;> simp only [desc] at update
  all_goals
    first | obtain ⟨_, fields, appended, _⟩ := update; rw [fields]
          | obtain ⟨fields, appended, _⟩ := update; rw [fields]
    constructor <;> intro i <;> dsimp only
    all_goals first
      | exact prev.funcs i
      | exact prev.tables i
      | exact prev.memories i
      | exact prev.globals i
      | simp only [appended, List.map_append, List.map_cons, List.map_nil, marked_snoc]
        first | exact prev.funcs i | exact prev.tables i | exact prev.memories i | exact prev.globals i

private theorem eager_of_refs {env after indices} (add : Module.References.Added env after indices) :
    after.funcs.val.map metadata.FuncDesc.eager = env.funcs.val.map metadata.FuncDesc.eager := by
  rw [add.funcs]
  apply List.ext_getElem <;> simp

private theorem effect_marks {data pos env before id next result after last}
    (h : Effect data pos env before id next result after) (prev : Marks env)
    (rep : Represents env before) (phase : Phase last before)
    (ordered : last < (Binary.sectionRank id).val) : Marks result := by
  cases h with
  | imports add bytes =>
    clear bytes
    induction add with
    | nil => exact prev
    | snoc _ update ih => exact import_marks update ih
  | exports add bytes =>
    clear bytes
    induction add with
    | nil => exact prev
    | snoc _ update ih => exact export_marks update ih
  | types add _ _ | dataCount add _ =>
    first | rw [add.1] | rw [add]
    exact ⟨prev.funcs, prev.tables, prev.memories, prev.globals⟩
  | functions add _ | tables add _ _ | memories add _ _ _ | globals add _ _ =>
    rw [add.1]
    constructor <;> intro i <;> dsimp only
    all_goals first
      | exact prev.funcs i
      | exact prev.tables i
      | exact prev.memories i
      | exact prev.globals i
      | rw [show _ = env.code.funcs.val.map metadata.FuncDesc.eager from eager_of_refs add.2.2]
        exact prev.funcs i
      | simp only [add.2.1, List.map_append, List.map_map, Function.comp_def, marked_append]
        first | exact prev.funcs i | exact prev.globals i
      | simp only [add.2, List.map_append, List.map_map, Function.comp_def, marked_append]
        first | exact prev.tables i | exact prev.memories i
  | elements add _ _ =>
    rw [add.fields]
    refine ⟨?_, prev.tables, prev.memories, prev.globals⟩
    intro i
    dsimp only
    rw [show _ = env.code.funcs.val.map metadata.FuncDesc.eager from eager_of_refs add.refs]
    exact prev.funcs i
  | start update _ lookup =>
    change last < 8 at ordered
    have empty : env.code.start = none := rep.start.symm.trans (phase.2.2.2.2.2.2.2.1 ordered)
    rw [update]
    refine ⟨?_, prev.tables, prev.memories, prev.globals⟩
    intro i
    dsimp only
    rw [marked_set lookup.1 rfl, prev.funcs, empty]
    grind

/-- A successful prefix parse records exactly the eager and exported descriptors. -/
theorem Run.descriptor_flags {data initial decls start initialId after afterDecls next id}
    (h : Run data initial decls start initialId after afterDecls next id)
    (init : metadata.ModuleMetadataCodeMetadata.new = .ok initial)
    (rep : Represents initial decls) (phase : Phase initialId.val decls) : DescriptorFlags after := by
  have empty : Marks initial := by
    simp only [metadata.ModuleMetadataCodeMetadata.new, metadata.CodeMetadata.new, bind_ok, Result.ok.injEq] at init
    subst initial
    constructor <;> simp [markedAt]
  apply Marks.flags
  induction h with
  | nil => exact empty
  | custom _ _ ih => exact ih
  | step previous ordered _ update ih =>
    exact effect_marks update ih (previous.represents rep phase) (previous.phase phase) ordered

end Itasca.Module.Environment
