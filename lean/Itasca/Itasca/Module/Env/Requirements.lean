import Itasca.Module.Env.ValidityTransport

section
open Aeneas Aeneas.Std

namespace Itasca.Module.Sections

open Module.Environment Binary

private theorem Marked.sameCore {env result desc} (h : Marked env result desc) : SameCore env result := by
  cases desc <;> obtain ⟨d, lookup, rfl⟩ := h <;> constructor <;>
    first | rfl | exact map_descriptor_update _ _ _ lookup rfl

private theorem Marked.globalEntries {env result desc} (h : Marked env result desc) :
    result.globals.val.map (fun g => (g.gtype, g.init)) =
      env.globals.val.map (fun g => (g.gtype, g.init)) := by
  cases desc <;> obtain ⟨d, lookup, rfl⟩ := h <;>
    first | rfl | exact map_descriptor_update _ _ _ lookup rfl

private theorem Marked.resolves {env result desc} (h : Marked env result desc) (valid : DescriptorIndices env) :
    ∃ xt, env.externalTypeAt desc = some xt := by
  cases desc <;> obtain ⟨d, lookup, rfl⟩ := h
  case Func idx =>
    have bound := valid d (List.mem_iff_getElem?.mpr ⟨_,lookup⟩)
    simp [metadata.CodeMetadata.externalTypeAt, lookup, List.getElem?_eq_getElem bound]
  all_goals simp [metadata.CodeMetadata.externalTypeAt, lookup]

private theorem Marked.declared {env result desc} (h : Marked env result desc) (i : Nat) :
    WebAssembly.uN.mk_uN i ∈ Translation.Environment.declaredReferences result ↔
    WebAssembly.uN.mk_uN i ∈ Translation.Environment.declaredReferences env ∨
      ∃ idx : U32, desc = .Func idx ∧ idx.val = i := by
  cases desc <;> obtain ⟨d, lookup, rfl⟩ := h
  case Func idx =>
    rw [Translation.Environment.mem_declaredReferences, Translation.Environment.mem_declaredReferences]
    have hc : (UScalar.cast .Usize idx).val = idx.val := by scalar_tac
    have hb := (List.getElem?_eq_some_iff.mp lookup).1
    by_cases eq : idx.val = i
    · subst i; simp [alloc.vec.Vec.set_val_eq, hc, hb]
    · simp [alloc.vec.Vec.set_val_eq, hc, List.getElem?_set_ne eq, eq]
  all_goals simp [Translation.Environment.declaredReferences]

private theorem projected_mem {α β : Type} {f : α → β} {xs ys : List α}
    (eq : xs.map f = ys.map f) {x} (hm : x ∈ xs) : ∃ y ∈ ys, f y = f x := by
  apply List.mem_map.mp
  rw [← eq]; exact List.mem_map_of_mem hm

/-- Marking an export preserves all previous external types and declares an exported function. -/
theorem ExportAdded.valid {env result entry} (h : ExportAdded env result entry)
    (hv : Valid env) (helements : env.elements.val = []) (hn : Utf8 entry.name.val) : Valid result := by
  obtain ⟨fields, exports, fresh, marked⟩ := h
  have hc := marked.sameCore
  have hg := marked.globalEntries
  refine ⟨?_, DescriptorIndices.marked hv.funcs marked, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc.types]; exact hv.types
  · intro d hd
    obtain ⟨old, hm, eq⟩ := projected_mem hc.tables hd
    rw [← eq]; exact hv.tables _ hm
  · intro d hd
    obtain ⟨old, hm, eq⟩ := projected_mem hc.memories hd
    rw [← eq]; exact hv.memories _ hm
  · have eq := congrArg List.length hc.memories
    simp only [List.length_map] at eq
    rw [eq]; exact hv.memoryCount
  · intro g hm init eq
    obtain ⟨old, hm, same⟩ := projected_mem hg hm
    have gt : old.gtype = g.gtype := congrArg Prod.fst same
    have gi := congrArg Prod.snd same
    rw [← gt]; exact hc.constant (hv.globals old hm init (gi.trans eq))
  · rw [fields]; exact hv.imports
  · intro e hm
    rw [exports] at hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hv.exportNames _ hm
    · exact List.mem_singleton.mp hm ▸ hn
  · rw [exports, List.map_append, List.map_singleton]
    exact List.Nodup.append hv.distinctExports (by simp) (by simpa using fresh)
  · intro e hm
    rw [exports] at hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨xt, hx⟩ := hv.exports e hm; exact ⟨xt, hc.export hx⟩
    · obtain rfl := List.mem_singleton.mp hm
      obtain ⟨xt, hx⟩ := marked.resolves hv.funcs
      exact ⟨xt, hc.export hx⟩
  · intro idx hs
    have same : result.code.start = env.code.start := by
      cases hd : entry.desc <;> rw [hd] at marked <;> obtain ⟨_,_,eq⟩ := marked <;> rw [eq]
    exact hc.start (hv.start idx (same ▸ hs))
  · rw [fields]; simp [helements]
  · have hglobal : result.code.globals.val.flatMap Module.References.global =
        env.code.globals.val.flatMap Module.References.global := by
      have eq := congrArg (List.flatMap (fun g : wasm_types.GlobalType × Option wasm_types.ConstExpr =>
        g.2.toList.flatMap Module.References.initializer)) hg
      unfold Module.References.global
      simpa only [List.flatMap_map, Function.comp_def] using eq
    intro i
    rw [marked.declared, hv.references]
    have elems : result.elements = env.elements := by rw [fields]
    simp only [Module.References.collected, hglobal, exports, elems, helements, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append]
    cases hd : entry.desc <;> simp [Module.References.exportIndices, hd] <;> grind

theorem ExportsAdded.valid {env entries result} (h : ExportsAdded env entries result)
    (hv : Valid env) (helements : env.elements.val = []) (hn : ∀ e ∈ entries, Utf8 e.name.val) : Valid result := by
  induction h with
  | nil => exact hv
  | snoc hp ha ih =>
    exact ha.valid (ih (by intro e hm; exact hn e (by simp [hm])))
      (by rw [hp.unchanged]; exact helements) (hn _ (by simp))

end Itasca.Module.Sections

namespace Itasca.Module.Environment

open Binary Module.Sections

private theorem initializer_bound {env init ty} (h : Module.Constants.Valid env init ty) :
    ∀ idx ∈ Module.References.initializer init, idx.val < env.funcs.val.length := by
  cases h <;> simp_all [Module.References.initializer]

private theorem element_bound {env entry} (h : ElementValid env entry) :
    ∀ idx ∈ Module.References.element entry, idx.val < env.funcs.val.length := by
  cases eq : entry.init with
  | Functions xs =>
    intro idx hm
    have mem : wasm_types.ConstExpr.RefFunc idx ∈ (rawElement entry).init := by
      simpa [rawElement, eq] using List.mem_map_of_mem (f := wasm_types.ConstExpr.RefFunc)
        (by simpa [Module.References.element, eq] using hm : idx ∈ xs.val)
    exact initializer_bound (h.2 _ mem) idx (by simp [Module.References.initializer])
  | Expressions xs =>
    intro idx hm
    obtain ⟨init, mem, ref⟩ := List.mem_flatMap.mp (by simpa [Module.References.element, eq] using hm :
      idx ∈ xs.val.flatMap Module.References.initializer)
    exact initializer_bound (h.2 init (by simpa [rawElement, eq] using mem)) idx ref

private theorem valid_late {env result : metadata.ModuleMetadata metadata.CodeMetadata}
    (valid : Valid env) (core : SameCore env.code result.code) (indices : DescriptorIndices result.code)
    (tables : result.code.tables = env.code.tables) (memories : result.code.memories = env.code.memories)
    (globals : result.code.globals = env.code.globals) (imports : result.imports = env.imports)
    (exports : result.exports = env.exports)
    (start : ∀ idx, result.code.start = some idx → ∃ ft, result.code.externalTypeAt (.Func idx) = some (.Func ft) ∧
      ft.params.val = [] ∧ ft.results.val = [])
    (elements : ∀ e ∈ result.elements.val, ElementValid result.code e)
    (refs : Module.References.Coherent result) : Valid result := by
  refine ⟨core.types ▸ valid.types, indices, tables ▸ valid.tables, memories ▸ valid.memories,
    memories ▸ valid.memoryCount, ?_, imports ▸ valid.imports, exports ▸ valid.exportNames,
    exports ▸ valid.distinctExports, ?_, start, elements, refs⟩
  · intro g hm init eq
    exact core.constant (valid.globals g (globals ▸ hm) init eq)
  · intro e hm
    obtain ⟨xt,hx⟩ := valid.exports e (exports ▸ hm)
    exact ⟨xt, core.export hx⟩

/-- A section effect in increasing section order preserves `Valid`, including name well-formedness,
export uniqueness and initializer validity. -/
theorem Effect.valid {data pos env before id next result after last}
    (h : Effect data pos env before id next result after)
    (hr : Represents env before) (hv : Valid env)
    (hp : Phase last before) (ho : last < (sectionRank id).val) : Valid result := by
  have indices := h.indices hv.funcs
  cases h with
  | @types updated _ added ha hb ht =>
    have early := Early.of_phase hr hp (by change last < 1 at ho; omega)
    have er : Early {env with code := updated} := by rw [ha.1]; exact ⟨early.globals, early.exports, early.start, early.elements⟩
    rw [ha.1] at er indices ⊢
    apply er.valid
    · intro ft hm
      rcases List.mem_append.mp (ha.2 ▸ hm) with h | h
      · exact hv.types _ h
      · exact ht _ h
    · exact indices
    · exact hv.tables
    · exact hv.memories
    · exact hv.memoryCount
    · exact hv.imports
    · exact hv.references
  | imports ha hb =>
    apply ha.valid hv (Early.of_phase hr hp (by change last < 2 at ho; omega))
    intro entry hm
    obtain ⟨_, bytes, _⟩ := hb
    obtain ⟨_, encoded⟩ := bytes.member hm
    obtain ⟨_, _, _, hm, hn, _, _⟩ := ImportEncoding.reader_parts.mp encoded
    exact ⟨hm.2, hn.2⟩
  | @functions updated _ added ha _ =>
    have early := Early.of_phase hr hp (by change last < 3 at ho; omega)
    have er : Early {env with code := updated} := by rw [ha.1]; exact ⟨early.globals, early.exports, early.start, early.elements⟩
    rw [ha.1] at er indices ⊢
    apply er.valid
      hv.types indices hv.tables hv.memories hv.memoryCount hv.imports
    apply er.coherent.mpr
    intro d hm
    rcases List.mem_append.mp (ha.2.1 ▸ hm) with h | h
    · exact early.coherent.mp hv.references _ h
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp h; rfl
  | @tables updated _ added ha _ ht =>
    have early := Early.of_phase hr hp (by change last < 4 at ho; omega)
    have er : Early {env with code := updated} := by rw [ha.1]; exact ⟨early.globals, early.exports, early.start, early.elements⟩
    rw [ha.1] at er indices ⊢
    refine er.valid
      hv.types indices ?_ hv.memories hv.memoryCount hv.imports hv.references
    intro d hm
    rcases List.mem_append.mp (ha.2 ▸ hm) with h | h
    · exact hv.tables _ h
    · obtain ⟨ty, mem, rfl⟩ := List.mem_map.mp h; exact ht _ mem
  | @memories updated _ added ha _ ht count =>
    have early := Early.of_phase hr hp (by change last < 5 at ho; omega)
    have er : Early {env with code := updated} := by rw [ha.1]; exact ⟨early.globals, early.exports, early.start, early.elements⟩
    rw [ha.1] at er indices ⊢
    refine er.valid
      hv.types indices hv.tables ?_ (by simpa [max_eq_right hv.memoryCount] using count) hv.imports hv.references
    intro d hm
    rcases List.mem_append.mp (ha.2 ▸ hm) with h | h
    · exact hv.memories _ h
    · obtain ⟨ty, mem, rfl⟩ := List.mem_map.mp h; exact ht _ mem
  | @globals updated _ added ha hb hg =>
    have early := Early.of_phase hr hp (by change last < 6 at ho; exact ho)
    have old : env.code.globals.val.flatMap Module.References.global = [] := by
      simpa [Module.References.collected, early.exports, early.elements] using early.collected
    have len := congrArg List.length ha.2.2.funcs
    simp only [List.length_map, List.length_zipIdx] at len
    have bound : ∀ idx ∈ added.flatMap (fun g => Module.References.initializer g.init), idx.val < env.code.funcs.val.length := by
      intro idx hm
      obtain ⟨g, mem, ref⟩ := List.mem_flatMap.mp hm
      exact len ▸ initializer_bound (hg g mem) idx ref
    have decl := ha.2.2.declared bound
    rw [ha.1] at indices ⊢
    refine ⟨hv.types, indices, hv.tables, hv.memories, hv.memoryCount, ?_, hv.imports,
      hv.exportNames, hv.distinctExports, ?_, ?_, ?_, ?_⟩
    · intro g hm init eq
      rcases List.mem_append.mp (ha.2.1 ▸ hm) with hm | hm
      · simp [early.globals g hm] at eq
      · obtain ⟨raw, member, rfl⟩ := List.mem_map.mp hm
        have valid := hg raw member
        cases eq
        rw [ha.1] at valid; exact valid
    · simp [early.exports]
    · simp [early.start]
    · simp [early.elements]
    · intro i
      change WebAssembly.uN.mk_uN i ∈ Translation.Environment.declaredReferences
        {env.code with funcs := _} ↔ _
      rw [decl, hv.references, early.collected]
      simp [Module.References.collected, ha.2.1, early.exports, early.elements, old,
        List.flatMap_map, Module.References.global]
  | exports ha hb =>
    apply ha.valid hv
    · have he := hp.2.2.2.2.2.2.2.2.1 (by change last < 7 at ho; omega)
      exact List.map_eq_nil_iff.mp (hr.elements.symm.trans he)
    intro entry hm
    obtain ⟨bytes, hbytes, _⟩ := hb
    obtain ⟨bs, he⟩ := hbytes.member (List.mem_map.mpr ⟨entry, hm, rfl⟩)
    obtain ⟨_, _, hn, _, _⟩ := ExportEncoding.reader_parts.mp he
    exact hn.2
  | @start updated _ index d he _ hstart =>
    have hc : SameCore env.code updated := by
      rw [he]
      constructor <;> first | rfl | exact map_descriptor_update _ _ _ hstart.1 rfl
    rw [he] at hc indices ⊢
    apply valid_late hv hc indices rfl rfl rfl rfl rfl
    · intro idx hs
      cases Option.some.inj hs
      obtain ⟨ft, lookup, params, results⟩ := hstart.2
      exact hc.start ⟨ft, by simp [metadata.CodeMetadata.externalTypeAt, hstart.1, lookup], params, results⟩
    · intro e hm; exact hc.element (hv.elements _ hm)
    · intro i
      rw [Translation.Environment.mem_declaredReferences]
      have old := hv.references i
      rw [Translation.Environment.mem_declaredReferences] at old
      change (_ ↔ ∃ idx ∈ Module.References.collected env, idx.val = i)
      rw [← old]
      dsimp only
      have cast : (UScalar.cast .Usize index).val = index.val := by scalar_tac
      obtain ⟨bound,eq⟩ := List.getElem?_eq_some_iff.mp hstart.1
      by_cases same : index.val = i
      · subst i
        simp [alloc.vec.Vec.set_val_eq, cast, bound, eq]
      · simp [alloc.vec.Vec.set_val_eq, cast, List.getElem?_set_ne same]
  | @elements updated _ added ha _ ht =>
    have bound : ∀ idx ∈ added.flatMap Module.References.element, idx.val < env.code.funcs.val.length := by
      intro idx hm
      obtain ⟨e, mem, ref⟩ := List.mem_flatMap.mp hm
      exact element_bound (ht e mem) idx ref
    have decl := ha.refs.declared bound
    have hc : SameCore env.code result.code := by
      rw [ha.fields]
      constructor <;> try rfl
      dsimp only
      rw [ha.refs.funcs]
      apply List.ext_getElem <;> simp
    rw [ha.fields] at hc indices ⊢
    apply valid_late hv hc indices rfl rfl rfl rfl rfl
    · intro idx hs; exact hc.start (hv.start idx hs)
    · intro e hm
      rcases List.mem_append.mp (ha.elements ▸ hm) with hm | hm
      · exact hc.element (hv.elements _ hm)
      · exact hc.element (ht _ hm)
    · intro i
      change WebAssembly.uN.mk_uN i ∈ Translation.Environment.declaredReferences
        {env.code with funcs := _} ↔ _
      rw [decl, hv.references]
      simp [Module.References.collected, ha.elements, List.flatMap_append, List.mem_append]
      grind
  | @dataCount updated _ count he _ =>
    have hc : SameCore env.code updated := by rw [he]; constructor <;> rfl
    rw [he] at hc indices ⊢
    apply valid_late hv hc indices rfl rfl rfl rfl rfl
    · intro idx hs; exact hc.start (hv.start idx hs)
    · intro e hm; exact hc.element (hv.elements _ hm)
    · exact hv.references

end Itasca.Module.Environment

end

/-! ## Semantics -/

section

/-!
# Semantic contract of the environment parser

`metadata.validate_env.semantic_spec` shows that for arbitrary bytes, `metadata.validate_env`
either rejects or returns an environment with `SemanticPostWith`. That is a `Represents`
declaration record, `Valid`, signature and size bounds, and an independent `PrefixEncoding` of the
consumed bytes. The same holds for `metadata.validate_env_with` with total custom-section hooks.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Environment

/-- Validity follows a run of sections, alongside the raw declaration representation. -/
theorem Run.valid {data initial decls start initialId after afterDecls next id}
    (h : Run data initial decls start initialId after afterDecls next id)
    (hr : Represents initial decls) (hv : Valid initial) (hp : Phase initialId.val decls) :
    Valid after := by
  induction h with
  | nil => exact hv
  | custom _ _ ih => exact ih
  | step previous horder hh he ih =>
      exact he.valid (previous.represents hr hp) ih (previous.phase hp) horder

/-- An accepted environment comes with a declaration record that represents it, its semantic
checks, the signature and size bounds needed by the code and data parsers, and the independent byte
encoding of the consumed prefix. -/
def SemanticPostWith (data : Slice U8) : core.result.Result (metadata.ModuleMetadata metadata.CodeMetadata × Usize) error.Error → Prop
  | .Err _ => True
  | .Ok (env, next) => ∃ decls, Represents env decls ∧ Valid env ∧
      SignatureBounded env.code next.val ∧ Bounded env next.val ∧
      Binary.At (fun ds bs => PrefixEncoding ds bs) data 0#usize decls next

/-- The run-based postcondition implies the semantic one. -/
theorem PostWith.semantic {data result} (h : PostWith data result) : SemanticPostWith data result := by
  cases result with
  | Err _ => trivial
  | Ok pair =>
      obtain ⟨env, next⟩ := pair
      obtain ⟨initial, start, decls, last, hinit, hheader, hrun, hbound⟩ := h
      have hi := metadata.ModuleMetadataCodeMetadata.new.declarations
      rw [hinit] at hi
      simp only [WP.spec_ok] at hi
      obtain ⟨hr, hv, hs, _, hp⟩ := hi
      exact ⟨decls, hrun.represents hr hp, hrun.valid hr hv hp,
        hrun.signature_bounded (hs.mono (Nat.zero_le _)), hbound, hrun.encoding hheader⟩

end Itasca.Module.Environment

namespace Itasca

/-- Arbitrary bytes either make `metadata.validate_env` reject or yield an independently encoded,
semantically valid declaration prefix with consistent caches. -/
theorem metadata.validate_env.semantic_spec (data : Slice U8) :
    metadata.validate_env data ⦃ Module.Environment.SemanticPostWith data ⦄ := by
  obtain ⟨result, hr, hp⟩ := WP.spec_imp_exists (metadata.validate_env.spec data)
  rw [hr]
  simpa only [WP.spec_ok] using Module.Environment.PostWith.semantic hp

end Itasca

end

/-! ## Requirements -/

section

/-!
# Declarative requirements of the environment

`SectionValid` states the semantic requirements of each declaration section against the
environment built so far. `Ready` says all slots through a given rank are complete, and
`Requirements` collects `SectionValid` for every section reached from a ready state. The
requirements contain no parser execution, so completeness can start from them. `StopAt` describes
where the greedy section scan ends.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Sections

/-- The semantic requirements for one import against the index spaces built so far. -/
def ImportValid (env : metadata.CodeMetadata) (desc : Binary.ImportDesc) : Prop :=
  match desc with
  | .Func idx => idx.val < env.types.val.length
  | .Table tt => Binary.LimitsValid tt.limits limits.MAX_TABLE_ELEMS
  | .Memory mt => Binary.LimitsValid mt.limits limits.MAX_MEMORY_PAGES ∧
      env.memories.val.length + 1 ≤ 1
  | .Global _ => True

/-- The memory types among the raw imports. -/
def rawMemories (entries : List Binary.Import) : List wasm_types.MemType :=
  entries.filterMap (fun e => match e.desc with | .Memory mt => some mt | _ => none)

/-- The imports are valid against `env`. Descriptor checks are separate from the cardinality limits
on the merged memory space, so imports can be processed in order. -/
structure ImportsValid (env : metadata.CodeMetadata) (entries : List Binary.Import) : Prop where
  descriptors : ∀ e ∈ entries, match e.desc with
    | .Func idx => idx.val < env.types.val.length
    | .Table tt => Binary.LimitsValid tt.limits limits.MAX_TABLE_ELEMS
    | .Memory mt => Binary.LimitsValid mt.limits limits.MAX_MEMORY_PAGES
    | .Global _ => True
  memories : env.memories.val.length + (rawMemories entries).length ≤ 1

/-- A raw element segment is valid against `env`. An active segment names a table of its element
type with a valid `i32` offset, and every initializer is a valid constant of the element type. -/
def ElementValidRaw (env : metadata.CodeMetadata) (entry : Binary.Element) : Prop :=
  (match entry.mode with
    | .Active idx offset => ∃ hi : idx.val < env.tables.val.length,
        env.tables.val[idx.val].ty.elem = entry.elem ∧ Module.Constants.Valid env offset .I32
    | .Passive | .Declarative => True) ∧
  ∀ init ∈ entry.init, Module.Constants.Valid env init (Module.Constants.referenceValueType entry.elem)

/-- The first import of a valid list is valid at the current index-space prefix. -/
theorem ImportsValid.head {env entry entries} (h : ImportsValid env (entry :: entries)) :
    ImportValid env entry.desc := by
  have hd := h.descriptors entry (by simp)
  have hm := h.memories
  cases he : entry.desc <;> simp only [he, ImportValid] at hd ⊢
  · exact hd
  · exact hd
  · refine ⟨hd, ?_⟩
    simp [rawMemories, he] at hm
    omega

/-- After the first import is added, the remaining imports are valid against the updated
environment. -/
theorem ImportsValid.tail {env result : metadata.ModuleMetadata metadata.CodeMetadata} {actual entries}
    (h : ImportsValid env.code (actual :: entries))
    (ha : ImportAdded env result actual) : ImportsValid result.code entries := by
  obtain ⟨_, ha⟩ := ha
  have hd : ∀ e ∈ entries, match e.desc with
      | .Func idx => idx.val < env.code.types.val.length
      | .Table tt => Binary.LimitsValid tt.limits limits.MAX_TABLE_ELEMS
      | .Memory mt => Binary.LimitsValid mt.limits limits.MAX_MEMORY_PAGES
      | .Global _ => True := fun e he => h.descriptors e (by simp [he])
  have hm := h.memories
  cases he : actual.desc <;> simp only [he] at ha
  · obtain ⟨_, hr, _, _⟩ := ha
    rw [hr]
    exact ⟨hd, by simpa [rawMemories, he] using hm⟩
  · obtain ⟨hr, _, _⟩ := ha
    rw [hr]
    exact ⟨hd, by simpa [rawMemories, he] using hm⟩
  · obtain ⟨hr, hs, _, _⟩ := ha
    rw [hr]
    refine ⟨hd, ?_⟩
    simp only
    rw [hs]
    have hl : (rawMemories (actual :: entries)).length = (rawMemories entries).length + 1 := by
      simp [rawMemories, he]
    rw [hl] at hm
    simp only [List.length_append, List.length_singleton]
    omega
  · obtain ⟨hr, _, _⟩ := ha
    rw [hr]
    exact ⟨hd, by simpa [rawMemories, he] using hm⟩

/-- A raw export descriptor resolves in its Wasm index space. -/
def ExportDescValid (env : metadata.CodeMetadata) (desc : metadata.ExportDesc) : Prop :=
  ∃ xt, env.externalTypeAt desc = some xt

end Itasca.Module.Sections

namespace Itasca.Module.Environment

/-- The greedy environment scan stops only at end of input or at a complete section header for the
code section (`10`) or data section (`11`). -/
def StopAt (data : Slice U8) (pos : Usize) : Prop :=
  pos = Slice.len data ∨ ∃ id first last,
    Binary.SectionHeader data pos id first last ∧ (id = 10#u8 ∨ id = 11#u8)

/-- The semantic requirements of declaration section rank `id` of `raw` against `env`. Binary
framing, UTF-8 names, and cursor and capacity bounds come separately from the grammar. -/
def SectionValid (raw : Binary.Module) (id : Nat) (env : metadata.CodeMetadata) : Prop :=
  match id with
  | 1 => ∀ ft ∈ raw.types, CodeEntry.FuncTypeWithinLimits ft
  | 2 => Module.Sections.ImportsValid env raw.imports
  | 3 => ∀ idx ∈ raw.functions, idx.val < env.types.val.length
  | 4 => ∀ tt ∈ raw.tables, Binary.LimitsValid tt.limits limits.MAX_TABLE_ELEMS
  | 5 => (∀ mt ∈ raw.memories, Binary.LimitsValid mt.limits limits.MAX_MEMORY_PAGES) ∧
      env.memories.val.length + raw.memories.length ≤ 1
  | 6 => ∀ g ∈ raw.globals, Module.Constants.Valid env g.init g.gtype.valtype
  | 7 => (raw.exports.map Binary.Export.name).Nodup ∧
      ∀ e ∈ raw.exports, Module.Sections.ExportDescValid env e.desc
  | 8 => ∀ idx, raw.start = some idx → ∃ ft, env.externalTypeAt (.Func idx) = some (.Func ft) ∧
      ft.params.val = [] ∧ ft.results.val = []
  | 9 => ∀ e ∈ raw.elements, Module.Sections.ElementValidRaw env e
  | 10 => True
  | _ => True

/-- Every declaration section of `raw` meets its requirements whenever the preceding slots are
ready. Declarative assembly discharges this once, and it has no parser-execution or
successful-decoding premise. -/
def Requirements (raw : Binary.Module) : Prop :=
  ∀ id decls env, 1 ≤ id → id ≤ 10 → Ready raw (id - 1) decls env → SectionValid raw id env.code

end Itasca.Module.Environment

end
