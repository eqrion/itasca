<!-- Research notes gathered on 2026-11-12 by a read-only research agent for PLAN.md. Statements marked [V] were read in the code; [I] are the agent's inferences and were not compiled. Line numbers refer to commit 81347267 and will drift. -->

# ExecutableInv and the public store API: research report

Path shorthand: `R/` = `lean/Itasca/Runtime/`, `Funs` = `lean/Itasca/Generated/Funs.lean`. Everything is marked **[V]** (verified by reading the code) or **[I]** (my inference, not compiled). Nothing was modified and nothing was built.

## 0. Headline findings

1. The fresh store is trivial, but it needs the hypothesis `0 < id.val` (`Shape.identity`). It does not need `Platform.MemoryLaws`.
2. `CumulativeStoreMutation` / `ExecutableInv.update` only covers operations that leave `id`, `funcs`, `types`, `instances`, `externs`, `limits` equal. That fits `define_memory_with`, `define_table_with`, `define_global_with`, `set_global`, `set_table`, `memory_mut`, `grow_memory_with`, `grow_table_with`. It does **not** fit `define_host_with` (funcs and types grow) or `define_extern_with` (externs grows).
3. `define_host_with` can return `Err` with a **changed** store (a newly interned type and no function). The postcondition must not say "error implies store unchanged".
4. All handle-taking operations index vectors without a bounds check, so a same-store out-of-range handle makes the extracted function `fail`. Each theorem needs an issued-handle premise. Value arguments need `IssuedValue`, otherwise a same-store dangling reference gets stored and breaks `ReferenceShape`.
5. Host functions need no extra hypothesis. Every function-indexed field is vacuous or trivially true for `.Host`.
6. Allocating operations need `Platform.AllocCorrect allocator` in addition to `MemoryLaws`.

## 1. Field tree of `ExecutableInv` [V]

`ExecutableInv view code store` (`R/Integration/Api/ExecutableInv.lean:19`) extends `CertifiedExecutableApiStore`, an `abbrev` for `CertifiedApiStore` (`R/Integration/Api/CertifiedApi.lean:22`, abbrev at :28), which extends `CertifiedSupportedStore` (`R/Integration/Execution/Ownership/CertifiedStore.lean:9`).

Anonymous constructor shape, as used by the existing `update` proofs: `⟨⟨⟨shape, storeSyntax, typed, supported, compiled, segmentBounds⟩, exportBounds⟩, segmentAccounting, capacities⟩`.

### CertifiedSupportedStore (CertifiedStore.lean:12-17)

| Field | Type | Meaning |
|---|---|---|
| `shape` (:12) | `Store.Shape view store` | Structural validity and resource accounting (below). |
| `storeSyntax` (:13) | `Store.StoreSyntax code store` | Every instance has well-formed export names and well-formed ghost source bodies. |
| `typed` (:14) | `Interp.CoreFunctionsTyped view code store` | Every function is source-typed. |
| `supported` (:15) | `SourceMachine.FunctionsSupported (Store.decodeStore view code store)` | Every Wasm body uses only supported instructions. |
| `compiled` (:16) | `Interp.Machine.CompiledFunctions code store` | Every Wasm function carries its compiler certificate. |
| `segmentBounds` (:17) | `Store.SegmentBounds store` | Every element and data segment is shorter than 2^32. |

**`Store.Shape`** (`R/Representation/StoreInvariant.lean:63-83`):
- `identity : 0 < s.id.val`
- `functions : ∀ f ∈ s.funcs.val, FunctionShape s f`. `FunctionShape` (:50): `f.signature.val < s.types.length ∧ match f.code with | .Host _ => True | .Wasm inst function => ∃ i, s.instances.val[inst.val]? = some i ∧ function.val < i.module.module.env.func_type_indices.length`.
- `memories : ∀ m ∈ s.memories.val, MemoryShape view m`. `MemoryShape` (:9): length is a multiple of 65536, at most 65536 pages, and pages ≤ maximum ≤ 65536 when a maximum exists.
- `tables : ∀ t ∈ s.tables.val, TableShape s t`. `TableShape` (:29): length ≤ `U32.max`, length ≤ maximum, every word satisfies `ReferenceShape s t.ty word`.
- `globals : ∀ g ∈ s.globals.val, GlobalShape s g`. `GlobalShape` (:21): I32/F32 need `lo < 2^32 ∧ hi = 0`, I64/F64 need `hi = 0`, V128 is `True`, references need `ReferenceShape` and `hi = 0`.
- `elements : ∀ e ∈ s.elems.val, ∀ word ∈ e.refs.val, ReferenceShape s e.ty word`.
- `instances : ∀ i ∈ s.instances.val, InstanceShape s i`. `InstanceShape` (:34): the seven map lengths equal the module's counts, and every mapped address has `store = s.id` and an in-range index.
- `canonicalTypes : (s.types.val.map decodeFuncType).Nodup`
- `objectLimit : funcs + types + tables + memories + globals + externs ≤ s.limits.max_objects.val`
- `instanceLimit`, `instanceAccounting : s.instance_items.val = (s.instances.val.map instanceItems).sum`, `instanceItemLimit`
- `signatureAccounting : s.signature_values.val = (s.types.val.map fun ty => ty.params.length + ty.results.length).sum`, `signatureLimit`
- `memoryAccounting : s.memory_bytes.val = (s.memories.val.map fun m => (view m.buf).length).sum`, `memoryLimit`
- `tableAccounting : s.table_elements.val = (s.tables.val.map fun t => t.elements.length).sum`, `tableLimit`

`ReferenceShape s ty word` (:15): `word.val = 0 ∨ (word.val - 1 < s.funcs.length` for FuncRef, `< s.externs.length` for ExternRef`)`.

**`StoreSyntax`** (`R/Store/Invariant/Syntax.lean:19`): `∀ index inst, s.instances.val[index]? = some inst → InstanceSyntax code index inst`. `InstanceSyntax` (:11) has `exportNames` (`wf_name` of each export) and `functionCodes` (`wf_funccode (code index inst.module function)` for each defined function index).

**`CoreFunctionsTyped`** (`R/Interp/Machine/Functions/Typing.lean:34`): `∀ function ∈ store.funcs.val, CoreFunctionTyped view code store function`. `CoreFunctionTyped` (:21): for `.Host _` it is `Functype_ok (Store.decodeFunction code store function).TYPE`. For `.Wasm ii fi` it is the existence of `inst index locals body` with the instance lookup, `code ii inst.module fi = .FUNC index locals body`, `SourceMachine.ModuleBindings (decodeStore view code store) (decodeInstance store inst) (Compiler.moduleSourceContext inst.module)`, and `Func_ok`.

**`FunctionsSupported`** (`R/SourceMachine/SupportedState.lean:14`): `∀ function ∈ s.FUNCS, match function.CODE with | .HOST _ => True | .FUNC _ _ body => Forall BinaryInstr body`.

**`CompiledFunctions`** (`R/Interp/Machine/Functions/CompiledFunctions.lean:33`): `∀ function ∈ store.funcs.val, FunctionCompiled code store function`. `FunctionCompiled` (:17) is quantified as `∀ instanceIndex functionIndex, function.code = .Wasm instanceIndex functionIndex → ∃ inst compiled signature declared body epilogue, ...` (instance lookup, compiled function lookup, `store.types` lookup, code equation, `FunctionTable`, decoded `TYPES` equation, `FunctionCode`). It is vacuous for `.Host`.

**`SegmentBounds`** (`R/Store/Invariant/Typing.lean:174`): `elements : ∀ element ∈ s.elems.val, element.refs.length < 2^32`, `data : ∀ segment ∈ s.datas.val, segment.bytes.length < 2^32`.

### CertifiedApiStore (CertifiedApi.lean:26)
- `exportBounds : Store.ExportBounds store`. `ExportBounds` (`R/Store/Api/ExportBounds.lean:19`): `∀ index inst, store.instances.val[index]? = some inst → ModuleExportBounds inst.module.module.env`. `ModuleExportBounds` (:10): export indices are in range and export names are `Nodup`.

### ExecutableInv own fields (ExecutableInv.lean:22-23)
- `segmentAccounting : Store.SegmentAccounting store` (`R/Store/Initialization/SegmentAccounting.lean:9`): `store.elems.length = (store.instances.val.map fun inst => inst.elems.length).sum`, and the same for `datas`.
- `capacities : Store.FunctionCapacities code store` (`R/Representation/StoreCapacity.lean:27`): `∀ function ∈ store.funcs.val, FunctionCapacity code store function`. `FunctionCapacity` (:13) is again `∀ instanceIndex functionIndex, function.code = .Wasm … → ∃ inst compiled typeIndex, …` (instance, compiled function, `Compiler.FunctionCapacity`, `TypeEntries`, `Interp.FunctionTable`, signature lookups). Vacuous for `.Host`.

### Decoding (`R/Representation/Store.lean`)
`CodeInterpretation := Nat → runtime.compiler.ExecutableModule → Nat → funccode` (:12). `decodeStore` (:112) maps funcs, globals, tables, memories, elems, datas. It never reads `externs`, `limits`, `id`, or any counter. `decodeFunction` (:102) reads only `s.types` and `s.instances`. A `.Host id` decodes to `⟨ty, default, .HOST id.val⟩`.

Derived facts already proved: `ExecutableInv.well_formed` (ExecutableInv.lean:27, `wf_store`), `ExecutableInv.source_typed` (:34, `Store_ok`, hosts included).

## 2. The empty store from `with_identity` [V body, I proof]

Extracted body (`Funs:63084-63106`) is a pure `ok {…}` with every vector `alloc.vec.Vec.new _` and every counter `0#usize`. The `MemoryBuffer` instance argument is unused.

| Field | Status |
|---|---|
| `shape.identity` | **Needs hypothesis** `0 < id.val`. Only non-trivial obligation. |
| `shape.functions/memories/tables/globals/elements/instances` | Vacuous, membership in `[]`. |
| `shape.canonicalTypes` | `List.nodup_nil`. |
| all limit fields | `0 ≤ _`. |
| all accounting fields | `0 = [].sum`. |
| `storeSyntax`, `exportBounds` | Vacuous, `[][index]? = some _` is false. |
| `typed`, `compiled`, `capacities`, `segmentBounds` | Vacuous. |
| `supported` | Vacuous, decoded `FUNCS = []`. |
| `segmentAccounting` | `0 = [].sum` twice. |

It holds for every `code`. `0 < id` is discharged outside the verified boundary: `src/runtime/native.rs:15-25` starts `NEXT_STORE` at 1 and uses `checked_add`. The native wrappers (`Store::new`, `with_limits`, `define_host`, `define_memory`, …, `native.rs:46-100`) are not extracted (DEVELOPMENT.md:131), so the `_with` functions are the verified surface.

## 3. Reusable lemmas [V]

### 3a. `ExecutableInv.update` and `CumulativeStoreMutation`

```lean
theorem ExecutableInv.update {M} {view} {code} {before after : runtime.store.Store M}
    (held : ExecutableInv view code before)
    (mutation : CumulativeStoreMutation view code before after) : ExecutableInv view code after
```
(`R/Integration/Api/ExecutableInv.lean:39`). Supporting: `CertifiedApiStore.update` (CertifiedApi.lean:40), `CertifiedSupportedStore.update` (CertifiedStore.lean:30), `CertifiedApiStore.change_code` (:48), `CertifiedSupportedStore.change_code` (`R/Integration/Execution/Ownership/CodeInterpretation.lean:13`).

```lean
structure CumulativeStoreMutation (view) (code) (before after : runtime.store.Store M) : Prop where
  metadata : Interp.FrameStoreMetadata before after   -- id, funcs, types, instances all EQUAL
  externs : after.externs = before.externs
  shape : Store.Shape view after
  segmentBounds : Store.SegmentBounds after
  extension : Extend_store (Store.decodeStore view code before) (Store.decodeStore view code after)
  segmentCounts : Store.SegmentCounts before after     -- elems.length and datas.length equal
  limits : after.limits = before.limits
```
(`R/Integration/Execution/Mutation/Certificate.lean:20`). `FrameStoreMetadata` is at `R/Interp/Relations/FrameStoreMetadata.lean:8`, `SegmentCounts` at `R/Store/Initialization/SegmentCounts.lean:8`.

Constructors, all in `R/Integration/Execution/Mutation/Operations.lean`:
- `:32 CumulativeStoreMutation.refl_of_shape (shaped : Shape view store) (sourceSyntaxBefore : StoreSyntax code store) (bounds : SegmentBounds store) : CumulativeStoreMutation view code store store`
- `:38 memory_mutation_cumulative_of_shape view code before after shaped sourceSyntaxBefore bounds (address : runtime.MemoryAddr) (object) (issued : before.memories.val[address.index.val]? = some object) (mutation : Interp.MemoryMutation view before after address object)`
- `:85 table_mutation_cumulative_of_shape view code before after shaped syntax bounds (address : runtime.TableAddr) object (replacement : U64) (issued : before.tables.val[address.index.val]? = some object) (mutation : TableMutation before after address object replacement) (reference : ReferenceShape before object.ty replacement)`
- `:113 memory_growth_cumulative_mutation_of_shape shaped _ bounds (issued : index.val < before.memories.length) (effect : MemoryGrowth view code before index delta out) (extension : Extend_store …) : CumulativeStoreMutation view code before out.2`. **Takes `extension` as a hypothesis.**
- `:125 table_growth_cumulative_mutation_of_shape shaped _ bounds (issued : index.val < before.tables.length) (owned : ReferenceShape before (before.tables.val[index.val]).ty value) (effect : TableGrowth before index delta value out) (extension : …)`. Same caveat.
- `:216 global_mutation_cumulative_of_shape view code before after shaped syntax bounds (value : val) (mutation : GlobalMutation before after value) (wellFormed : wf_val value) (owned : SourceMachine.Ownership.ValueOwned (ownershipBounds before) value)`
- Also `:98 segment_mutation…`, `:138/:148/:158/:169/:180/:188` fill/copy/init, `:202/:209` drops, `:246 core_mutation…`.

Mutation relations:
- `Interp.MemoryMutation view before after address object` (`R/Interp/Memory/MemoryMutation.lean:11`): `∃ buffer, after = {before with memories := before.memories.set address.index {object with buf := buffer}} ∧ (view buffer).length = (view object.buf).length`.
- `Interp.TableMutation before after address object replacement` (`R/Interp/State/TableMutation.lean:8`): `∃ words, after = {before with tables := before.tables.set address.index {object with elements := words}} ∧ words.length = object.elements.length ∧ ∀ word ∈ words.val, word ∈ object.elements.val ∨ word = replacement`.
- `Interp.GlobalMutation before after value` (`R/Interp/State/GlobalMutation.lean:7`): `∃ index old lo hi, before.globals.val[index.val]? = some old ∧ old.ty.mutability = .Var ∧ sourceType old.ty.valtype = Compiler.valueType value ∧ pairWords old.ty.valtype (lo,hi) = Compiler.encodeValue value ∧ (old.ty.valtype ≠ .V128 → hi = old.hi) ∧ after = {before with globals := before.globals.set index {old with lo,hi}}`.

Shape helpers: `Shape.memory_replace(_same_length)`, `table_replace(_same_length)`, `global_replace`, `memory_extend`, `table_extend` (`R/Representation/StoreInvariant.lean:94-253`); `global_encoded_shape`, `global_mutation_shape` (`R/Integration/Execution/Mutation/GlobalShape.lean:55,83`); `table_mutation_shape`, `table_mutation_extends` (`…/Mutation/TableShape.lean:38,56`).

### 3b. Prefix (append-only) transport, needed for define_host

`StagedPrefix before after` (`R/Store/Invariant/Rollback.lean:119`): `identity`, `limits` equal; `funcs`, `types`, `tables`, `memories`, `globals`, `instances`, `elems`, `datas` each as `after.X.val.take before.X.length = before.X.val`; `externs` **equal**; `instanceItems` equal. `StagedPrefix.refl/.trans` at `R/Store/Preparation/Staging.lean:8,20`.

- `decode_instance_prefix`, `decode_function_prefix`, `decode_store_prefix` (`R/Store/Invariant/Extension.lean:22,33,56`): decoded old objects are unchanged under a `StagedPrefix`.
- `store_prefix_extends (before after : store) (hb : wf_store before) (ha : wf_store after) hf hg ht hm he hd : Extend_store before after` (Extension.lean:108).
- `core_function_typed_prefix` and `staged_core_function_typed_old_wf view code before after shape sourceSyntax afterWf retained typed function present : CoreFunctionTyped view code after function` (`R/Store/Invariant/CoreTypingExtension.lean:30,54`).
- `supported_function_compiled_prefix shape retained (agrees : CodeAgreesOn before oldCode newCode) compiled : FunctionCompiled newCode after function` (`R/Store/Invariant/SupportedFunctionTables.lean:7`).
- `FunctionCapacity.staged retained agrees capacity : FunctionCapacity newCode after function` (`R/Store/Invariant/FunctionCapacities.lean:8`). Also `FunctionCapacities.metadata` (:77), `.code_agrees` (:85).
- `StagedPrefix.instance_shape`, `StagedPrefix.function_shape` (`R/Store/Invariant/ShapeAssembly.lean:16,25`).
- `StoreSyntax.instances_eq` (`R/Store/Invariant/SourceSyntax.lean:45`), `ExportBounds.instances_eq` (ExportBounds.lean:52), `SegmentAccounting.preserve` (SegmentAccounting.lean:37).
- `AllocationShape view store` (`R/Store/Preparation/AllocationShape.lean:11`) is `Shape` without the function, instance and instance-item fields. `Shape.allocated` (:26), `InternEffect.allocated` (:39), `FunctionStageEffect.allocated` (:77, template for "push one function"), `TableStageEffect.allocated` and `MemoryStageEffect.allocated` (`R/Store/Preparation/AllocationStorage.lean:6,46`), `GlobalStageEffect.allocated` (`R/Store/Preparation/AllocationInitializers.lean:8`). These are stated on instantiation-specific effect records, so their proof bodies are templates to copy, not directly callable.
- Monotonicity: `ReferenceShape.mono`, `GlobalShape.mono`, `TableShape.mono`, `InstanceShape.mono` (`R/Store/Api/Define.lean:39,50,59,69`). These take length inequalities, so they also work when `externs` grows.
- For `code` agreement with the same `code`, the witness is `fun _ _ _ _ => rfl`.

### 3c. define_* theorems (all in "raw effect" vocabulary, none mention the invariant)

- `define_global_effect ops allocator (ha : Platform.AllocCorrect allocator) s ty value (hbound : objectCount s ≤ Usize.max) (htype : ty.valtype = Interp.rawType value) (hv : ValueInStore s value)` (`R/Store/Api/Define.lean:97`). Post: `(∃ error, result = (.Err error, s)) ∨ ∃ globals words, runtime.value.encode value = .ok words ∧ globals.val = s.globals.val ++ [{ty, lo := words.1, hi := words.2}] ∧ objectCount s < s.limits.max_objects.val ∧ result = (.Ok ⟨s.id, alloc.vec.Vec.len s.globals⟩, {s with globals})`. **Only covers well-typed, owned values.**
- `define_memory_effect ops allocator ha view (laws : Platform.MemoryLaws ops view) s ty buffer hbound` (`R/Store/Api/DefineMemory.lean:27`). Post: error with unchanged store, or `∃ memories count, memories.val = s.memories.val ++ [{buf := buffer, maximum := ty.limits.max}] ∧ LimitsFit ty.limits 65536#u32 ∧ (view buffer).length = ty.limits.min.val * 65536 ∧ objectCount s < … ∧ count.val = s.memory_bytes.val + (view buffer).length ∧ count.val ≤ s.limits.max_memory_bytes.val ∧ result = (.Ok ⟨s.id, len s.memories⟩, {s with memories, memory_bytes := count})`.
- `define_table_effect ops allocator ha s ty hbound` (`R/Store/Api/DefineTable.lean:40`). Post: error unchanged, or `∃ tables elements count, elements.val = List.replicate ty.limits.min.val 0#u64 ∧ tables.val = s.tables.val ++ [{elements, ty := ty.elem, maximum := ty.limits.max}] ∧ LimitsFit ty.limits core.num.U32.MAX ∧ … ∧ result = (.Ok ⟨s.id, len s.tables⟩, {s with tables, table_elements := count})`.
- Supporting: `objectCount` (Define.lean:8), `Shape.object_count_bound` (:12), `room_spec` (:18, `@[step]`), `reserve_wrapper_eq` (:31), `LimitsFit` and `check_limits_spec` (DefineMemory.lean:6,16), `define_table_loop` (DefineTable.lean:6), `within_spec` (`R/Store/Api/Grow.lean:7`).
- Error classification only: `define_{table,global,memory}_errors` (`R/Store/Invariant/DefinitionErrors.lean:12,23,36`), `define_global_resource_causes` (`R/Store/Api/GlobalStagingCauses.lean:27`), `define_memory_resource_causes` (`R/Store/Api/MemoryAllocationCauses.lean:16`), `define_table_resource_causes` (`R/Store/Api/TableAllocationCauses.lean`).
- `intern_type_effect ops allocator ha s ty (hbound : objectCount s ≤ Usize.max) : intern_type … ⦃ result => InternEffect s ty result ⦄` (`R/Store/Invariant/InternTypes.lean:62`). `InternEffect` (:49) has three cases: error with `s` unchanged; existing index with `s` unchanged; appended (`types.val = s.types.val ++ [ty] ∧ ty ∉ s.types.val ∧ objectCount s < max ∧ count = signature_values + params + results ∧ count ≤ max_signature_values ∧ result = (.Ok (len s.types), {s with types, signature_values := count})`). Consequences: `InternEffect.lookup`, `.staged` (gives `StagedPrefix`), `.object_bound`, `.only_types` (`R/Store/Invariant/TypeStaging.lean:55,63,71,88`), `.allocated` (AllocationShape.lean:39). `decode_func_type_injective` at `R/Store/Invariant/TypeEquality.lean:103`.

### 3d. Growth and write effects; `R/Store/Api/` inventory

- `TableGrowth s index delta value result` (Grow.lean:59), `table_grow_effect ops allocator ha s index delta value (hindex : index.val < s.tables.length) (hsizes : ∀ t ∈ s.tables.val, t.elements.length ≤ U32.max) : grow_table_index … ⦃ result => TableGrowth s index delta value result ⦄` (:72).
- `MemoryGrowth view code s index delta result` (:128), `memory_grow_effect ops view laws code s index delta (hindex) (hsizes : ∀ m ∈ s.memories.val, (view m.buf).length ≤ 4294967296) (halign : ∀ m ∈ …, (view m.buf).length % 65536 = 0)` (:146). The failure branch of `MemoryGrowth` allows the buffer to be replaced by one with an equal `view`.
- `MemoryGrowth.shape`, `TableGrowth.shape` (needs `ReferenceShape s (s.tables.val[index.val]).ty value`), `.metadata` (`R/Store/Api/GrowthEffects.lean:8,46,77,85`), `.limits` (`GrowthLimits.lean:5,12`).
- `decode_memory_growth`, `decode_table_growth` (`MemoryGrowSource.lean:18`, `TableGrowSource.lean:10`) give the spec `fun_growmemory` / `fun_growtable`. `decode_memory_extends`, `decode_table_extends` (`R/Store/Invariant/ObjectExtension.lean:8,23`) give `Extend_meminst` / `Extend_tableinst`.
- `Spec.extend_store_refl/_trans` (`R/Spec/Extend.lean:46,171`), `Spec.extend_store_set_global/_mem/_table` (`R/Spec/Mutation.lean:82,91,100`), `Spec.extend_store_wf` (`R/Spec/ExtensionTyping.lean:4`).
- Values: `check_value_owned` (`Write.lean:12`), `check_value_eq` (`@[step]`, `R/Interp/Relations/Arguments.lean:71`, result is `checkOwner store.id value`), `value_type_exact`, `element_value_type_exact` (Write.lean:8,30), `value_type_ne`, `mut_ne` (`@[step]`, `R/Store/Linking/LinkEffects.lean:127,134`), `encode_global_shape`, `encode_reference_shape` (`R/Store/Invariant/ValueShape.lean:16,49`), `Interp.encode_value_spec` (`R/Representation/Values.lean:94`), `decode_encoded_value` (`R/Store/Invariant/ValueDecode.lean:15`), `decode_global_owned` (`R/Store/Invariant/ValueRead.lean:19`, the read-side lemma for `global`/`table_get`), `source_value_owned` (`R/Integration/Execution/Ownership/Entry.lean:11`), `Interp.source_value_wf`, `Interp.source_value_type` (Values.lean:59,52), `vec_set_current` (`R/Store/Invariant/SemanticApi.lean:6`), `decode_store_global_update`, `decode_store_table_update` (`R/Store/Invariant/InvalidWrite.lean:7,13`), `decode_store_memory_update` (Store.lean:120), `Interp.func_type_lookup` (`R/Interp/Invocation/Checks.lean:9`).
- Vec indexing: `vec_index_given` (`R/Interp/Relations/Fetch.lean:11`, public). The `index_mut` forms `global_index_given`/`global_index_mut_given` (`R/Interp/State/Globals.lean:6,14`) and `table_access_index_given`/`_mut_given` (`R/Interp/State/TableAccess.lean:6,14`) are **private duplicates**.

`R/Store/Api/` files (45): `ApiMetadata` (decoded function type), `Define` (objectCount, room, shape monotonicity, define_global effect), `DefineMemory`, `DefineTable`, `ExportBounds`, `Global{Effects,ErrorLoop,Errors,Loop,LoopCertificates,MapPreservation,Staging,StagingCauses,TypeMap}` (instantiation-time global staging, errors and causes), `Grow` (within, grow index effects), `GrowthEffects` (shape and metadata of growth), `GrowthLimits`, `Memory{AllocationCauses,AllocationLoop,BindingLoop,Staging,StagingCauses}` and `NewMemoryCauses` (instantiation-time memory staging), `MemoryCopy`, `MemoryCopyLoops`, `MemoryFill`, `MemoryInit` (bulk memory instructions), `MemoryGrowSource`, `TableGrowSource` (growth matches the spec function), `Table{AllocationCauses,AllocationLoop,BindingLoop,Staging,StagingCauses,Types}` and `NewTableCauses` (instantiation-time table staging), `TableCopy`, `TableCopyDistinct`, `TableFill`, `TableFillLoop`, `TableInit`, `TableInitLists` (bulk table instructions), `TableMemoryBindings`, `TableMemoryOrder` (binding and address order maps), `Write` (value type and check_value facts).

### 3e. Host functions

There is **no** existing lemma about adding a host function to a store. `R/Integration/Host/` (22 files) and `R/Interp/Host/` are entirely about calling hosts during execution. Relevant pieces:
- `decode_host_function view code store address function identity signature found host signatureFound : SpecExt.HostFunction (decodeStore view code store) address.index.val identity.val (signature.params.val.map Interp.sourceType) (signature.results.val.map Interp.sourceType)` (`R/Store/Invariant/HostSignature.lean:9`).
- `SpecExt.host_funcinst_ok` (`R/Spec/Typing/HostTyping.lean:10`); `decode_store_typed` handles `.Host` (`R/Store/Invariant/SourceStoreTyping.lean:38`).
- `Functype_ok` holds for every functype. Existing idiom at SourceStoreTyping.lean:67-69: `cases … with | mk_functype params results => cases params; cases results; constructor`.
- How each field treats `.Host id`: `FunctionShape` needs only `signature < types.length`; `CoreFunctionTyped` needs `Functype_ok` (always true); `FunctionsSupported` is `True`; `FunctionCompiled` and `FunctionCapacity` are vacuous.
- `R/Runtime/Contracts.lean:79-107` defines `HostWorldSound`, `HostRetention`, `HostLaws`. These are exactly the consumers of the new theorems: a callback must give `Inv afterCode after`, `CodeAgreesOn`, `Extend_store`, `Store_ok`, `FrameStorePrefix`, `externs.length` monotone, and `IssuedValue` for results. `lean/Itasca/Examples/TrapHost.lean:33` shows the proof shape for a trivial callback.

### 3f. Definitions requested

- `Store.ExternalIssued store : runtime.Extern → Prop` (`R/Store/Linking/LinkEffects.lean:288`): `.Func a => a.store = store.id → a.index.val < store.funcs.length`, and likewise `.Table`, `.Memory`, `.Global`. It has **no case for `ExternAddr` or `InstanceAddr`**.
- `Store.IssuedValue s value` (`R/Store/Invariant/IssuedValues.lean:7`): `.FuncRef (some a) => a.store = s.id → a.index.val < s.funcs.length`, `.ExternRef (some a) => a.store = s.id → a.index.val < s.externs.length`, otherwise `True`.
- `Store.ValueInStore s value` (`R/Store/Invariant/ValueShape.lean:8`): `Interp.ValueOwnedFits s.id value ∧` in-range index for references. `ValueOwnedFits` (`R/Representation/Values.lean:33`) is `a.store = store ∧ a.index.val < Usize.max ∧ a.index.val < U64.max`.
- Bridges: `issued_value_owned_or_foreign` (IssuedValues.lean:14, gives `ValueInStore ∨ ForeignValue`), `IssuedValue.in_store (issued) (owner : Interp.OwnedBy s.id value)` and `ValueInStore.issued` (`R/Store/Invariant/CheckedValues.lean:18,81`), `ForeignValue` (`R/Store/Invariant/ForeignValues.lean:8`).
- `Store.CodeAgreesOn store before after` (`R/Store/Invariant/FunctionTables.lean:92`): `∀ index inst, store.instances.val[index]? = some inst → ∀ function, after index inst.module function = before index inst.module function`. `installCode`, `install_code_agrees` at :99, :102.
- `Interp.FrameStorePrefix before after` (`R/Interp/Relations/FrameStorePrefix.lean:8`): `identity : after.id = before.id`, and `take`-prefix for `funcs`, `types`, `instances`. `.refl` (:25), `.trans` (:40), `FrameStoreMetadata.prefix` (:45).
- `Platform.MemoryLaws ops view` (`R/Platform/Memory.lean:13`): `read`, `write` (`∃ back, ops.bytes_mut m = .ok (view m, back) ∧ ∀ bytes, bytes.length = (view m).length → view (back bytes) = bytes`), `create`, `grow`. `Platform.AllocCorrect` at `R/Platform/Alloc.lean:12`. `Platform.Laws` bundle at `R/Platform/Laws.lean:13`.

## 4. Extracted signatures [V] and Rust bodies (`src/runtime/store.rs`)

All take `{M : Type} (platformMemoryBufferInst : runtime.platform.MemoryBuffer M)` first. Those marked (A) also take `{A : Type} (platformAllocInst : runtime.platform.Alloc A)` second.

| Function (Funs line) | Remaining args → result | Rust (lines) |
|---|---|---|
| `with_identity` (63084) | `(id : Std.Usize) (limits : runtime.store.StoreLimits) : Result (runtime.store.Store M)` | 119-137. Empty vectors, zero counters. |
| `define_host_with` (63110, A) | `(self) (ty : wasm_types.FuncType) (host_id : Std.U64) : Result ((core.result.Result runtime.FuncAddr runtime.ExecError) × (runtime.store.Store M))` | 166-183. `intern_type`, then `room`, then `reserve(funcs,1)`, then push `{signature, code := Host host_id}`. Returns `{store := id, index := old funcs.len}`. |
| `define_extern_with` (63157, A) | `(self) (identity : Std.U64) : Result ((Result runtime.ExternAddr ExecError) × Store M)` | 185-197. `room`, `reserve(externs,1)`, push. |
| `extern_identity` (63190) | `(self) (a : runtime.ExternAddr) : Result (core.result.Result Std.U64 runtime.ExecError)` | 199-202. Store check, then unchecked `externs[a.index]`. |
| `define_memory_with` (60424, A) | `(self) (ty : wasm_types.MemType) (buf : M) : Result ((Result runtime.MemoryAddr ExecError) × Store M)` | 204-233. `room`, `check_limits(…,65536)`, buffer length must equal `min*65536` (else BadArguments), `within` memory budget, reserve, push `{buf, maximum}`, add to `memory_bytes`. |
| `define_table_with` (60565, A) | `(self) (ty : wasm_types.TableType) : Result ((Result runtime.TableAddr ExecError) × Store M)` | 235-267. `room`, `check_limits(…,u32::MAX)`, `within` element budget, build `min` zero words, reserve, push, add to `table_elements`. |
| `define_global_with` (60302, A) | `(self) (ty : wasm_types.GlobalType) (value : runtime.Value) : Result ((Result runtime.GlobalAddr ExecError) × Store M)` | 269-287. `room`, `check_value` (store id only), type tag equality (else BadArguments), reserve, push encoded `{lo,hi,ty}`. |
| `func_type` (42627) | `(self) (a : runtime.FuncAddr) : Result (core.result.Result wasm_types.FuncType runtime.ExecError)` | 289-292. Store check, unchecked `types[funcs[a.index].signature]`. |
| `global` (63210) | `(self) (a : runtime.GlobalAddr) : Result (core.result.Result runtime.Value runtime.ExecError)` | 321-325. Store check, unchecked index, decode. |
| `set_global` (63231) | `(self) (a : runtime.GlobalAddr) (v : runtime.Value) : Result ((core.result.Result Unit runtime.ExecError) × (runtime.store.Store M))` | 327-338. Store check, `check_value`, unchecked index, BadArguments unless `Var` and type matches, then write `lo,hi`. |
| `memory` (63286) | `(self) (a : runtime.MemoryAddr) : Result (core.result.Result (Slice Std.U8) runtime.ExecError)` | 340-343. Store check, unchecked index, `bytes()`. |
| `memory_mut` (63307) | `(self) (a : runtime.MemoryAddr) : Result ((core.result.Result (Slice Std.U8) runtime.ExecError) × (core.result.Result (Slice Std.U8) runtime.ExecError → runtime.store.Store M))` | 345-351. Inline id comparison, unchecked index, `bytes_mut()`. The backward function writes the `Ok` slice (or the original slice for `Err`) through `bytes_mut_back`. |
| `table_size` (63336) | `(self) (a : runtime.TableAddr) : Result (core.result.Result Std.U32 runtime.ExecError)` | 353-356. |
| `table_get` (63358) | `(self) (a : runtime.TableAddr) (index : Std.U32) : Result (core.result.Result runtime.Value runtime.ExecError)` | 358-370. Element bounds checked (TableOutOfBounds), table index not. |
| `set_table` (63391) | `(self) (a : runtime.TableAddr) (index : Std.U32) (v : runtime.Value) : Result ((core.result.Result Unit runtime.ExecError) × (runtime.store.Store M))` | 372-384. Store check, `check_value`, type match (BadArguments), element bounds (Trap), write `encode(v).0`. |
| `export` (63574) | `(self) (a : runtime.InstanceAddr) («name» : Slice Std.U8) : Result (core.result.Result (Option runtime.Extern) runtime.ExecError)` | 386-405. Store check, unchecked `instances[a.index]`, linear scan, last match wins only because the loop stops at first hit. Uses `export_loop` (63558), `same_bytes` (63482). |
| `grow_memory_with` (63599) | `(self) (addr : runtime.MemoryAddr) (delta : Std.U32) : Result ((core.result.Result Std.U32 runtime.ExecError) × (runtime.store.Store M))` | 406-413. Store check, then `Ok(grow_memory_index(addr.index, delta))`. |
| `grow_table_with` (63622, A) | `(self) (addr : runtime.TableAddr) (delta : Std.U32) (v : runtime.Value) : Result ((core.result.Result Std.U32 runtime.ExecError) × (runtime.store.Store M))` | 414-426. Store check, `check_value`, unchecked table index, type match (BadArguments), then `Ok(grow_table_index(…, encode(v).0))`. |

Helpers: `runtime.store.Store.check` (42260), `check_value` (42400), `runtime.reserve` (42316), `runtime.value.encode` (42514), `runtime.value.decode` (42562), `room` (60278), `check_limits` (60406), `intern_type` (60863), `grow_table_index` (55606), `grow_memory_index` (55904), `within` (55568).

## 5. Proposed statements [I]

Preamble: `namespace Itasca.Runtime.Integration`, `open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Interp`. Suggested homes: support lemmas in new files under `R/Integration/Api/`, headline theorems in a new `lean/Itasca/Results/Store.lean` that must be imported from `lean/Itasca/Main.lean` (which lists every Results file).

### 5.0 Transport lemma (new, do this first)

```lean
theorem ExecutableInv.append_hosts {M : Type} {view : M → Slice U8} {code : CodeInterpretation}
    {before after : runtime.store.Store M} (held : ExecutableInv view code before)
    (retained : StagedPrefix before after) (shape : Shape view after)
    (instances : after.instances = before.instances)
    (elements : after.elems = before.elems) (datas : after.datas = before.datas)
    (fresh : ∀ function ∈ after.funcs.val,
      function ∈ before.funcs.val ∨ ∃ id, function.code = .Host id) :
    ExecutableInv view code after ∧
      Extend_store (decodeStore view code before) (decodeStore view code after)
```
Proof sketch: syntax via `StoreSyntax.instances_eq`; `wf_store` after via `decode_store_wf`; extension via `decode_store_prefix` + `store_prefix_extends`; `typed` old via `core_function_typed_prefix`, new host via the `Functype_ok` idiom; `supported` old via `decode_function_prefix`, new host is `True` after `simp only [decodeFunction, hostEq]`; `compiled` old via `supported_function_compiled_prefix` with `fun _ _ _ _ => rfl`, new host by contradiction on `.Host = .Wasm`; `segmentBounds` by rewriting `elements`/`datas`; `exportBounds.instances_eq`; `SegmentAccounting.preserve`; `capacities` old via `FunctionCapacity.staged`, new host vacuous. **Moderate.** Also a companion `Shape.of_allocated (shape : Shape view before) (allocated : AllocationShape view after) (retained) (instances : after.instances = before.instances) (functions : ∀ f ∈ after.funcs.val, FunctionShape after f) : Shape view after` (**trivial-moderate**, copy `shape_after_staging`, ShapeAssembly.lean:83).

This lemma also serves `define_memory/table/global` and makes `CumulativeStoreMutation` optional for them.

### 5.1 Fresh store. **Trivial.**

```lean
theorem runtime.store.Store.with_identity.spec {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (id : Usize)
    (limits : runtime.store.StoreLimits) (positive : 0 < id.val) :
    runtime.store.Store.with_identity memory id limits ⦃ store =>
      ExecutableInv view code store ∧ store.id = id ∧ store.limits = limits ∧
      Store.decodeStore view code store = ⟨[], [], [], [], [], []⟩ ⦄
```
`simp only [runtime.store.Store.with_identity, WP.spec_ok]`, then the nested anonymous constructor with `simp [alloc.vec.Vec.new]` or `intro _ h; cases h` per field.

### 5.2 define_host_with. **Moderate to hard** (most branches, Shape for the pushed function, error path with a changed store).

```lean
theorem runtime.store.Store.define_host_with.spec {M A : Type}
    (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (ty : Itasca.wasm_types.FuncType) (host : U64) :
    runtime.store.Store.define_host_with memory allocator store ty host ⦃ out =>
      ExecutableInv view code out.2 ∧ StagedPrefix store out.2 ∧
      Extend_store (decodeStore view code store) (decodeStore view code out.2) ∧
      ∀ address, out.1 = .Ok address →
        address.store = store.id ∧ address.index.val = store.funcs.length ∧
        ExternalIssued out.2 (.Func address) ∧ ValueInStore out.2 (.FuncRef (some address)) ∧
        HostFunction (decodeStore view code out.2) address.index.val host.val
          (ty.params.val.map sourceType) (ty.results.val.map sourceType) ⦄
```
Builds on `intern_type_effect`, `InternEffect.{staged,lookup,object_bound,allocated}`, `room_spec`, `reserve_wrapper_eq`, `FunctionStageEffect.allocated` proof as template, 5.0, `decode_host_function`. `StagedPrefix` gives `FrameStorePrefix`, equal `externs` and equal `limits`.

### 5.3 define_extern_with. **Moderate** (no existing relation fits; every field but `shape` should close by definitional unfolding because nothing else reads `externs`).

```lean
theorem runtime.store.Store.define_extern_with.spec … (law) (held) (identity : U64) :
    runtime.store.Store.define_extern_with memory allocator store identity ⦃ out =>
      ExecutableInv view code out.2 ∧ FrameStoreMetadata store out.2 ∧ out.2.limits = store.limits ∧
      decodeStore view code out.2 = decodeStore view code store ∧
      ((∃ error, out = (.Err error, store)) ∨
        ∃ externs : alloc.vec.Vec U64, externs.val = store.externs.val ++ [identity] ∧
          out = (.Ok ⟨store.id, alloc.vec.Vec.len store.externs⟩, {store with externs}) ∧
          ValueInStore out.2 (.ExternRef (some ⟨store.id, alloc.vec.Vec.len store.externs⟩))) ⦄
```
Builds on `room_spec`, `reserve_wrapper_eq`, the four `.mono` lemmas, `Spec.extend_store_refl` (via `well_formed`) if `Extend_store` is wanted.

### 5.4 define_memory_with. **Moderate.**

```lean
theorem runtime.store.Store.define_memory_with.spec … (law) (laws : Platform.MemoryLaws memory view)
    (held) (ty : Itasca.wasm_types.MemType) (buffer : M) :
    runtime.store.Store.define_memory_with memory allocator store ty buffer ⦃ out =>
      CumulativeStoreMutation view code store out.2 ∧
      ((∃ error, out = (.Err error, store)) ∨
        ∃ address, out.1 = .Ok address ∧ address.store = store.id ∧
          address.index.val = store.memories.length ∧ ExternalIssued out.2 (.Memory address) ∧
          out.2.memories.val = store.memories.val ++ [{buf := buffer, maximum := ty.limits.max}]) ⦄
```
`ExecutableInv` follows by `held.update`. Builds on `define_memory_effect`, `MemoryStageEffect.allocated` proof body, `decode_store_prefix` + `store_prefix_extends` (or 5.0).

### 5.5 define_table_with. **Moderate.** Same shape, `ty : Itasca.wasm_types.TableType`, no `laws`, new table `{elements, ty := ty.elem, maximum := ty.limits.max}` with `elements.val = List.replicate ty.limits.min.val 0#u64`. Builds on `define_table_effect`, `TableStageEffect.allocated` proof body.

### 5.6 define_global_with. **Moderate** (needs a total variant of the effect lemma).

```lean
theorem runtime.store.Store.define_global_with.spec … (law) (held)
    (ty : Itasca.wasm_types.GlobalType) (value : runtime.Value) (issued : IssuedValue store value) :
    runtime.store.Store.define_global_with memory allocator store ty value ⦃ out =>
      CumulativeStoreMutation view code store out.2 ∧
      ((∃ error, out = (.Err error, store)) ∨
        ∃ address, out.1 = .Ok address ∧ address.store = store.id ∧
          address.index.val = store.globals.length ∧ ExternalIssued out.2 (.Global address) ∧
          ty.valtype = rawType value ∧
          (decodeStore view code out.2).GLOBALS = (decodeStore view code store).GLOBALS ++
            [⟨.mk_globaltype (decodeMut ty.mutability) (sourceType ty.valtype), sourceValue value⟩]) ⦄
```
Case split with `issued_value_owned_or_foreign`. Owned and matching type: `define_global_effect`. Otherwise unfold and use `check_value_eq` / `value_type_ne` to reach `(.Err _, store)`. Shape via `encode_global_shape` and the `GlobalStageEffect.allocated` proof body. Decoded value via `decode_encoded_value`.

### 5.7 set_global. **Moderate.**

```lean
theorem runtime.store.Store.set_global.spec … (held) (address : runtime.GlobalAddr)
    (value : runtime.Value) (issued : ExternalIssued store (.Global address))
    (valueIssued : IssuedValue store value) :
    runtime.store.Store.set_global memory store address value ⦃ out =>
      CumulativeStoreMutation view code store out.2 ∧
      (∀ error, out.1 = .Err error → out.2 = store) ∧
      (out.1 = .Ok () → GlobalMutation store out.2 (sourceValue value)) ⦄
```
Build `GlobalMutation` with `lo,hi` from `encode`: type equation from `source_value_type`, words from `encode_value_spec`, `hi = old.hi` for non-V128 because `encode_global_shape` gives `hi = 0` and `held.shape.globals` gives `old.hi = 0`. Then `global_mutation_cumulative_of_shape` with `source_value_wf` and `source_value_owned`. Error branches return `{self with globals := index_mut_back g}`, closed by `vec_set_current`. Rejection uses `mut_ne`, `value_type_ne`.

### 5.8 set_table. **Moderate.**

```lean
theorem runtime.store.Store.set_table.spec … (held) (address : runtime.TableAddr) (index : U32)
    (value : runtime.Value) (issued : ExternalIssued store (.Table address))
    (valueIssued : IssuedValue store value) :
    runtime.store.Store.set_table memory store address index value ⦃ out =>
      CumulativeStoreMutation view code store out.2 ∧
      (∀ error, out.1 = .Err error → out.2 = store) ⦄
```
`TableMutation` with `words := object.elements.set index word` (`List.mem_or_eq_of_mem_set`), `ReferenceShape` from `encode_reference_shape`, then `table_mutation_cumulative_of_shape`. Template for the extracted steps: `table_set_effect` (`R/Interp/State/TableAccess.lean:75`).

### 5.9 memory_mut write-back. **Moderate** (closure-valued postcondition is unusual).

```lean
theorem runtime.store.Store.memory_mut.spec … (laws : Platform.MemoryLaws memory view) (held)
    (address : runtime.MemoryAddr) (issued : ExternalIssued store (.Memory address)) :
    runtime.store.Store.memory_mut memory store address ⦃ out =>
      (address.store ≠ store.id ∧ out.1 = .Err .WrongStore ∧ ∀ reply, out.2 reply = store) ∨
      ∃ object, address.store = store.id ∧
        store.memories.val[address.index.val]? = some object ∧ out.1 = .Ok (view object.buf) ∧
        (∀ bytes : Slice U8, bytes.length = (view object.buf).length →
          MemoryMutation view store (out.2 (.Ok bytes)) address object ∧
          CumulativeStoreMutation view code store (out.2 (.Ok bytes)) ∧
          (decodeStore view code (out.2 (.Ok bytes))).MEMS =
            (decodeStore view code store).MEMS.set address.index.val
              ⟨(decodeMemory view object).TYPE, decodeBytes bytes.val⟩) ∧
        ∀ error, CumulativeStoreMutation view code store (out.2 (.Err error)) ⦄
```
Builds on `laws.write`, `memory_mutation_cumulative_of_shape`. Template for the extracted steps: `R/Interp/Memory/MemoryDispatch.lean:60-110`.

### 5.10 grow_memory_with. **Moderate** (must derive `Extend_store` itself).

```lean
theorem runtime.store.Store.grow_memory_with.spec … (laws) (held) (address : runtime.MemoryAddr)
    (delta : U32) (issued : ExternalIssued store (.Memory address)) :
    runtime.store.Store.grow_memory_with memory store address delta ⦃ out =>
      CumulativeStoreMutation view code store out.2 ∧
      ((address.store ≠ store.id ∧ out = (.Err .WrongStore, store)) ∨
        ∃ pages, address.store = store.id ∧ out.1 = .Ok pages ∧
          MemoryGrowth view code store address.index delta (pages, out.2)) ⦄
```
`memory_grow_effect` (sizes and alignment from `held.shape.memories`, `MemoryShape.length_bound`), `MemoryGrowth.shape`, a new helper `MemoryGrowth.extends : Extend_store …` (failure branch: `rw` the decode equality then `Spec.extend_store_refl`; success branch: `Spec.extend_store_set_mem` + `decode_memory_extends`, modelled on Operations.lean:38-84), then `memory_growth_cumulative_mutation_of_shape`.

### 5.11 grow_table_with. **Moderate.** Same shape with `(law)`, `(value : runtime.Value)`, `(valueIssued : IssuedValue store value)`, three rejection outcomes (`WrongStore` twice, `BadArguments`) all with `out.2 = store`, and success `TableGrowth store address.index delta word (n, out.2)`. Builds on `table_grow_effect`, `encode_reference_shape`, `element_value_type_exact`, `TableGrowth.shape`, a new `TableGrowth.extends` via `Spec.extend_store_set_table` + `decode_table_extends`, then `table_growth_cumulative_mutation_of_shape`.

## 6. Obstacles and things to decide

1. **`0 < id.val`** is required for the fresh store and comes from unverified native code. Report it as a stated premise, not a trust-boundary change.
2. **`define_host_with` error path changes the store** [V, Funs:63124-63148]. If `intern_type` appends a type and then `room` or `reserve` fails, the result is `(Err, self1)` with one more type. The invariant still holds (5.0 with no new function), but "Err implies unchanged" is false for this one operation. This is observable Rust behavior worth flagging to the user: a failed `define_host` can permanently consume one object slot and signature budget.
3. **No existing relation covers `define_host_with` or `define_extern_with`.** `CumulativeStoreMutation` requires equal `funcs`, `types`, `externs`. `StagedPrefix` requires equal `externs`. Hence 5.0 for host and a direct proof for extern.
4. **Unchecked indexing makes the extracted functions `fail`** for a same-store out-of-range handle (`extern_identity`, `global`, `set_global`, `memory`, `memory_mut`, `table_size`, `table_get`, `set_table`, `func_type`, `export`, `grow_memory_with`, `grow_table_with`). Each needs an issued premise. `ExternalIssued` has no `ExternAddr` or `InstanceAddr` case: use `IssuedValue store (.ExternRef (some a))` for `extern_identity`, and a plain `a.store = store.id → a.index.val < store.instances.length` for `export`.
5. **Value arguments need `IssuedValue`.** `check_value` only compares store ids. A same-store reference with an out-of-range index would be encoded and stored, violating `ReferenceShape`; with index `u64::MAX` the `+ 1` in `encode` even fails. Without the premise the preservation theorems are false.
6. **Platform premises.** `AllocCorrect` is needed by `define_host/extern/memory/table/global_with` and `grow_table_with`. `MemoryLaws` is needed by `define_memory_with` (`read`), `grow_memory_with` (`read`, `grow`), `memory_mut` (`write`), `memory` (`read`). The task statement mentioned only `MemoryLaws`.
7. **`memory_mut` backward function needs a length premise.** `MemoryLaws.write` says nothing when the written slice has a different length, so the theorem must quantify over `bytes.length = (view object.buf).length`. Rust's `&mut [u8]` guarantees this; in the model it is explicit.
8. **Growth `Extend_store` is currently supplied by the source transition**, not derived from the raw effect (Operations.lean:110-123 doc comment). Two small new lemmas (`MemoryGrowth.extends`, `TableGrowth.extends`) are needed.
9. **`define_global_effect` assumes a well-typed owned value.** The public theorem needs the rejection branches too.
10. **Private duplicated helpers.** `global_index_given`/`global_index_mut_given` and `table_access_index_given`/`_mut_given` are private copies of the same two facts. The new proofs need them a third time. Cleanest is one public pair next to `vec_index_given` in `R/Interp/Relations/Fetch.lean` and deleting the private copies, which touches two existing files.
11. **No handle-persistence lemmas.** Nothing states that `ExternalIssued` / `IssuedValue` / `ValueInStore` survive store growth. Callers composing several API calls will want them. `FrameStorePrefix` covers only `funcs`; tables, memories, globals and externs need explicit length monotonicity (for example by returning `StagedPrefix` or `CumulativeStoreMutation` plus the append equations, as drafted).
12. **`objectCount s ≤ Usize.max`** is a precondition of `room_spec`, `intern_type_effect`, and all three define effects. Derive it from `held.shape.object_count_bound` and `scalar_tac` on `max_objects`; after interning use `InternEffect.object_bound`.
13. **No obstacle for host functions themselves.** I found no invariant field that a new `.Host` function fails to satisfy, and no API function whose behavior breaks a field once the premises in items 4, 5 and 7 are present [V for definitions, I for the overall claim].
14. Process notes from AGENTS.md: handwritten Lean only, so the required check is `just prove`; no `sorry`/axioms; `Results/Store.lean` needs an import in `lean/Itasca/Main.lean` and matching entries in README/`lean/README.md` claims.
