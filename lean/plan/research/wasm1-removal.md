<!-- Research notes gathered on 2026-11-12 by a read-only research agent for PLAN.md. Statements marked [V] were read in the code; [I] are the agent's inferences and were not compiled. Line numbers refer to commit 81347267 and will drift. -->

# Wasm 1.0 removal inventory for itasca

Method: `rg`, file reads, and inline Python over stdin for import-graph and counting. I created and modified nothing; `lake`, `make`, `just`, `cargo` were not run. (`git status` now shows untracked `lean/PROOF_ENGINEERING.md`, `lean/plan/`, `lean/scripts/`; they are not mine.) "V" = verified by reading, "I" = inferred. Paths are repo-relative.

## 0. Headline facts

1. **Dependency direction (V): the Wasm 2.0 instruction grammar is defined as an extension of the Wasm 1.0 grammar.** `lean/Itasca/Binary/Wasm1/*` and `lean/Itasca/Wasm1/Complete/*` are the shared scalar base and cannot be deleted. Only `Binary/Wasm1/Subset.lean` is Wasm1-only there.
2. **Problem with the two-stage idea: Stage 1 is one atomic red-to-green step on the Lean side.** After a single-variant re-extraction, 82 non-example files (plus 12 example files) that name `.Wasm1` stop elaborating, including the lowest layers.
3. **The single-variant trick is still worth keeping** (I). Threading-only theorems stay untouched, and unit-like eta makes any `profile` definitionally `.Wasm2`, so the 847 `.Wasm2`-literal lines in `Runtime/Compiler` keep applying.
4. **The runtime Wasm1 precheck is an independent slice** that can be removed first, with the enum still two-variant.

## 1. Rust inventory (all V)

### 1a. Behavior-affecting sites

| Site | Function | Wasm1 arm | Wasm2 arm |
|---|---|---|---|
| `src/code.rs:1544` | `check_opcode` | rejects `0x1c,0x25,0x26,0xc0-0xc4,0xd0-0xd2,0xfc,0xfd` with `UnrecognizedOpcode` | `Ok(())` |
| `src/code.rs:1556` | `check_block_type` | allows only `Empty` or `Value(I32/I64/F32/F64)`, else `InvalidBlockType` | `Ok(())` |
| `src/code.rs:1572` | `check_table_byte` | `call_indirect` table byte must be 0, else `ReservedByteNotZero` | `Ok(())` |
| `src/code.rs:1587` | `check_table_target` | each `br_table` target must satisfy `same_types` with the first, else `TypeMismatch` | `Ok(())` |
| `src/module.rs:438` (449-460) | `decode_value_type` | `0x7b`, `0x70`, `0x6f` give `InvalidType` | V128 / FuncRef / ExternRef |
| `src/module.rs:492` (515-522) | `decode_func_type` | `results.len() > MAX_RESULTS` (1) gives `Error::TooManyResults` | nothing |
| `src/module.rs:550` (558-561) | `decode_elem_type` | `0x6f` gives `InvalidType` | ExternRef |
| `src/module.rs:585` | `check_table_count` | `table_types.len() > MAX_TABLES` (1) gives `Error::MultipleTables` | nothing |
| `src/module.rs:759` (800, 810, 823) | `decode_const_expr` | `0xd0`, `0xd2`, `0xfd` give `InvalidConstExpr` | ref.null / ref.func / v128.const |
| `src/module.rs:1172` | `decode_segment_index` | `(index_or_flags, pos, false)`, the word is the index | flags 0 gives index 0; 2 reads an explicit index; else `InvalidType(0xff)` |
| `src/module.rs:1198` (1205-1259) | `decode_element_header` | tag is the table index, active, FuncRef, index vector | 8 flag forms (tag ≤ 7) |
| `src/module.rs:1351` | `decode_data_count` | `UnknownSection(SECTION_DATA_COUNT)` | reads count into `env.data_count` |
| `src/module.rs:1568` (1575-1576) | `decode_data_segment` | always active | `Wasm2 if tag == 1 => Passive`, else active |
| `src/runtime/store.rs:495` | `fn wasm1` | `true` | `false` |
| `src/runtime/store/instantiate.rs:183-197` | `prepare_instance` | runs `check_element_bounds` (:384) then `check_data_bounds` (:413) over all segments before publication | skipped |

Things that become dead with the Wasm1 arms:
- `limits::MAX_TABLES` (`src/limits.rs:16`), `limits::MAX_RESULTS` (:25).
- `Error::MultipleTables` (`src/error.rs:91`, :145) and `Error::TooManyResults` (:151). These are public variants, and removing them changes the extracted `error.Error` inductive.
- `check_element_bounds`, `check_data_bounds`, `fn wasm1`.

Things that stay: `same_types` (also used at `code.rs:1745`), `OpError::InvalidBlockType` (`signature.rs:139`), `OpError::ReservedByteNotZero` (`code.rs:572`).

### 1b. Thread-only signatures

- `src/module.rs`: `validate_module` 305 (pub), `decode_value_types` 465, `decode_table_type` 567, `decode_global_type` 605, `decode_type_section` 873, `decode_import` 894, `decode_import_section` 955, `decode_table_section` 990, `decode_global_section` 1029, `decode_element_initializer` 1276, `decode_element_initializers` 1296, `decode_element` 1320, `decode_element_section` 1331, `decode_env_section` 1378, `validate_env` 1402, `validate_env_with` 1411, `decode_locals` 1463, `validate_code_entry_with` 1507, `validate_code_entry` 1555, `decode_data_section` 1595, `validate_tail` 1618, `validate_tail_with` 1632.
- `src/code.rs`: `enter_info` 1687, `enter` 1716, `branch_table_with` 1859, `branch_table` 1903, `call_indirect_info` 1933, `call` 1960, `body_loop` 2000, `step_profile` 2025, `validate_body_with` 2106.
- `src/stream.rs`: field `CodeBatch.profile` 134, `validate_next` 232-247 (reads `self.profile`), `validate_streaming` 274 (pub), `validate_remaining` 293, `submit_code_batches` 353 (sets the field at 379), `validate_module_slice` 507.
- `src/runtime/compiler/mod.rs`: field `ExecutableModule.profile` 153, `compile_default_with` 272, `compile_with` 284 (sets the field at 335), unit test at 773.
- `src/runtime/native.rs`: `compile` 128, `compile_with_limits` 140 (both pub).

Comment-only mentions: `src/types.rs:7,126`, `src/limits.rs:27,31`, `src/error.rs:35`, `src/code.rs:1,90,1279,1538,1975,1999,2024,2098,2562`.

### 1c. Public API mentioning the profile

- `pub enum ValidationProfile { Wasm1, Wasm2 }` at `src/lib.rs:74`; crate docs at `lib.rs:1-10` use `Wasm1`.
- `validate_module(data, profile)`, `validate_streaming(module_id, profile, ...)`.
- `CodeBatch::profile()` at `stream.rs:154`.
- `ExecutableModule::profile()` at `runtime/compiler/mod.rs:216`.
- `runtime::compile`, `runtime::compile_with_limits`.
- There is no `Module::profile()` and `Config` has no profile field (`stream.rs:33`).
- Docs: `README.md:8-13,24,29-34,90,100`, `DEVELOPMENT.md:12,15,114,167,217,224-225,229`, `AGENTS.md:4`, `lean/README.md`, `lean/PROOF_GUIDE.md` (about 20 lines), `lean/Itasca/Runtime/README.md:192-200,229,255`, `fuzz/README.md`, `tests/spec2/README.md:8,36,57`.

### 1d. Tests, fuzz, examples

Wasm 1.0 only:
- `tests/spec_tests.rs` (wasmparser `WasmFeatures::WASM1`, lines 64, 280) with fixtures `tests/spec/{valid,invalid}` (778 and 1641 files).
- `tests/wasm1_profile.rs`.
- `examples/wast_extract.rs` (generates `tests/spec`).
- `fuzz/fuzz_targets/wasm1_smith.rs`, `wasm1_execute.rs`, `raw_bytes.rs:22`; `fuzz/Cargo.toml:22`.
- `tests/runtime_wast.rs:13-18` (`wasm1_execution_corpus`).
- Submodule `tests/third_party/wasm-spec` (pinned at wg-1.0).
- `tests/support/mvp_binary.rs` (`normalize_to_wasm1`). It is `#[path]`-included by 7 fuzz targets and 2 tests, but only called under Wasm1.

Mixed, need the Wasm1 half removed:
- `tests/runtime_api.rs:97,121` (segment-failure effects per profile).
- `tests/runtime_differential.rs:130-136,172,199`.
- `tests/compiler_tests.rs:17-26,92`.
- `tests/wasm2_scalar_extensions.rs:45`, `tests/wasm2_simd.rs:151`, `tests/wasm2_boundaries.rs:323` ("Wasm1 rejects" asserts).
- `tests/support/runtime_wast.rs:217,248,669,799`.
- `tests/support/runtime_differential.rs:289,434,643`.
- `tests/support/runtime_numeric.rs:236-256`.
- `fuzz/fuzz_targets/runtime_compile.rs:12-16` (first byte selects the profile), `runtime_smith_support.rs:5-6`, `fuzz/scripts/runtime_{smoke,instrumented}.py` (seeds per profile).
- `examples/runtime_bench.rs` (11 Wasm1 uses; `oracle_engine` at 271).

Wasm2 only (stay): `tests/spec2_tests.rs`, `tests/spec2/`, `tests/runtime_adversarial.rs`, `tests/support/runtime_scenarios.rs`, `fuzz/.../wasm2_*.rs`.

The Wasm 1.0 corpus cannot simply be re-run at Wasm2 (I): it relies on historical segment prechecks, strict `br_table`, and flag-less segment encodings.

## 2. Lean definitions parameterized by profile (V unless noted)

About 157 defs, structures and inductives mention a profile. Most only thread it. The ones that branch:

### Trivial at Wasm2 (delete)

- `Profile.FuncType` (`Profile/Types.lean:17`): `| .Wasm2 => True`.
- `Profile.Environment` (:29): two `∀ ft, True` conjuncts.
- `Profile.Instructions` (`Profile/Instructions.lean:17`): `| .Wasm2 => True`.
- `ModuleBinary.ValueTypeAllowed` (`Binary/Module.lean:129`), `ElemTypeAllowed` (:135), `ConstAllowed` (:206): `| _, _ => True`.
  - Hence `ValueTypeEncodingFor`/`ElemTypeEncodingFor` (:145, :152) reduce to the plain encodings.
  - `ModuleTypesAllowed` (:427) and `ModuleSections.ImportAllowed` (`Module/Sections/Imports.lean:25`) are all-True.
- `Frames.ProfileFrames` (`Wasm2/ProfileFrames.lean:103`): `profile = .Wasm1 → Wasm1Frames root frames`, vacuous. `Saved.Wasm1Ok` and `Wasm1Frames` go with it.
- `Wasm1.Instruction(s)`, `SameTargets`, `Leaf` (`Wasm1/ProfileSyntax.lean`).
- Every `profile = .Wasm1 → …` clause (74 lines in 30 files):
  - `Wasm2.Validated` last conjunct (`Wasm2/BodySpec.lean:44`).
  - `Wasm2.State.running/closed` and `Pending.profileFrames/profileConsumed/opcode` (`Wasm2/Invariant.lean:38-47,118-121`).
  - `CallbackTrace.AcceptedBody` (`Wasm2/Trace/Correspondence.lean:32`).
  - `CodeEntry.AcceptedTrace` (`Profile/EntryTrace.lean:41`).
  - `LeafContract` (`Wasm2/Complete/Leaf.lean:118`), `Program`/`AtomProgram` (`Wasm2/Complete/Program.lean:29,44`).
  - `ModuleEnv.Valid.tableCount` (`Module/Env/Basic.lean:58`).
  - `ModuleConditions.table_count` (`Module/Elab/Elaboration.lean:90`).
  - `ImportValid`, `ImportsValid.tables`, `SectionValid` slot 4 (`Module/Env/Requirements.lean:25,47,157`).
  - `Effect.tables` (`Module/Env/Effects.lean:46`).
- `(hwasm2 : profile ≠ .Wasm1)` hypotheses: 14 lines in 7 files (`Wasm2/Simd/Sound.lean` ×8, `Simd/Reader.lean:24`, `References/{Reader,Step}.lean`, `NumericExt/Sound.lean:27`, `Complete/LeafContracts.lean:311`, `Invariant.lean:167`).
- `profile = .Wasm2 ∧/→` guards: `ModuleEnv.Payload` slot 10 (`Module/Env/Slots.lean:32`), `Effect.dataCount` (`Effects.lean:69`), `Module/Sections/DataCount.lean:77`, `Module/Env/DispatchComplete.lean:112`.
- Runtime `PrecommitError` (`Runtime/Store/Invariant/PrecommitError.lean:17`): `.Trap .MemoryOutOfBounds | .Trap .TableOutOfBounds => profile = .Wasm1`, so False at Wasm2.

### Real content at Wasm2 (must survive under a profile-free name)

- `Profile.FuncTypeWithinLimits` (`Profile/Types.lean:24`) and `EnvironmentWithinLimits` (:38): already profile-free.
- `Profile.FuncTypeAdmissible` (:44): `| .Wasm2 => params ≤ MAX_MULTI_VALUE_PARAMS ∧ results ≤ MAX_MULTI_VALUE_RESULTS`, which equals `FuncTypeWithinLimits`.
- `Profile.BodyEncoding` (`Profile/BodySpec.lean:19`): `| .Wasm2 => Wasm2.BodyEncoding data ops`.
- `Profile.Body` (:27): at Wasm2 the same as `Wasm2.Validated` (proved by `Body.iff_validated`, `Profile/Body.lean:32`). Merge the two.
- `Profile.BodyBytes` (`Profile/CodeEntry.lean:20`): `| .Wasm2 => ∃ tokens, ModuleBinary.Rep Wasm2.TokenEncoding tokens bytes ∧ Wasm2.BodyTokens tokens ops`.
- `Profile.CodeEncoding` (:28), `CodeEncodingWithinLimits` (:36), `EntryTyped` (:53; drop the `signature`, `instructions`, `locals_allowed` fields), `Entry` (:70).
- `ModuleBinary.SegmentIndexEncoding` (`Binary/Module.lean:304`): `(flags = 0 ∧ index = 0 ∧ explicit = false ∧ bytes = []) ∨ (flags = 2 ∧ explicit = true ∧ IndexEncoding index bytes)`.
- `ElementEncodingFor` (:313): `Wasm2ElementEncoding`. `DataEncodingFor` (:369): `Wasm2DataEncoding`.
- `DataCountSectionEncoding` (:466): `PaddedEncoding 12#u8 StartEncoding none value bytes`.
- `ModuleEncodingWith codeRel value bytes profile` (:474): keeps everything, plus `DataCountValid value`.
- `ModuleElements.HeaderEncoding` (`Module/Sections/ElementHeader.lean:21`): inductive indexed by profile. Drop the `legacy` constructor (`.Wasm1`); the other 8 are `.Wasm2`.
- `CodeEntry.Typed` (`Module/Code/Context.lean:58`): keep `type_lt`, `typed`, `declared`.
- `ModuleElaboration.ModuleConditions` (`Elaboration.lean:88`): keep `unique_exports` and `memory_count ≤ 1`; `arity` is trivial.
- `ModuleElaboration.Profile` (`Module/Elab/Profile.lean:34`): keep `ModuleConditions` and `declared : DeclaredReferences.Module (moduleOf raw)`. `bodies` reduces to index-in-range plus a length equality, both already in `Elaborates`.
- `ModuleEnv.Valid` (`Module/Env/Basic.lean:54`): everything except `tableCount`. This includes `distinctExports`, `references`, `memoryCount`, and `types` (now the signature caps).
- `ModuleSound.Validated` (`Module/Soundness.lean:24`).
- `ModuleBinary.ModuleEncodingWithinLimits` (`Module/Limits.lean:75`).
- `StreamCompleteRegions.Certificate` (`Stream/DriverRegions.lean:84`): field `profile : Profile.Environment …` is trivial; the rest is real.
- `Contracts.lean`:
  - `StreamBatch.Issued.profile` field (:132).
  - `StreamScheduler.CallbacksTotal` (:179) and `Provenance` (:196): only the `issued.profile = profile` premise.
  - `StreamAcceptingScheduler.Valid` (:225): `validation_profile` and `profile` fields trivial; `limits` and typed/encoded entries real.
  - `ValidQueue` (:237), `Accepts` (:247).
- Runtime:
  - `Integration.CompilationCertificate` (`Runtime/Integration/Compilation/Certificate.lean:26`): drop `executable.profile = profile`.
  - `Compiler.ValidCompilationSource`/`CompileEligible` (`Runtime/Compiler/Module/CompilationAvailable.lean:13,24`).
  - `SourceFrameCapacity`/`FunctionCapacity` (`Runtime/Representation/FunctionCapacity.lean:14,29`, use `Profile.BodyEncoding profile`).
  - `ProfileEnvironment` (`Runtime/Compiler/Module/SchedulerProfileSafety.lean:9`): becomes `EnvironmentWithinLimits`.
  - `ReaderOpcode : ValidationProfile → U8 → Prop` (`Runtime/Compiler/Local/Relations/Syntax/ReaderOpcode.lean:111`). `ReaderOpcode .Wasm1` is used as "the base opcode set handled by `code.step`" (`…/Reader/Replay/OpcodeClassification.lean:20-26,65`). It needs a profile-free base predicate, not a deletion.
- `ProfileConsumed` (`Binary/ProfileEncoding.lean:54`): `| .Wasm2 => Wasm2.Consumed`. Replace by `Wasm2.Consumed`.

### Wasm1 defaults

`(profile : ValidationProfile := .Wasm1)` appears on 65 lines in 32 files (full list in section 4). `optParam ValidationProfile .Wasm1` appears in 5 inductive signatures: `Module/Sections/Tail.lean:33`, `Module/Env/Effects.lean:31`, `Module/Sections/Imports.lean:18`, `Module/Env/Run.lean:22`, `Module/Env/Chain.lean:20`.

## 3. Deletable files versus misleading names

### Dependency facts (V)

- `Binary/Wasm2/Encoding.lean:49-51`: `Wasm2.Immediate.plain : Wasm1.Immediate opcode (.plain op) bytes → Immediate opcode (.plain op) bytes`. Every plain scalar token of Wasm2 is a `Wasm1.Immediate`.
- `Wasm2.At` and `Wasm2.Consumed` are built on `Wasm1.BytesAt` (defined at `Binary/Wasm1/Encoding.lean:27`; 206 uses tree-wide).
- `Binary/Wasm2/{Bulk,References,Simd,NumericExtensions,EncodingComplete,EncodingUnique}.lean` import `Binary/Wasm1/{Encoding,MemoryMeaning,NumericMeaning,EncodingComplete,PrefixUnique}`.
- `Binary/Module.lean` imports only `Binary.Wasm1.Encoding`. `ModuleBinary.BodyEncoding` (:342) is `Rep Wasm1.TokenEncoding`.
- `Binary.Wasm2.Encoding → Binary.Wasm2.Simd → Binary.PrefixUnique → Binary.Module`. So `Binary/Module.lean` cannot import the Wasm2 token grammar (cycle). That is why the Wasm2 code grammar is injected through the `codeRel` argument (`Profile.CodeEncoding`). Keep `codeRel`, or split the file.
- `Wasm2/Scalar/Complete.lean:2-3,21-45` dispatches every base instruction to `Wasm1.Completeness.{nop,unreachable,localGet,localSet,localTee,globalGet,globalSet,memory,memorySize,memoryGrow}` and `Frame.step_*`. `Wasm2/Complete/Frame.lean:52` embeds `Wasm1.Completeness.Frame`. These lemmas are about the shared `code.step` and have no profile.
- `Binary/Wasm1/Subset.lean` goes the other way (it imports `Binary.Wasm2.Encoding`) and is used only by `Binary/ProfileEncoding.lean`, `Wasm2/ProfileFilters.lean`, `Wasm2/ProfileFrames.lean`.

### Delete outright (after their users' Wasm1 arms are gone)

- `Wasm2/ProfileAgreement.lean` (655 lines). Users:
  - `Profile/BodyVisitor.lean:43-51` (`wasm1_of_body`).
  - Runtime Wasm1 arms: `Runtime/Compiler/Local/Demand/IndependentBodyDemand.lean:52`, `…/Local/Relations/Function/EntryTypedSteps.lean:24`, `…/Module/CompileTotal.lean:33`, `…/Module/EntryFinishAvailable.lean:194`.
- `Wasm2/ProfileFrames.lean` (231). Only `Wasm2/Invariant.lean` imports it.
- `Wasm2/ProfileFilters.lean` (133). Delete once the four Rust `check_*` functions go; until then only the `.wasm2`/`complete` lemmas remain. 28 handwritten files reference `code.check_*` (largest: `Wasm2/Trace/ControlBytes.lean` 18, `Runtime/Compiler/Body/Relations/Calls/IndirectCalls.lean` 8).
- `Binary/Wasm1/Subset.lean` (118). Outside users: `Wasm2/Invariant.lean:151-153,167`, `Wasm2/Control/BranchStep.lean:98`, `Wasm2/NumericExt/Sound.lean:56`. All are in Wasm1-only clauses.
- `Binary/ProfileEncoding.lean` (128). Replace `ProfileConsumed` by `Wasm2.Consumed` in `Wasm2/Complete/{Program,Control,Leaf}.lean` and `Wasm2/Completeness.lean`.
- `Wasm1/ProfileSyntax.lean` (100). `Wasm1/Complete/Frame.lean`, `Module/Code/BodyContext.lean` and `Wasm2/Prefix.lean` import it but use no `Wasm1.Instruction*` name; swap in `Itasca.Support.ControlTranslation`.
- `Profile/Instructions.lean` (31).
- `Examples/Wasm1/ProfileBoundary.lean` (212).
- `SpecExt/Wasm1.lean` (42) and most of the runtime precheck cluster (section 6).
- `Module/Code/Encoding.lean`: all but `slice_bytes`, which has 5 outside users.
- Inside shared files:
  - `ModuleBinary.ElementEncoding` (`Binary/Module.lean:251`), `DataEncoding` (:352), `BodyEncoding` (:342), `CodeEncoding`, `ModuleEncoding` (:493).
  - `ModuleBinary.CodeEncodingWithinLimits` (`Module/Limits.lean:~22`).
  - `ModuleBinary.code_prefix_unique` (`Binary/ModuleUniqueSections.lean:18`), `ModuleBinary.BodyEncoding.unique` (`Binary/Wasm1/PrefixUnique.lean:123`).
  - Wasm1 wrappers: `ModuleEnv.SemanticPost` (`Module/Env/Semantics.lean:55,71`), `Module/Env/Complete.lean:108`, `Module/Code/EntryOfEnv.lean:41`, `Module/Env/Preservation.lean:37`, `metadata.decode_segment_index.wasm1` (`Module/Readers/Basic.lean:237`).

### Named Wasm1 or Profile but needed at Wasm2 (keep; rename later if desired)

- `Binary/Wasm1/Encoding.lean`: `BytesAt`, `IndicesEncoding`, plain `Immediate` constructors, `At.of_*`.
  - Optional cleanup: its `block/loop/if_/else_/end_` constructors, `TokenEncoding`, `Consumed`, `BodyEncoding` are Wasm1-only.
  - `Wasm1.TokenEncoding` is still used by `ModuleBinary.BodyEncoding` and by `Examples/Module/Functions.lean:131`, `Examples/Wasm2/Module.lean:93-98`.
  - `Binary/Wasm1/BlockType.lean` (`ScalarBlockByte`) can only go together with those constructors.
- `Binary/Wasm1/{NumericMeaning,MemoryMeaning,MemoryTyping,BrTableLabels,DeclaredReferences,EncodingComplete,PrefixUnique}.lean`.
- `Binary/Wasm1/EncodingUnique.lean`: actually `Leb128.Decoded.unique` and `BrTable.*.unique`, imported by 6 runtime compiler files.
- `Wasm1/Complete/{Frame,Env,Scalar}.lean`.
- `Profile/{Types,BodySpec,Body,BodyVisitor,CodeEntry,EntrySound,EntryComplete,EntryPipeline,EntryTrace,BinaryUnique}.lean`: real Wasm2 content with a now-pointless parameter.
- `Module/Elab/Profile.lean`: export uniqueness, memory count, declared references.
- Runtime "Profile" files are about the Rust function `step_profile` at `.Wasm2`:
  - `Runtime/Compiler/Body/Reader/Replay/{ProfileAgreement,ProfileSafety,CallbackProfile}.lean`.
  - `…/Acceptance/ProfileAcceptance.lean`, `…/Safety/ProfileOrdinarySafety.lean`.
  - `Runtime/Compiler/Module/{CompileProfileTotal,SchedulerProfileSafety}.lean`.
- `Examples/Wasm1/Support.lean`: generic body-run helpers, used by `Examples/Module/CodeEntryRejection.lean`.

### Examples

All of `Examples/Module/*` (10 files, 80 `.Wasm1` mentions) and `Examples/Stream.lean:43,166` are Wasm1 runs and must be ported. `Sections.lean` uses the Wasm1 element and data encodings. `Examples/Wasm2/Module.lean:140,170` compares both profiles.

## 4. Headline theorems and defaults (V)

- `Results/Validate.lean`:
  - Generic: `metadata.validate_module.profile_spec` (24), `profile_total` (32), `profile_sound` (38), `profile_complete` (47), `profile_complete_with_metadata` (60).
  - Wasm1: `wasm_spec` (72), `wasm_total` (80), `wasm_sound` (86), `wasm_complete` (94), `wasm_complete_with_metadata` (104).
- `Results/Stream.lean`:
  - Generic: `stream.validate_streaming.profile_sound` (29), `profile_total` (48), `profile_complete` (60).
  - Wasm1: `wasm_sound` (78), `wasm_total` (95), `wasm_complete` (103).
- `Results/Compile.lean`: `runtime.compiler.compile_with.profile_sound` (29), `profile_spec` (38), `compile_default_with.profile_spec` (50), `compile_with.profile_complete` (69), `profile_complete_spec` (80).
- `Results/Unique.lean`: `Profile.module_unique` (16), `ModuleBinary.ModuleEncoding.unique` (23, Wasm1 grammar).
- `Results/Batch.lean` (7 theorems, `{profile}` implicit, `hprofile : batch.profile = profile`; :113 has `hresults : ∀ ft, Profile.FuncType profile ft`, trivial at Wasm2).
- `Results/Trace.lean` (7 theorems with `(profile)`; :107 has the same trivial premise).
- `Results/Instantiate.lean:34-37` takes `profile`. `Results/Invoke.lean` has no profile.
- `Main.lean:20-41,47-59` lists these.
- 53 theorems named `*.profile_*` exist tree-wide. Outside `Results`, the remaining `wasm1` names are `Pending.wasm1_at`, `Closed.wasm1`, `code.validate_body_with.wasm1_of_body`, `metadata.decode_segment_index.wasm1`, and the `ProfileAgreement.lean` family.

`:= .Wasm1` (65 lines, 32 files):
- `Binary/Module.lean:475`, `Binary/ModuleUnique.lean:33`, `Contracts.lean:180,198,226,238,249`.
- `Stream/{SubmissionSound:33,176,186; SubmissionComplete:46,58,66; DriverRegions:86; DriverRun:26,64; Scheduler:24}`.
- `Module/Limits.lean:76`, `Module/Soundness.lean:25`, `Module/Layout.lean:27,35`.
- `Module/Code/{Context:59; Section:57,71,125; Locals:109,193}`.
- `Module/Readers/Types.lean:111,254,287`.
- `Module/Sections/{Tail:54,132,227; Import:24,67; Imports:61,102; Table:45,114; Global:73,163; TailComplete:36}`.
- `Module/Env/{Replay:38,45,63,78; Slots:21,69; Encoding:53,69; Requirements:21,41,151,172; Basic:54; Declarations:76}`.
- `Module/Elab/{Profile:28,34; Elaboration:88}`.
- `Runtime/Compiler/Module/StreamingAvailable.lean:28,40,48`.
- `Examples/Module/{Negative:132,378; SliceLayout:89}` (named-argument uses).

## 5. Case splits on profile (V)

99 lines in 52 files: 61 `cases profile with`, 14 `cases profile <;>`, 6 bare `cases profile`, 12 `match profile …` (all in definitions), plus a few `rcases`/`by_cases`. 73 `| Wasm1 =>` arms sit in 42 files.

| Directory | Lines | Files |
|---|---|---|
| Profile/ | 15 | 7 |
| Binary/ | 15 | 4 |
| Runtime/Compiler | 12 | 9 |
| Wasm2/ (top level) | 12 | 4 |
| Module/Sections | 11 | 6 |
| Module/Readers | 9 | 5 |
| Module/Const | 9 | 3 |
| Wasm2/Control | 3 | 3 |
| Wasm2/Complete | 3 | 3 |
| Module/Env | 3 | 3 |
| Examples/Wasm2 | 3 | 1 |
| Runtime/Store | 2 | 2 |
| Module/Code | 1 | 1 |
| Module/ (top) | 1 | 1 |

Representative shapes:

1. Definition by `match`, `lean/Itasca/Profile/Types.lean:17-20`:
```lean
def FuncType (profile : ValidationProfile) (ft : wasm_types.FuncType) : Prop :=
  match profile with
  | .Wasm1 => ft.results.val.length ≤ 1
  | .Wasm2 => True
```
2. `cases profile <;>` with simp, `lean/Itasca/Module/Readers/BasicComplete.lean:74-76`:
```lean
  cases profile <;> cases ty <;>
    simp_all [metadata.decode_value_type, valueByte, ValueTypeAllowed,
      core.result.Result.Insts.CoreOpsTry.branch]
```
3. `cases profile with` where the Wasm2 arm is trivial, `lean/Itasca/Wasm2/Control/Call.lean:240-245`:
```lean
  have hbyte : code.check_table_byte profile data middle = .ok (.Ok ()) := by
    cases profile with
    | Wasm2 => rfl
    | Wasm1 =>
      obtain ⟨hlt, hz⟩ := hzero rfl
      exact code.check_table_byte.complete _ data middle hlt hz
```
4. Both arms real (two grammars), `lean/Itasca/Module/Sections/ElementHeader.lean:116-122`:
```lean
  cases profile with
  | Wasm1 =>
    obtain ⟨index, offset, initializers, ib, ob, entries, rfl, hi, ho, hv, rfl⟩ := h
    exact ⟨false, ib ++ ob, entries, .legacy hi ho, indices_vector_intro hv, rfl⟩
  | Wasm2 =>
    cases h with
```
5. Runtime split on a field, `lean/Itasca/Runtime/Store/Instantiation/PrepareInstanceClassified.lean:602-604,645-646` (`ResourceDecomposition.lean:637,680` is the same):
```lean
cases profile : dataInst.module.profile with
| Wasm2 =>
  simp only [runtime.store.wasm1, profile, bind_ok, Bool.false_eq_true, ↓reduceIte] at run
...
| Wasm1 =>
  simp only [runtime.store.wasm1, profile, bind_ok, ↓reduceIte] at run
```
6. Runtime transport through agreement, `lean/Itasca/Runtime/Compiler/Module/CompileTotal.lean:31-33`:
```lean
    cases profile with
    | Wasm1 =>
      obtain ⟨result',returned⟩ := code.validate_body_with.wasm1_returns _ _ _ _ _ _ _ run
```

The dominant shape is the guarded hypothesis `profile = .Wasm1 → …` (74 lines in 30 files), not a tactic case split.

## 6. Runtime specifics (V)

**How the profile reaches the runtime.** `compile_with` stores it in `ExecutableModule.profile` (`src/runtime/compiler/mod.rs:335`). `CompilationCertificate` records `executable.profile = profile` (`Runtime/Integration/Compilation/Certificate.lean:31`). `instantiate` reads it once (`instantiate.rs:183`). In Lean, `inst.module.profile` is otherwise only an index:
- `ModuleEnv.Valid module.module.env module.profile` (about 45 lines in `Runtime/Store/{Instantiation,Preparation,Invariant,Initialization}` and `Runtime/Integration/Instantiation`).
- `Compiler.FunctionCapacity inst.module.profile …` (`Runtime/Representation/StoreCapacity.lean:19`).
- Preservation lemmas `after.profile = module.profile` (`Runtime/Compiler/Local/Relations/Segments/SegmentComplete.lean:28-90`, `…/Local/Initializer/InitializerComplete.lean:207-268`).

**What `runtime.store.wasm1` changes.** Under Wasm1, after staging all instance items and before publication, `prepare_instance` evaluates every active element offset, then every active data offset, and range-checks them (`Trap::TableOutOfBounds`, `Trap::MemoryOutOfBounds`). Failure rejects before any segment write and the store rolls back. Under Wasm2 there is no precheck, so segment writes are sequential and partial effects persist (`tests/runtime_api.rs:97-130` asserts both).

In `Generated/Funs.lean` the prechecks are `prepare_instance_loop10` and `loop11`, the last two loops. Removing them does not renumber loops 0-9, and only the `Precheck*` files reference loops 10 and 11.

Lean files involved:
- Mention `runtime.store.wasm1`: `Runtime/Store/Instantiation/PrepareInstanceClassified.lean`, `ResourceDecomposition.lean`.
- Mention `check_element_bounds`/`check_data_bounds`: `Runtime/Store/Initialization/{PrecheckLoop,PrecheckErrors,PrecheckWitness,PrecheckResources}.lean`.
- Cluster built on them: `PrecheckCertifiedWitness.lean`, `PrecheckCertifiedResourceCauses.lean`, `PrecheckSource.lean`, `Runtime/Store/Instantiation/PrecommitSource.lean`, and `PrecommitOrigins.lean` (fields `bounds`, `staging`).
- Two traps:
  - `storeParts` is defined in `PrecheckLoop.lean:94` and used in about 30 other store files. Move it first.
  - `ElementPrecheckReady`/`DataPrecheckReady` (`PrecheckLoop.lean:68,79`) are used by `InitializerCertificates.lean:78-113`, which then feeds only the precheck cluster.

**`SpecExt/Wasm1.lean`.** Defines `SegmentBoundsFailure` (constructors `element`, `data`: evaluated offset plus length exceeds the staged table or memory) and `BoundsRollback` (single constructor `reject`, resulting store equals `before`), plus `BoundsRollback.unchanged`. Its only importer is `Runtime/Store/Initialization/PrecheckSource.lean`; names are used there, in `PrecommitSource.lean`, and in `InstantiateSource.lean:46`. It is a handwritten specification extension, so removing it is a trust-boundary change to report.

**`InstantiationSourceOutcome`** (`Runtime/Integration/Instantiation/InstantiateSource.lean:36-58`) is a disjunction:
- Rejected before publication: `PrecommitError module.profile error ∧ after = before ∧ host = platform ∧ ∀ trap, error = .Trap trap → module.profile = .Wasm1 ∧ ∃ staged inst, … SpecExt.Wasm1.BoundsRollback …`.
- Published: follows `fun_instantiate` and `InitializedSource`.

At Wasm2 `PrecommitError` admits no trap, so the trap clause is vacuous. The proof derives `module.profile = .Wasm1` at lines 273-276. `PrecommitError` appears in 15 files, including `Runtime/Store/Linking/LinkErrors.lean` (5) and `PrecommitOrigins.linked`, which already takes `PrecommitError .Wasm2`.

## 7. Assessment of the removal order

### Problems with the proposed two stages

1. **Stage 1 is atomic for Lean.** "Most statements still typecheck" holds only for threading statements. Once `Generated/Types.lean` lacks `Wasm1`:
   - 350 standalone `.Wasm1` lines in 94 files fail (82 non-example files, listed in my notes by count; the heaviest are `Wasm2/ProfileAgreement.lean` 53, `Wasm2/Invariant.lean` 12, `Results/Validate.lean` 10, `Binary/Module.lean` 8, `Wasm2/Complete/LeafContracts.lean` 8, `Wasm2/Simd/Sound.lean` 8).
   - Transitive dependents of the failing base files, out of 2,422 Lean files: `Binary/Module.lean` 1,237; `Profile/Types.lean` 962; `Wasm1/ProfileSyntax.lean` 869; `Wasm2/BodySpec.lean` 822; `Wasm2/Invariant.lean` 761; `Contracts.lean` 739.
   - Nothing above them can be checked until they are fixed bottom-up.
2. **Defaults.** 65 `:= .Wasm1` lines and 5 `optParam … .Wasm1` signatures must all be edited. These can be front-loaded in a green Lean-only step.
3. **Arity fallout beyond files that name `.Wasm1`** (I). Removing guarded fields changes constructor and tuple arity, and positional patterns elsewhere break. Affected: `State.running/closed`, `Pending`, `Wasm2.Validated`, `AcceptedBody`, `AcceptedTrace`, `ModuleEnv.Valid`, `ModuleConditions`, `EntryTyped`, `CodeEntry.Typed`, `HeaderEncoding`. Example: `Wasm2/Invariant.lean:66,134` name every constructor argument.
4. **`ReaderOpcode .Wasm1`** in the runtime compiler is a real "base opcode" predicate and needs restating.
5. **Module grammar layering.** The Wasm1 grammar is the default `ModuleEncoding`, and `Binary/Module.lean` cannot import Wasm2 tokens (cycle). Keep `ModuleEncodingWith`'s `codeRel`.
6. **`Binary/Wasm1` and `Wasm1/Complete` must not be deleted** despite the names.
7. **Runtime precheck.** Deleting the `if wasm1` block reshapes `prepare_instance`. Two very deep proofs split on it (`PrepareInstanceClassified.lean` about 592-710, `ResourceDecomposition.lean` about 627-750), and `storeParts` must move first.
8. **Examples** are almost all Wasm1 runs and need porting, not deleting.
9. **Rust side** (I). If arms are deleted by removing the `match` entirely, `profile` becomes an unused parameter (warning) unless renamed. Keeping a one-arm `match profile { ValidationProfile::Wasm2 => … }` avoids that. There is precedent for a single-variant enum type in extraction (`error.VisitError`, `Generated/Types.lean`), but none for a `match` on one.
10. **Dead `Error` variants.** Removing `Error::MultipleTables` and `Error::TooManyResults` changes the extracted `error.Error` and can break `cases` proofs. Do it in Stage 2.
11. **Rebuild cost** (I). Every Rust edit changes `Generated/*.lean` (line-number comments), and everything imports it, so each extraction point probably costs a full rebuild. Keep extraction points few.
12. **Stage 2 scale.** 85 extracted definitions take `profile`; 2,651 references to them in 340 handwritten files (`code.step_profile` alone 476), 200 of those files in `Runtime/Compiler`. Struct fields `stream.CodeBatch.profile`, `ExecutableModule.profile`, `StreamBatch.Issued.profile` change anonymous-constructor arity (for example `Examples/Stream.lean:43`, `Runtime/Compiler/Module/CompileProfileTotal.lean:76`). Do not rename `step_profile` in the same series; `code.step`, `step_wasm2`, `step_extended` already exist.

### Why not Lean-first with the enum still two-variant

Weakening bottom-up is impossible while Rust still rejects at Wasm1 (completeness would be false). Specializing top-down to `.Wasm2` means rewriting roughly 390 binders that Stage 2 then rewrites again.

### Recommended order

- **Step 0, green, no extraction** (Lean, tests, docs only):
  - Delete the 8 `wasm_*` theorems, `ModuleEncoding.unique`, and the `Main.lean` entries.
  - Delete `Examples/Wasm1/ProfileBoundary.lean`; port `Examples/Module/*` and `Examples/Stream.lean` to `.Wasm2`; move `Examples/Wasm1/Support.lean`.
  - Delete the Wasm1 wrapper lemmas listed in section 3.
  - Make all 65 defaults and 5 `optParam`s explicit.
  - Move `storeParts` out of `PrecheckLoop.lean`.
  - Remove or trim the Wasm1 Rust tests, fuzz targets and `wast_extract` (not extraction inputs).
- **Step 1, extraction 1: runtime precheck slice, enum still two-variant.**
  - Rust: delete `fn wasm1`, the `if wasm1` block, `check_element_bounds`, `check_data_bounds`.
  - Lean: collapse the two `cases profile : dataInst.module.profile` splits to their Wasm2 arm.
  - Delete the `Precheck*` cluster, `PrecommitSource.lean`, `SpecExt/Wasm1.lean`.
  - Drop `PrecommitOrigins.bounds/staging`, the trap line and the profile parameter of `PrecommitError`, and the trap clause of `InstantiationSourceOutcome`.
  - This touches no validator file.
- **Step 2, extraction 2: single-variant enum, delete validator Wasm1 arms.**
  - Keep the one-arm `match` and keep the trivial `check_*` and `check_table_count` functions so generated bodies keep their shape.
  - Fix Lean bottom-up in import order: `Binary/Module.lean` and `Binary/ModuleUnique*.lean`; `Profile/Types.lean`; `Module/Readers`, `Const`, `Sections`, `Env`; `Wasm2/BodySpec.lean`, `Invariant.lean`, `Control`, `Complete`, `Trace`; `Profile/*`; `Module/Elab`, `Soundness`; `Contracts.lean`, `Stream/*`; the 8 runtime compiler files with Wasm1 arms plus `OpcodeClassification.lean`; `Results`.
  - Delete the files listed in section 3.
- **Step 3, extraction 3 (or one per Rust module, callee-first: `code.rs`, `module.rs`, `stream.rs`, runtime).**
  - Remove the `profile` parameter, both struct fields, both accessors, the enum, the trivial `check_*` functions, the dead limits and `Error` variants.
  - Sweep Lean; merge `Profile.Body` into `Wasm2.Validated`; rename or flatten `Profile.*`; drop `executable.profile = profile`.
  - Renaming the `Wasm1` namespaces (233 files) is optional and belongs in a separate series.

Decision for you: Step 2 can be cut into smaller green slices (table and result counts; value types and constants; segments and data count; body filters) while keeping two variants, at the price of one extraction and probable full rebuild per slice. The body-filter slice is the exception: it needs the single-variant enum, or simultaneous parameter removal in `code.rs`, because the runtime compiler's `.Wasm2`-stated lemmas otherwise have no way to cover `.Wasm1`.

Not verified: how Aeneas prints a `match` on a single-variant enum; that unit-like eta makes `rw`/`simp` (as opposed to `exact`) see `profile` as `.Wasm2`; full-rebuild cost per extraction; exact count of positional patterns broken by field removal.

Policy notes from `AGENTS.md`: validator proofs must not import `Itasca.Runtime` or `SpecExt` (Step 1 respects this), and dropping the Wasm 1.0 guarantees plus `SpecExt/Wasm1.lean` is a trust-boundary and README-claim change that must be reported explicitly.
