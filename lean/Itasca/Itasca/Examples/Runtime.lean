import Itasca
import Itasca.Examples.Module.SliceLayout

/-!
Proofs for Examples.

This module collects Runtime, Stream.
Each section documents its contracts and consumers.
-/

/-! ## Runtime -/

section

/-!
# Closed runtime examples

The concrete vector memory, mathematical float dictionary, trapping callbacks,
and granting allocator discharge the runtime's platform obligations. These
examples establish a fresh store and compile the eight-byte empty module from
independent source validity and numerical eligibility. The closed host invocation demonstrates the public behavior guarantee.
-/

namespace Itasca.Examples.Runtime
open Aeneas Aeneas.Std WebAssembly Integration

def exampleMemory := Platform.vecMemory grantAll
def exampleView := Platform.vecMemoryView
def exampleCode : Representation.CodeInterpretation := fun _ _ _ => .HOST 0
def exampleLimits : runtime.store.StoreLimits :=
  ⟨1024#usize, 1024#usize, 1024#usize, 1024#usize, 1024#usize, 1024#usize, 1024#usize, 1024#usize⟩
def freshStore : runtime.store.Store runtime.platform.VecMemory := {
  id := 1#usize, limits := exampleLimits,
  funcs := alloc.vec.Vec.new _, types := alloc.vec.Vec.new _, tables := alloc.vec.Vec.new _,
  memories := alloc.vec.Vec.new _, globals := alloc.vec.Vec.new _, instances := alloc.vec.Vec.new _,
  elems := alloc.vec.Vec.new _, datas := alloc.vec.Vec.new _, externs := alloc.vec.Vec.new _,
  instance_items := 0#usize, signature_values := 0#usize, memory_bytes := 0#usize, table_elements := 0#usize }

/-- The additional embedding premises for resource completeness are jointly
satisfied by continuing interrupts, a granting allocator and trapping hosts. -/
theorem example_resources
    (Inv : Representation.CodeInterpretation → runtime.store.Store runtime.platform.VecMemory → Prop) :
    ResourceAvailability (trapHost exampleMemory) grantAll Inv := by
  refine ⟨?_, (fun _ _ _ => rfl), ?_, ?_⟩
  · intro code store invariant host p args defaults result nextPlatform after returned called
    simp only [trapHost, Result.ok.injEq, Prod.mk.injEq] at called
    obtain ⟨_, _, rfl, _⟩ := called
    rfl
  · intro before after
    simp only [trapHost, ne_eq, Result.ok.injEq, Prod.mk.injEq,
      core.result.Result.Err.injEq, reduceCtorEq, false_and, not_false_eq_true]
  · intro code store invariant p identity args defaults nextPlatform after returned
    simp only [trapHost, ne_eq, Result.ok.injEq, Prod.mk.injEq,
      core.result.Result.Err.injEq, reduceCtorEq, false_and, not_false_eq_true]

theorem fresh_store_valid
    (Inv : Representation.CodeInterpretation → runtime.store.Store runtime.platform.VecMemory → Prop)
    (contract : RuntimeContract exampleView Inv) : Inv exampleCode freshStore := by
  have created := Store.with_identity.spec exampleView Inv contract.toStoreMutationContract exampleMemory exampleCode
    1#usize exampleLimits (by scalar_tac)
  change Result.ok freshStore ⦃ store => Inv exampleCode store ∧
    store.id = 1#usize ∧ store.limits = exampleLimits ∧ Representation.decodeStore exampleView exampleCode store = ⟨[], [], [], [], [], []⟩ ⦄ at created
  simp only [WP.spec_ok] at created
  exact created.1

private theorem host_invocation {s : store} {address host : Nat}
    (wellFormed : wf_store s) (function : HostFunction s address host [] []) :
    fun_invoke s address [] ⟨⟨s, Spec.invocationFrame⟩, [.CALL_ADDR address]⟩ := by
  obtain ⟨module, found⟩ := function
  have frameWf : wf_frame Spec.invocationFrame := by
    constructor
    · intro value member; cases member
    · constructor; intro exported member; cases member
  have typed : ResultsTyped s [] [] := by
    exact List.Forall₂.nil
  have configWf := Spec.host_call_wf (fa := address) wellFormed frameWf typed
  apply fun_invoke.fun_invoke_case_0 s address 0 [] Spec.invocationFrame [] [] rfl
  · exact (List.getElem?_eq_some_iff.mp found).1
  · simpa only [fun_funcinst, List.getElem!_eq_getElem?_getD, found, Option.getD_some]
  · exact configWf
  · exact frameWf
  · exact .state_case_0 _ _ wellFormed frameWf
  · rfl

def exampleHostType : Itasca.wasm_types.FuncType := ⟨alloc.vec.Vec.new _, alloc.vec.Vec.new _⟩
def exampleExecution : runtime.interp.Execution :=
  ⟨0#usize, alloc.vec.Vec.new _, alloc.vec.Vec.new _, alloc.vec.Vec.new _, alloc.vec.Vec.new _⟩

/-- This closed call creates a fresh store, successfully defines a [] → []
host, and applies invocation soundness with every platform obligation proved. -/
theorem host_only_invoke : ∃ Inv, RuntimeContract exampleView Inv ∧ ∃ address after,
    runtime.store.Store.define_host_with exampleMemory grantAll freshStore exampleHostType 0#u64 =
      .ok (.Ok address, after) ∧
    InvocationBehavior exampleMemory (trapHost exampleMemory) Platform.floatWitness grantAll
      exampleView Inv exampleCode exampleExecution after () address (Slice.new runtime.Value)
      (alloc.vec.Vec.new runtime.Value)
      ⟨⟨Representation.decodeStore exampleView exampleCode after, Spec.invocationFrame⟩, [.CALL_ADDR address.index.val]⟩
      (runtime.interp.invoke_with exampleMemory (trapHost exampleMemory) Platform.floatWitness grantAll
        exampleExecution after () address (Slice.new runtime.Value) (alloc.vec.Vec.new runtime.Value)) := by
  obtain ⟨Inv, contract⟩ := Integration.runtime_verified exampleView
  refine ⟨Inv, contract, ?_⟩
  have available := define_host_available exampleMemory grantAll grant_all_correct (grant_all_available _)
    freshStore exampleHostType 0#u64
    (by simp only [freshStore, Store.objectCount, alloc.vec.Vec.new, alloc.vec.Vec.from_val,
          alloc.vec.Vec.length, List.length_nil, Nat.zero_add, exampleLimits]; scalar_tac)
    (by simp only [exampleHostType, alloc.vec.Vec.new, alloc.vec.Vec.from_val,
          alloc.vec.Vec.length, List.length_nil, Nat.zero_add]; omega)
    (by simp only [freshStore, exampleHostType, alloc.vec.Vec.new, alloc.vec.Vec.from_val,
          alloc.vec.Vec.length, List.length_nil, Nat.add_zero, exampleLimits]; scalar_tac)
  obtain ⟨⟨result, after⟩, run, address, same⟩ := WP.spec_imp_exists available
  subst result
  have defined := Store.define_host_with.spec exampleView Inv contract.toStoreMutationContract
    exampleMemory grantAll grant_all_correct exampleCode freshStore (fresh_store_valid Inv contract) exampleHostType 0#u64
  rw [run] at defined
  simp only [WP.spec_ok, uncurry_apply_pair] at defined
  obtain ⟨valid, retained, _externs, _limits, _sourcePrefix, extension, owner, index, issued, owned, host⟩ := defined
  have sourceHost : HostFunction (Representation.decodeStore exampleView exampleCode after) address.index.val 0 [] [] := by
    simpa only [exampleHostType, alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.map_nil,
      UScalar.ofNatCore_val_eq] using host
  refine ⟨address, after, run, ?_⟩
  apply Interp.invoke_with.behaves exampleMemory (trapHost exampleMemory) Platform.floatWitness
    grantAll exampleView Inv contract.toInvocationContract ?_ exampleCode
    (trap_host_laws _ _ Inv contract.well_formed contract.source_typed) exampleExecution after () valid
    address (Slice.new runtime.Value) (alloc.vec.Vec.new runtime.Value) issued ?_
    _ (host_invocation (contract.well_formed _ _ valid) sourceHost)
  · exact ⟨Platform.float_witness_correct, grant_all_correct,
      fun _ => by rw [trapHost, WP.spec_ok]; trivial, Platform.vec_memory_laws grantAll grant_all_correct⟩
  · intro value member
    cases member

namespace EmptyModule
open Compiler Itasca Binary Module.Elaboration

def raw : Binary.Module := ⟨[], [], [], [], [], [], [], none, [], none, [], []⟩
def bytes : Slice U8 := Slice.from magicVersion (by simp only [magicVersion, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]; scalar_tac)
def env : metadata.Env where
  types := alloc.vec.Vec.new _
  imports := alloc.vec.Vec.new _
  globals := alloc.vec.Vec.new _
  exports := alloc.vec.Vec.new _
  elements := alloc.vec.Vec.new _
  start := none
  data_count := none
  declared_funcs := alloc.vec.Vec.new _
  func_type_indices := alloc.vec.Vec.new _
  func_types := alloc.vec.Vec.new _
  table_types := alloc.vec.Vec.new _
  mem_types := alloc.vec.Vec.new _
  global_types := alloc.vec.Vec.new _
  num_imported_funcs := 0#usize
  num_imported_globals := 0#usize

private theorem cache : Module.Environment.Cache env [] [] := by
  constructor <;> simp only [env, alloc.vec.Vec.from_val, Module.Environment.importedFuncs, Module.Environment.importedGlobals,
    Module.Environment.importedTables, Module.Environment.importedMems, List.filterMap_nil, List.append_nil,
    List.forall₂_nil_right_iff, UScalar.ofNatCore_val_eq, List.length_nil, List.map_nil]

private theorem environment_valid : Module.Environment.Valid env := by
  constructor <;> simp only [env, Itasca.CodeEntry.FuncTypeWithinLimits, Module.References.Coherent,
    Module.References.collected, alloc.vec.Vec.from_val, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, Nat.reducePow, Nat.add_one_sub_one, List.length_nil, zero_le, List.map_nil,
    List.nodup_nil, reduceCtorEq, not_lt_zero, IsEmpty.exists_iff, List.flatMap_nil,
    List.append_nil]

private theorem omitted {α : Type} (id : U8) (R : α → List U8 → Prop) (absent : α) :
    PaddedEncoding id R absent absent [] := ⟨[], [], .nil, .absent, rfl⟩

private theorem encoded : ModuleEncodingWithinLimits raw bytes.val := by
  constructor
  · exact Compiler.module_header_fits
  · refine ⟨[], [], [], [], [], [], [], [], [], [], [], [], [],
      omitted _ _ _, omitted _ _ _, omitted _ _ _, omitted _ _ _, omitted _ _ _,
      omitted _ _ _, omitted _ _ _, omitted _ _ _, omitted _ _ _, omitted _ _ _,
      omitted _ _ _, omitted _ _ _, .nil, ?_, ?_⟩
    · simp only [bytes, Slice.from_val, List.append_nil]
    · simp only [DataCountValid, raw, List.not_mem_nil, IsEmpty.forall_iff, implies_true]

theorem valid : Compiler.ValidCompilationSource bytes raw := by
  have codes : List.Forall₂ (fun idx code => CodeEntry.Typed env idx code) env.func_type_indices.val [] := .nil
  refine ⟨encoded, ?_, ?_, ?_, ?_⟩
  · simp only [ModuleSignaturesWithinLimits, raw, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  · exact Module.Elaboration.elaborates (segments := []) cache codes
  · exact Module.Elaboration.typed (segments := []) cache environment_valid (by simp only [env, alloc.vec.Vec.from_val, List.not_mem_nil, IsEmpty.forall_iff, implies_true]) (by simp only [env, alloc.vec.Vec.from_val, List.not_mem_nil, IsEmpty.forall_iff, implies_true])
      codes (by simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]) (by simp only [env, reduceCtorEq, List.length_nil, IsEmpty.forall_iff, implies_true]) (List.Forall₂.nil : List.Forall₂ (Module.Externals.ExportResolves env) [] [])
  · exact Module.Elaboration.restrictions (segments := []) cache environment_valid codes

/-- Eight input bytes and one initializer instruction suffice for the empty module. -/
def compileLimits : runtime.compiler.CompileLimits :=
  ⟨8#usize, 0#usize, 0#usize, 1#usize, 0#usize, 0#usize, 0#usize⟩

theorem eligible : Compiler.CompileEligible bytes raw compileLimits := by
  constructor <;> norm_num [Compiler.compilationBudget, bytes, raw, magicVersion,
    Slice.from_val, compileLimits]
  all_goals scalar_tac

/-- Compiler completeness has satisfiable premises on the header-only module. -/
theorem compiled : ∃ executable,
    runtime.compiler.compile_with grantAll bytes compileLimits = .ok (.Ok executable) ∧
      CompilationSource bytes executable :=
  Compiler.compile_with.complete grantAll grant_all_correct bytes raw compileLimits valid eligible
    (grant_all_available _)

/-- The compiled empty module can be passed to instantiation with every API
premise discharged, preserving the executable invariant and source outcome. -/
theorem compiled_instantiates : ∃ Inv, RuntimeContract exampleView Inv ∧ ∃ executable,
    runtime.compiler.compile_with grantAll bytes compileLimits = .ok (.Ok executable) ∧
    runtime.store.instantiate.Store.instantiate_with exampleMemory (trapHost exampleMemory)
      Platform.floatWitness grantAll freshStore executable (Slice.new runtime.Extern) ()
      ⦃ (result, after, platform) =>
        Inv
          (Store.installCode exampleCode freshStore.instances.length (Compiler.sourceFunctions raw)) after ∧
        InstantiationSourceOutcome exampleView exampleCode
          (Store.installCode exampleCode freshStore.instances.length (Compiler.sourceFunctions raw))
          freshStore executable (Slice.new runtime.Extern) raw () result after platform ⦄ := by
  obtain ⟨Inv, laws⟩ := Integration.runtime_verified exampleView
  refine ⟨Inv, laws, ?_⟩
  obtain ⟨executable, accepted, _⟩ := compiled
  have contract := Store.Instantantiation.instantiate_with.spec exampleMemory
    (trapHost exampleMemory) Platform.floatWitness grantAll exampleView Inv laws.toInstantiationContract
    (Platform.vec_memory_laws grantAll grant_all_correct) grant_all_correct freshStore executable
    (Slice.new runtime.Extern) () exampleCode (fresh_store_valid Inv laws)
    (by intro external member; cases member) bytes compileLimits accepted raw encoded.encoding
  refine ⟨executable, accepted, WP.spec_mono contract.2 ?_⟩
  rintro ⟨result, after, platform⟩ ⟨invariant, _retained, _extension, outcome⟩
  exact ⟨invariant, outcome⟩

end EmptyModule

end Itasca.Examples.Runtime

end

/-! ## Stream -/

section

/-!
# Adversarial streaming cases

Kernel-checked examples for the streaming API (`stream.CodeBatch`, `stream.Source`,
`stream.retire_code_batch`, `stream.validate_module_slice`). They show why the guarantees
need the issued-batch provenance (`Stream.Batch.Reachable`) and source coherence
(`Stream.Source.Coherent`) premises: a forged finished batch, an incoherent source, and replayed or
foreign batch completions. They also show that splitting a truncated buffer stays in bounds.
-/

open Aeneas Aeneas.Std

namespace Itasca.Examples.Stream

open Itasca.Examples.Module.Support (bytes)

/-- A module environment with no types, imports, functions, tables, memories or globals. -/
def emptyEnv : metadata.Env where
  types := alloc.vec.Vec.new _
  imports := alloc.vec.Vec.new _
  globals := alloc.vec.Vec.new _
  exports := alloc.vec.Vec.new _
  elements := alloc.vec.Vec.new _
  start := none
  data_count := none
  declared_funcs := alloc.vec.Vec.new _
  func_type_indices := alloc.vec.Vec.new _
  func_types := alloc.vec.Vec.new _
  table_types := alloc.vec.Vec.new _
  mem_types := alloc.vec.Vec.new _
  global_types := alloc.vec.Vec.new _
  num_imported_funcs := 0#usize
  num_imported_globals := 0#usize

/-- The empty byte slice. -/
def emptyBytes : Slice U8 := bytes []

/-- An issued-batch descriptor over the empty environment, which has no function to validate. -/
def impossibleIssued : Stream.Batch.Issued :=
  ⟨0#u64, 0#usize, emptyEnv, emptyBytes, 0#usize, 0#usize, 1#usize⟩

/-- An arbitrary extracted record can forge the private validation cursor. -/
def forgedBatch : stream.CodeBatch :=
  { impossibleIssued.seed with num_validated := 1#usize }

/-- `stream.CodeBatch.finish` accepts the forged record, so the finish check alone does not
establish provenance in the extracted model. -/
theorem forged_finish : stream.CodeBatch.finish forgedBatch = .ok (.Ok ()) := by
  rw [stream.CodeBatch.finish.accepted_iff]
  simp [forgedBatch, impossibleIssued, Stream.Batch.Issued.seed, emptyBytes, bytes,
    alloc.vec.Vec.deref]
  rfl

/-- No sequence of actual batch operations can manufacture this successful
finish: the empty environment rejects every function-entry validation. -/
theorem forged_unreachable : ¬ Stream.Batch.Reachable impossibleIssued forgedBatch := by
  intro h
  have hzero : ∀ {count pos}, Stream.Batch.Prefix impossibleIssued count pos → count = 0 := by
    intro count pos hp
    induction hp with
    | nil => rfl
    | snoc visitor previous index run ih =>
      simp [impossibleIssued, emptyEnv, metadata.validate_code_entry_with] at run
  have hz := hzero h.validation.2.1
  change 1 = 0 at hz
  omega

/-- A source whose environment is empty and whose code region has length 3. Reads of `[0, 2)` and
`[1, 3)` each return two bytes, but the overlapping views disagree at offset 1. -/
def incoherentSource : stream.Source Unit where
  environment := fun _ => .ok (.Ok emptyBytes)
  code_len := fun _ => .ok 3#usize
  code := fun _ first _ => .ok (.Ok (if first = 0#usize then bytes [0#u8, 0#u8]
    else bytes [1#u8, 0#u8]))
  tail := fun _ => .ok (.Ok emptyBytes)

/-- Reading code bytes `[0, 2)` from `incoherentSource` returns `[0x00, 0x00]`. -/
theorem incoherent_first_read : stream.read_exact incoherentSource () 0#usize 2#usize =
    .ok (.Ok (bytes [0#u8, 0#u8])) := by
  apply stream.read_exact.complete
  · decide
  · simp [incoherentSource]
  · rfl

/-- Reading code bytes `[1, 3)` from `incoherentSource` returns `[0x01, 0x00]`. -/
theorem incoherent_second_read : stream.read_exact incoherentSource () 1#usize 3#usize =
    .ok (.Ok (bytes [1#u8, 0#u8])) := by
  apply stream.read_exact.complete
  · decide
  · simp [incoherentSource]
  · rfl

/-- No code region makes `incoherentSource` coherent: correct read lengths do not substitute for
one fixed logical code region. -/
theorem incoherent_no_region (environment code tail : List U8) :
    ¬ Stream.Source.Coherent incoherentSource () environment code tail := by
  intro h
  have hlen := h.code_len_eq 3#usize rfl
  have hfirst := h.code_eq 0#usize 2#usize (bytes [0#u8, 0#u8]) (by decide)
    (by change 2 ≤ code.length; change 3 = code.length at hlen; omega)
    (by simp [incoherentSource])
  have hsecond := h.code_eq 1#usize 3#usize (bytes [1#u8, 0#u8]) (by decide)
    (by change 3 ≤ code.length; change 3 = code.length at hlen; omega)
    (by simp [incoherentSource])
  cases code with
  | nil => simp at hlen
  | cons a rest =>
    cases rest with
    | nil => simp at hlen
    | cons b rest =>
      cases rest with
      | nil => simp at hlen
      | cons c rest =>
        have hf : [0#u8, 0#u8] = [a, b] := by
          simpa [bytes, alloc.vec.Vec.deref, List.slice] using hfirst
        have hs : [1#u8, 0#u8] = [b, c] := by
          simpa [bytes, alloc.vec.Vec.deref, List.slice] using hsecond
        have hb0 : 0#u8 = b := (List.cons.inj (List.cons.inj hf).2).1
        have hb1 : 1#u8 = b := (List.cons.inj hs).1
        have hbad := congrArg UScalar.val (hb0.trans hb1.symm)
        contradiction

local notation "sync" => stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor

/-- The synchronous visitor's `poll_code_batch` returns its one stored completion and clears it;
polling again yields a `Host` error. -/
theorem sync_poll_once :
    (sync).poll_code_batch ⟨some forgedBatch, none⟩ =
      .ok (.Ok forgedBatch, ⟨none, none⟩) ∧
    (sync).poll_code_batch ⟨none, none⟩ = .ok (.Err .Host, ⟨none, none⟩) := by
  exact ⟨Stream.Sync.poll_some _ _ rfl, Stream.Sync.poll_none _ rfl⟩

/-- Retiring a finished record whose ID is not in the pending list returns a `Host` error. -/
theorem replay_rejected :
    stream.retire_code_batch sync 0#u64 ⟨some forgedBatch, none⟩ (alloc.vec.Vec.new Usize) =
      .ok (.Err .Host, ⟨none, none⟩, alloc.vec.Vec.new Usize) := by
  have hs : stream.retire_code_batch_loop (alloc.vec.Vec.new Usize) 0#usize 0#usize = .ok 0#usize := by
    rw [stream.retire_code_batch_loop, loop]
    simp [stream.retire_code_batch_loop.body]
  unfold stream.retire_code_batch
  rw [Stream.Sync.poll_some ⟨some forgedBatch, none⟩ forgedBatch rfl]
  simp [
    core.result.Result.Insts.CoreOpsTry.branch, forgedBatch, impossibleIssued, Stream.Batch.Issued.seed, hs]

/-- A finished record issued for invocation 0 is rejected with a `Host` error when it is retired
under invocation 1, even though its pending list is non-empty. -/
theorem foreign_rejected :
    stream.retire_code_batch sync 1#u64 ⟨some forgedBatch, none⟩ (alloc.vec.Vec.from [0#usize] (by scalar_tac)) =
      .ok (.Err .Host, ⟨none, none⟩, alloc.vec.Vec.from [0#usize] (by scalar_tac)) := by
  unfold stream.retire_code_batch
  rw [Stream.Sync.poll_some ⟨some forgedBatch, none⟩ forgedBatch rfl]
  simp [
    core.result.Result.Insts.CoreOpsTry.branch, forgedBatch, impossibleIssued, Stream.Batch.Issued.seed]

/-- `stream.find_code_region` on an empty buffer returns the empty region `(0, 0)`. -/
theorem empty_split : stream.find_code_region emptyBytes = .ok (0#usize, 0#usize) := by
  rw [stream.find_code_region, stream.find_code_region_loop, loop]
  simp [stream.find_code_region_loop.body, emptyBytes, bytes, alloc.vec.Vec.deref]
  rfl

/-- `stream.validate_module_slice` on an empty buffer reports `UnexpectedEof` from the missing
module header. -/
theorem empty_slice_rejected : stream.validate_module_slice emptyBytes =
    .ok (.Err (.Read .UnexpectedEof)) := by
  have hslice : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      emptyBytes { start := 0#usize, «end» := 0#usize } = .ok emptyBytes := by
    simp [Slice.index_SliceIndexRangeUsizeSliceInst,
      core.slice.index.SliceIndexRangeUsizeSlice.index, emptyBytes, bytes, alloc.vec.Vec.deref]
  change core.slice.index.SliceIndexRangeUsizeSlice.index
    { start := 0#usize, «end» := 0#usize } emptyBytes = .ok emptyBytes at hslice
  have hlen : Slice.len emptyBytes = 0#usize := rfl
  have hadd : limits.add_offset 0#usize 0#usize = .ok (.Ok 0#usize) := by
    obtain ⟨sum, hs, hv⟩ := limits.add_offset.complete 0#usize 0#usize (by simp)
    have he : sum = 0#usize := by apply UScalar.eq_of_val_eq; simpa using hv
    simpa [he] using hs
  have hheader : metadata.read_header emptyBytes = .ok (.Err (.Read .UnexpectedEof)) := by
    simp [metadata.read_header, reader.read_byte, hlen, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  unfold stream.validate_module_slice
  rw [empty_split]
  simp only [bind_ok, Std.uncurry, hlen]
  simp [hslice, metadata.Env.new, stream.validate_streaming,
    stream.SliceSource.Insts.ItascaStreamSource.environment,
    stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor.custom_region, hlen,
    metadata.validate_env_with, hheader, hadd, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Itasca.Examples.Stream

end
