import Itasca.Stream.FramingComplete
import Itasca.Stream.Sync
import Itasca.Stream.SplitTotal
import Itasca.Examples.Module.Support

/-!
# Adversarial streaming cases

Kernel-checked examples for the streaming API (`stream.CodeBatch`, `stream.Source`,
`stream.retire_code_batch`, `stream.validate_module_slice`). They show why the guarantees
need the issued-batch provenance (`StreamBatch.Reachable`) and source coherence
(`StreamSource.Coherent`) premises: a forged finished batch, an incoherent source, and replayed or
foreign batch completions. They also show that splitting a truncated buffer stays in bounds.
-/

open Aeneas Aeneas.Std

namespace Itasca.Examples.Stream

open ModuleSupport (bytes)

/-- A module environment with no types, imports, functions, tables, memories or globals. -/
def emptyEnv : module.Env where
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
def impossibleIssued : StreamBatch.Issued :=
  ⟨0#u64, 0#usize, emptyEnv, emptyBytes, 0#usize, 0#usize, 1#usize, .Wasm1⟩

/-- An arbitrary extracted record can forge the private validation cursor. -/
def forgedBatch : stream.CodeBatch :=
  { impossibleIssued.seed with num_validated := 1#usize }

/-- `stream.CodeBatch.finish` accepts the forged record, so the finish check alone does not
establish provenance in the extracted model. -/
theorem forged_finish : stream.CodeBatch.finish forgedBatch = .ok (.Ok ()) := by
  rw [stream.CodeBatch.finish.accepted_iff]
  simp [forgedBatch, impossibleIssued, StreamBatch.Issued.seed, emptyBytes, bytes,
    alloc.vec.Vec.deref]
  rfl

/-- No sequence of actual batch operations can manufacture this successful
finish: the empty environment rejects every function-entry validation. -/
theorem forged_unreachable : ¬ StreamBatch.Reachable impossibleIssued forgedBatch := by
  intro h
  have hzero : ∀ {count pos}, StreamBatch.Prefix impossibleIssued count pos → count = 0 := by
    intro count pos hp
    induction hp with
    | nil => rfl
    | snoc visitor previous index run ih =>
      simp [impossibleIssued, emptyEnv, module.validate_code_entry_with] at run
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
    ¬ StreamSource.Coherent incoherentSource () environment code tail := by
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
  exact ⟨StreamSync.poll_some _ _ rfl, StreamSync.poll_none _ rfl⟩

/-- Retiring a finished record whose ID is not in the pending list returns a `Host` error. -/
theorem replay_rejected :
    stream.retire_code_batch sync 0#u64 ⟨some forgedBatch, none⟩ (alloc.vec.Vec.new Usize) =
      .ok (.Err .Host, ⟨none, none⟩, alloc.vec.Vec.new Usize) := by
  have hs : stream.retire_code_batch_loop (alloc.vec.Vec.new Usize) 0#usize 0#usize = .ok 0#usize := by
    rw [stream.retire_code_batch_loop, loop]
    simp [stream.retire_code_batch_loop.body]
  unfold stream.retire_code_batch
  rw [StreamSync.poll_some ⟨some forgedBatch, none⟩ forgedBatch rfl]
  simp [
    core.result.Result.Insts.CoreOpsTry.branch, forgedBatch, impossibleIssued, StreamBatch.Issued.seed, hs]

/-- A finished record issued for invocation 0 is rejected with a `Host` error when it is retired
under invocation 1, even though its pending list is non-empty. -/
theorem foreign_rejected :
    stream.retire_code_batch sync 1#u64 ⟨some forgedBatch, none⟩ (alloc.vec.Vec.from [0#usize] (by scalar_tac)) =
      .ok (.Err .Host, ⟨none, none⟩, alloc.vec.Vec.from [0#usize] (by scalar_tac)) := by
  unfold stream.retire_code_batch
  rw [StreamSync.poll_some ⟨some forgedBatch, none⟩ forgedBatch rfl]
  simp [
    core.result.Result.Insts.CoreOpsTry.branch, forgedBatch, impossibleIssued, StreamBatch.Issued.seed]

/-- `stream.find_code_region` on an empty buffer returns the empty region `(0, 0)`. -/
theorem empty_split : stream.find_code_region emptyBytes = .ok (0#usize, 0#usize) := by
  rw [stream.find_code_region, stream.find_code_region_loop, loop]
  simp [stream.find_code_region_loop.body, emptyBytes, bytes, alloc.vec.Vec.deref]
  rfl

/-- `stream.validate_module_slice` on an empty buffer reports `UnexpectedEof` from the missing
module header. -/
theorem empty_slice_rejected : stream.validate_module_slice emptyBytes .Wasm1 =
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
  have hheader : module.read_header emptyBytes = .ok (.Err (.Read .UnexpectedEof)) := by
    simp [module.read_header, reader.read_byte, hlen, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  unfold stream.validate_module_slice
  rw [empty_split]
  simp only [bind_ok, Std.uncurry, hlen]
  simp [hslice, module.Env.new, stream.validate_streaming,
    stream.SliceSource.Insts.ItascaStreamSource.environment,
    stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor.custom_region, hlen,
    module.validate_env_with, hheader, hadd, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Itasca.Examples.Stream
