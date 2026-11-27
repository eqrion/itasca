import Itasca.Module.Definitions
import Itasca.Results.Definitions.Streaming

/-! Proof helpers for intermediate states; public results use the semantic
vocabulary in Interface. Keeping these here avoids exposing parser progress
and implementation accounting as part of the public contract. -/

namespace Itasca.Stream.Framing
open Aeneas Aeneas.Std Itasca

/-- The driver observes either an absent code region or an exact bounded
header view. Counts and section size are independent of entry validation. -/
def HeaderChecked {S : Type} (source : stream.StreamingSource S) (state : S)
    (codeLen : Usize) (env : metadata.CodeMetadata) (entries : Usize) : Prop :=
  (codeLen = 0#usize ∧ entries = 0#usize ∧ (Translation.Environment.definedTypeIndices env) = []) ∨
  ∃ header content size count,
    stream.read_exact source state 0#usize (core.cmp.impls.OrdUsize.min codeLen 11#usize) =
      .ok (.Ok header) ∧
    Binary.At Binary.ByteEncoding header 0#usize 10#u8 1#usize ∧
    Binary.Leb128.Decoded header 1#usize size content ∧
    codeLen.val = content.val + size.val ∧
    Binary.Leb128.Decoded header content count entries ∧
    entries.val ≤ codeLen.val ∧ count.val = (Translation.Environment.definedTypeIndices env).length

end Itasca.Stream.Framing

namespace Itasca.Stream.Framing
open Aeneas Aeneas.Std Itasca

/-- The code region is either empty with no declared functions, or a code section whose size
covers the whole region. A present zero-entry section is distinct from an absent one. -/
def HeaderAt (data : Slice U8) (env : metadata.CodeMetadata) (entries : Usize) : Prop :=
  (data.val = [] ∧ entries = 0#usize ∧ (Translation.Environment.definedTypeIndices env) = []) ∨
    ∃ count, Module.Code.Section data 0#usize env ⟨count, entries, Slice.len data⟩ ∧
      entries.val ≤ data.length

end Itasca.Stream.Framing

/-! The bound used by the driver termination argument follows directly from
the header witness; it requires no execution invariant. -/

open Aeneas Aeneas.Std

namespace Itasca.Stream.Framing

/-- A checked header declares no more entries than the code region has bytes. -/
theorem HeaderChecked.entries_le {S : Type} {source : stream.StreamingSource S} {state : S}
    {codeLen : Usize} {env : metadata.CodeMetadata} {entries : Usize}
    (h : HeaderChecked source state codeLen env entries) : entries.val ≤ codeLen.val := by
  rcases h with ⟨rfl, rfl, _⟩ | ⟨_, _, _, _, _, _, _, _, _, hp, _⟩
  · simp
  · exact hp

end Itasca.Stream.Framing

/-! Internal witnesses connect parser phases and scheduler operations. Public
results describe the validated module returned by the driver. -/

namespace Itasca.Stream.Run

/-- Witnesses for code submission, tail decoding and retirement after prefix decoding. They describe executions of the extracted driver, not an alternate
validator. -/
structure Remaining {S V : Type} (source : stream.StreamingSource S)
    (visitor : stream.StreamingVisitor V) (id : U64) (state : S)
    (moduleInfo : metadata.ModuleMetadata metadata.CodeMetadata) (environmentLength : Usize) (before after : V)
     where
  codeLength : Usize
  codeEnd : Usize
  entries : Usize
  config : stream.StreamingConfig
  configured : V
  pending : alloc.vec.Vec Usize
  submitted : V
  ended : V
  tailBytes : Slice U8
  moduleEnd : Usize
  region : V
  tail : alloc.vec.Vec metadata.Data
  decodedTail : V
  remaining : alloc.vec.Vec Usize
  length_call : source.code_len state = .ok codeLength
  code_bound : limits.add_offset environmentLength codeLength = .ok (.Ok codeEnd)
  header_call : stream.read_code_header source state codeLength moduleInfo.code = .ok (.Ok entries)
  configured_call : visitor.environment_ready before moduleInfo = .ok (.Ok config, configured)
  batch_bytes_positive : config.batch_bytes ≠ 0#usize
  max_batches_positive : config.max_batches ≠ 0#usize
  submit_call : stream.submit_code_batches source visitor id state moduleInfo.code codeLength entries config configured =
    .ok (.Ok pending, submitted)
  end_call : visitor.code_end submitted = .ok (.Ok (), ended)
  tail_call : source.tail state = .ok (.Ok tailBytes)
  module_bound : limits.add_offset codeEnd (Slice.len tailBytes) = .ok (.Ok moduleEnd)
  region_call : visitor.custom_region ended .Tail = .ok region
  decode_tail : metadata.validate_tail_with visitor.metadataModuleVisitorInst tailBytes 0#usize moduleInfo.code region =
    .ok (.Ok tail, decodedTail)
  drain_call : stream.retire_all_code_batches visitor id decodedTail pending = .ok (.Ok (), after, remaining)

/-- Witnesses of an accepted `stream.validate_streaming`: the environment read, its size bound, the
custom-section region callback, the environment decode, and the `Remaining` phases. -/
structure Accepted {S V : Type} (source : stream.StreamingSource S)
    (visitor : stream.StreamingVisitor V) (id : U64) (state : S)
    (before after : V) (moduleInfo : metadata.ModuleMetadata metadata.CodeMetadata)
     where
  environment : Slice U8
  environmentLength : Usize
  decodedPrefix : metadata.ModuleMetadata metadata.CodeMetadata
  region : V
  decoded : V
  environment_call : source.environment state = .ok (.Ok environment)
  environment_bound : limits.add_offset 0#usize (Slice.len environment) = .ok (.Ok environmentLength)
  region_call : visitor.custom_region before .Environment = .ok region
  decode_environment : metadata.validate_env_with visitor.metadataModuleVisitorInst environment region =
    .ok (.Ok (decodedPrefix, environmentLength), decoded)
  remaining : Remaining source visitor id state decodedPrefix environmentLength decoded after
  published : moduleInfo = { decodedPrefix with data := remaining.tail }

end Itasca.Stream.Run

namespace Itasca.Stream.CompleteRegions
open Aeneas Aeneas.Std

/-- `stream.find_code_region` and the slice operations on `data` produce the environment, code and
tail regions of `source`. -/
def ComputedSplit (data : Slice U8) (source : stream.SliceSource) : Prop :=
  ∃ codePos tailPos,
    stream.find_code_region data = .ok (codePos, tailPos) ∧
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      data ⟨0#usize, codePos⟩ = .ok source.env ∧
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      data ⟨codePos, tailPos⟩ = .ok source.code ∧
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      data ⟨tailPos, Slice.len data⟩ = .ok source.tail


end Itasca.Stream.CompleteRegions

/-! Independent batch validity used by the completeness proof. Scheduler contracts
only describe work delivery; typing and successful finishing are proved internally. -/

namespace Itasca.Stream.Scheduler
open Aeneas Aeneas.Std Itasca

/-- Independent byte, typing, and size premises for an issued batch. -/
structure Valid (issued : Stream.Batch.Issued) : Prop where
  /-- Framing supplied positive count, function-index and region-size bounds. -/
  bounded : issued.Bounded
  /-- Function parameters plus the local cap fit the modeled machine integer. -/
  entry_bounds : CodeEntry.Bounds issued.env
  /-- All environment signatures satisfy implementation parameter/result caps. -/
  limits : CodeEntry.EnvironmentWithinLimits issued.env
  /-- Exactly the assigned entries are independently encoded and source typed. -/
  entries : ∃ entries, entries.length = issued.num_funcs.val ∧
    Module.Code.EntriesTyped issued.env issued.first_func.val entries ∧
    Binary.Rep CodeEntry.CodeEncodingWithinLimits entries issued.code.val

/-- Every batch in the queue belongs to module `id` and is `Valid`. -/
def ValidQueue (id : U64) (queue : List Stream.Batch.Issued) : Prop :=
  ∀ issued ∈ queue, issued.module_id = id ∧ Valid issued

end Itasca.Stream.Scheduler
