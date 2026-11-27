import Aeneas
import ItascaRust.Funs
import Itasca.Results.Definitions.Binary
import Itasca.Results.Definitions.Validation
import WebAssembly

/-!
# Coherent sources and issued workers

Streaming validation consumes independently obtained byte regions and batches that may
finish out of order. These contracts explain why those pieces describe one module:
coherent views fix logical bytes, issuance and reachability retain worker provenance, and
scheduler contracts govern return and acceptance. Framing is not validation. Storage
lifetimes and Rust ownership remain embedding obligations, not a concurrent Lean execution
model.

-/

/-! ## StreamingContracts -/

section StreamingContracts

/-!
## Embedding contracts

The obligations that the streaming headline theorems in `Itasca/Results/` place on an embedding:
the `stream.StreamingSource` implementation, the `stream.StreamingVisitor` scheduling code batches, and
the custom-section hooks of its module visitor.

| Claim | Requires |
| --- | --- |
| Soundness | `Stream.Source.Describes`, `Stream.Scheduler.Provenance` |
| Termination | `Stream.Source.CallbacksTotal`, `Stream.Scheduler.CallbacksTotal` |
| Completeness | `Stream.Source.CanonicalAvailable`, `Stream.Scheduler.Accepts` |

Soundness allows read errors and any split. The driver itself checks pending IDs and completion,
so provenance does not assume workers finish. The accepting scheduler is one sufficient policy,
not the only one. Logical coherence across separate source calls remains the embedding's
obligation.

This file holds definitions only, together with the worker and region vocabulary they mention
(`Stream.Batch.Issued`, `Stream.Batch.Reachable`, `Stream.CompleteRegions.Split`).
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Tail

/-- The visitor's custom-section hook returns normally for every state and chunk. It may still
reject; totality excludes only panics and divergence. -/
def HooksTotal {V : Type} (visitor : metadata.ModuleVisitor V) : Prop :=
  ∀ (v : V) (chunk : wasm_types.CustomSection), ∃ r, visitor.on_custom_section v chunk = .ok r

/-- The custom section hooks always return normally and accept. -/
def HooksAccept {V : Type} (visitor : metadata.ModuleVisitor V) : Prop :=
  ∀ (v : V) (chunk : wasm_types.CustomSection),
    ∃ v', visitor.on_custom_section v chunk = .ok (.Ok (), v')

/-- The visitor's `on_custom_section` hook preserves the predicate `P` on its state across
successful calls. Hooks may advance workers, and no fixed work observation is required. -/
def PreservesInvariant {V : Type} (visitor : metadata.ModuleVisitor V) (P : V → Prop) : Prop :=
  ∀ v chunk v', visitor.on_custom_section v chunk = .ok (.Ok (), v') → P v → P v'

end Itasca.Module.Tail

namespace Itasca.CodeEntry

/-- Arithmetic bounds provided by the decoder for entry validation. The imported
function prefix fits in the descriptor vector, and expanded locals fit in a vector. -/
structure Bounds (env : metadata.CodeMetadata) : Prop where
  imported : env.num_imported_funcs.val ≤ env.funcs.val.length
  locals : ∀ ft ∈ env.types.val, ft.params.val.length + limits.MAX_LOCALS.val ≤ Usize.max

end Itasca.CodeEntry

namespace Itasca.Stream.Source

/-- Soundness premise on the source: successful views agree with fixed logical environment, code
and tail bytes. Read errors are permitted; neither availability nor a canonical module split is
assumed. -/
structure Coherent {S : Type} (source : stream.StreamingSource S) (state : S)
    (environment code tail : List U8) : Prop where
  /-- Every successful environment view contains the fixed environment bytes. -/
  environment_eq : ∀ bytes, source.environment state = .ok (.Ok bytes) →
    bytes.val = environment
  /-- The reported code-region length agrees with the fixed logical code bytes. -/
  code_len_eq : ∀ len, source.code_len state = .ok len → len.val = code.length
  /-- Every successful in-bounds read agrees with the same logical code slice. -/
  code_eq : ∀ first last bytes, first.val ≤ last.val → last.val ≤ code.length →
    source.code state first last = .ok (.Ok bytes) →
    bytes.val = code.slice first.val last.val
  /-- Every successful tail view contains the fixed tail bytes. -/
  tail_eq : ∀ bytes, source.tail state = .ok (.Ok bytes) → bytes.val = tail

/-- Successful source views describe one fixed module byte string. The split need
not be canonical and reads may fail; the driver checks framing before accepting.
All successful overlapping code reads agree with these same logical bytes. -/
def Describes {S : Type} (source : stream.StreamingSource S) (state : S) (data : Slice U8) : Prop :=
  ∃ regions : stream.SliceSource,
    data.val = regions.env.val ++ regions.code.val ++ regions.tail.val ∧
    Coherent source state regions.env.val regions.code.val regions.tail.val

/-- Successful reads of the given regions. It prescribes successful reads without identifying the
regions with a valid module or requiring canonical splitting. -/
structure Available {S : Type} (source : stream.StreamingSource S) (state : S)
    (environment code tail : List U8) : Prop where
  /-- The source supplies the specified environment view successfully. -/
  environment_read : ∃ bytes, source.environment state = .ok (.Ok bytes) ∧
    bytes.val = environment
  /-- The source returns the specified code-region length. -/
  code_len_read : ∃ len, source.code_len state = .ok len ∧ len.val = code.length
  /-- Every well-ordered in-bounds code slice is successfully readable. -/
  code_read : ∀ first last, first.val ≤ last.val → last.val ≤ code.length →
    ∃ bytes, source.code state first last = .ok (.Ok bytes) ∧
      bytes.val = code.slice first.val last.val
  /-- The source supplies the specified tail view successfully. -/
  tail_read : ∃ bytes, source.tail state = .ok (.Ok bytes) ∧ bytes.val = tail

/-- Termination premise on the source: its callbacks return ordinary modeled results. This allows
Rust errors and says nothing about the bytes. -/
structure CallbacksTotal {S : Type} (source : stream.StreamingSource S) (state : S) : Prop where
  /-- Environment access returns normally, including a possible Rust read error. -/
  environment_returns : ∃ r, source.environment state = .ok r
  /-- Code-length access returns normally. -/
  code_len_returns : ∃ len, source.code_len state = .ok len
  /-- Code access returns normally for arbitrary endpoint arguments. -/
  code_returns : ∀ first last, ∃ r, source.code state first last = .ok r
  /-- Tail access returns normally, including a possible Rust read error. -/
  tail_returns : ∃ r, source.tail state = .ok r

end Itasca.Stream.Source

namespace Itasca.Stream.CompleteRegions

/-- Consecutive framed sections before code. Custom sections and data-count
sections belong to the environment; section IDs 10 and 11 end this prefix. -/
inductive Prefix (data : Slice U8) : Usize → Usize → Prop where
  | empty (pos) : Prefix data pos pos
  | skip {pos first next last id} :
      Binary.SectionHeader data pos id first next →
      (id.val < 10 ∨ id.val = 12) → Prefix data next last → Prefix data pos last

/-- Canonical byte boundaries: scan past the eight-byte module header and
preceding sections, then include the complete code section if present. Without
code, the environment ends at the first later non-data-count section or EOF.
This relation contains no parser or slice-operation calls. -/
structure Boundaries (data : Slice U8) (first last : Usize) : Prop where
  preceding : Prefix data 8#usize first
  stop : (∃ content, Binary.SectionHeader data first 10#u8 content last) ∨
    (last = first ∧ (first = Slice.len data ∨ ∃ id content finish,
      Binary.SectionHeader data first id content finish ∧ 10 < id.val ∧ id.val ≠ 12))

/-- The three buffers contain exactly the canonical byte regions. -/
def Split (data : Slice U8) (source : stream.SliceSource) : Prop :=
  ∃ first last, Boundaries data first last ∧
    source.env.val = data.val.slice 0 first.val ∧
    source.code.val = data.val.slice first.val last.val ∧
    source.tail.val = data.val.slice last.val data.length

end Itasca.Stream.CompleteRegions

namespace Itasca.Stream.Source

/-- Completeness premise on the source: it makes the canonical regions of `data` readable, that
is the independent section-boundary relation `CompleteRegions.Split`. This says nothing
about parser success or worker validation. -/
def CanonicalAvailable {S : Type} (source : stream.StreamingSource S) (state : S) (data : Slice U8) : Prop :=
  ∃ regions : stream.SliceSource, Stream.CompleteRegions.Split data regions ∧
    Available source state regions.env.val regions.code.val regions.tail.val

end Itasca.Stream.Source

namespace Itasca.Stream.Batch

/-- Immutable description of the exact state issued by the driver. -/
structure Issued where
  /-- Driver invocation identity carried by every returned worker. -/
  module_id : U64
  /-- Batch identity assigned within that invocation. -/
  batch_id : Usize
  /-- Immutable decoded environment shared by the batch's workers. -/
  env : metadata.CodeMetadata
  /-- Exact bytes of the framed entries assigned to this batch. -/
  code : Slice U8
  /-- Start of `code` measured from the complete code-region origin. -/
  code_offset : Usize
  /-- First defined-function index assigned to this batch. -/
  first_func : Usize
  /-- Number of consecutive defined functions assigned to the batch. -/
  num_funcs : Usize

/-- Workers begin with independent zeroed dispatch and validation cursors. -/
def Issued.seed (issued : Issued) : stream.StreamingBatch :=
  { module_id := issued.module_id, batch_id := issued.batch_id,
    env := issued.env, code := issued.code, code_offset := issued.code_offset,
    first_func := issued.first_func, num_funcs := issued.num_funcs,
    num_dispatched := 0#usize, dispatch_end := 0#usize,
    num_validated := 0#usize, validated_end := 0#usize, error := none }

/-- Bounds supplied by framing and the actual environment decode, separately
from the operation history of a worker. -/
def Issued.Bounded (issued : Issued) : Prop :=
  0 < issued.num_funcs.val ∧
  issued.first_func.val + issued.num_funcs.val ≤ (Translation.Environment.definedTypeIndices issued.env).length ∧
  issued.code_offset.val + issued.code.length ≤ limits.MAX_MODULE_BYTES.val

/-- Workers obtainable from the seed of `issued` through actual `stream.StreamingBatch.next_entry` and
`stream.StreamingBatch.validate_func` executions. No constructor can assign a validation cursor or
assert successful finishing. -/
inductive Reachable (issued : Issued) : stream.StreamingBatch → Prop where
  | seed : Reachable issued issued.seed
  | dispatch {before after result} : Reachable issued before →
      stream.StreamingBatch.next_entry before = .ok (result, after) → Reachable issued after
  | validate {V : Type} (visitor : code.OpVisitor V) {before after index v v' result} :
      Reachable issued before →
      stream.StreamingBatch.validate_func visitor before index v = .ok (result, after, v') →
      Reachable issued after

end Itasca.Stream.Batch

namespace Itasca.Stream.Retirement

/-- Polling returns an ordinary result in every visitor state. It may report an error or return
an arbitrary record. Termination of retirement needs no batch provenance, worker correctness or
successful finish. -/
def PollTotal {V : Type} (visitor : stream.StreamingVisitor V) : Prop :=
  ∀ state, ∃ r, visitor.poll_code_batch state = .ok r

end Itasca.Stream.Retirement

namespace Itasca.Stream.Scheduler

/-- Termination premise on the scheduler: every callback of the visitor returns an ordinary
result. Submission is only required to return for seeds of bounded issued batches. Rust errors and malformed returned worker records are allowed, and
nothing is assumed
about the workers. This is independent of the soundness provenance contract. -/
structure CallbacksTotal {V : Type} (visitor : stream.StreamingVisitor V) : Prop where
  /-- Custom-section callbacks return normally for all visitor states/chunks. -/
  custom : Module.Tail.HooksTotal visitor.metadataModuleVisitorInst
  /-- Selecting a custom-section region returns normally. -/
  region : ∀ v region, ∃ v', visitor.custom_region v region = .ok v'
  /-- Environment notification returns normally for any supplied metadata. -/
  environment : ∀ v env, ∃ r, visitor.environment_ready v env = .ok r
  /-- Submitting a bounded issued seed returns normally; acceptance is optional. -/
  submit : ∀ v (issued : Stream.Batch.Issued), issued.Bounded → CodeEntry.Bounds issued.env →
    ∃ r, visitor.submit_code_batch v issued.seed = .ok r
  /-- Polling returns normally without assuming worker provenance or completion. -/
  poll : Stream.Retirement.PollTotal visitor
  /-- End-of-code notification returns normally. -/
  code_end : ∀ v, ∃ r, visitor.code_end v = .ok r

/-- Soundness premise on the scheduler: returned workers derive from issued seeds through
`Stream.Batch.Reachable`. The scheduler tracks the history of issued batches across every
callback, and a polled batch whose module and batch IDs match a historical issued batch is
reachable from it through actual batch operations, which does not mean the worker succeeded.
Unknown, foreign, unfinished and replayed batches are permitted. The driver checks pending IDs and
finish. -/
structure Provenance {V : Type} (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List Stream.Batch.Issued → V → Prop) : Prop where
  /-- Successful custom-section callbacks preserve the historical batch tracker. -/
  custom : ∀ id history, Module.Tail.PreservesInvariant
    visitor.metadataModuleVisitorInst (Tracks id history)
  /-- Region selection preserves the same invocation and batch history. -/
  region : ∀ id history v region v', Tracks id history v →
    visitor.custom_region v region = .ok v' → Tracks id history v'
  /-- Successful environment notification preserves that history. -/
  environment : ∀ id history v env config v', Tracks id history v →
    visitor.environment_ready v env = .ok (.Ok config, v') → Tracks id history v'
  /-- Successful submission appends its fresh, matching issued batch to history. -/
  submit : ∀ id history issued v v', Tracks id history v →
    issued.module_id = id → issued.Bounded → CodeEntry.Bounds issued.env →
    (∀ old ∈ history, old.batch_id ≠ issued.batch_id) →
    visitor.submit_code_batch v issued.seed = .ok (.Ok (), v') →
    Tracks id (history ++ [issued]) v'
  /-- Every polled worker matching a historical identity is actually reachable
  from that issued seed; polling preserves the full history. -/
  poll : ∀ id history v batch v', Tracks id history v →
    visitor.poll_code_batch v = .ok (.Ok batch, v') →
    Tracks id history v' ∧ ∀ issued ∈ history,
      issued.module_id = batch.module_id → issued.batch_id = batch.batch_id →
      Stream.Batch.Reachable issued batch
  /-- Successful end-of-code notification preserves history. -/
  code_end : ∀ id history v v', Tracks id history v →
    visitor.code_end v = .ok (.Ok (), v') → Tracks id history v'

/-- Completeness premise on the scheduler: positive batch settings, accepting callbacks, and
actual `stream.StreamingBatch.validate_all` results in any order. Each returned worker is the actual
result of `validate_all` on an issued seed, including its possible validation error.
The scheduler does not assume valid Wasm or successful finishing. This is one
sufficient policy, not a characterization of every possible worker strategy. The visitor state is tracked by `Queued`, which lists the issued batches not yet
polled. -/
structure Accepts {V : Type} (visitor : stream.StreamingVisitor V)
    (config : stream.StreamingConfig) (Queued : U64 → List Stream.Batch.Issued → V → Prop) : Prop where
  /-- Framing can make progress with a positive configured batch size. -/
  batch_positive : 0 < config.batch_bytes.val
  /-- The scheduler can retain at least one outstanding batch. -/
  capacity_positive : 0 < config.max_batches.val
  /-- Custom-section callbacks return normally and accept. -/
  custom_accepts : Module.Tail.HooksAccept visitor.metadataModuleVisitorInst
  /-- Successful custom-section callbacks retain the outstanding queue. -/
  custom_preserves : ∀ id queue, Module.Tail.PreservesInvariant
    visitor.metadataModuleVisitorInst (Queued id queue)
  /-- Region selection returns with the same outstanding queue. -/
  region : ∀ id queue v region, Queued id queue v →
    ∃ v', visitor.custom_region v region = .ok v' ∧ Queued id queue v'
  /-- Environment notification accepts and supplies this configuration. -/
  environment : ∀ id queue v env, Queued id queue v →
    ∃ v', visitor.environment_ready v env = .ok (.Ok config, v') ∧ Queued id queue v'
  /-- A bounded issued batch is accepted and appended while queue capacity remains,
  even when its bytes are invalid. The bounds ensure worker operations can return. -/
  submit : ∀ id queue issued v, Queued id queue v → issued.Bounded → CodeEntry.Bounds issued.env →
    issued.module_id = id → queue.length < config.max_batches.val →
    ∃ v', visitor.submit_code_batch v issued.seed = .ok (.Ok (), v') ∧
      Queued id (queue ++ [issued]) v'
  /-- Polling removes any queued batch and returns the actual `validate_all`
  result on its issued seed. Queue permutation permits out-of-order completion. -/
  poll : ∀ id queue v, Queued id queue v → queue ≠ [] →
    ∃ issued rest after v', (issued :: rest).Perm queue ∧
      visitor.poll_code_batch v = .ok (.Ok after, v') ∧
      stream.StreamingBatch.validate_all issued.seed = .ok after ∧ Queued id rest v'
  /-- End-of-code notification accepts and retains the queue. -/
  code_end : ∀ id queue v, Queued id queue v →
    ∃ v', visitor.code_end v = .ok (.Ok (), v') ∧ Queued id queue v'

end Itasca.Stream.Scheduler

end StreamingContracts
