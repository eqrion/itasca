import Itasca.Module.Code.Section
import Itasca.Profile.Types

/-!
# Embedding contracts

The obligations that the streaming headline theorems in `Itasca/Results/` place on an embedding:
the `stream.Source` implementation, the `stream.StreamingVisitor` scheduling code batches, and
the custom-section hooks of its module visitor.

| Claim | Requires |
| --- | --- |
| Soundness | `StreamSource.Coherent`, `StreamScheduler.Provenance` |
| Termination | `StreamSource.CallbacksTotal`, `StreamScheduler.CallbacksTotal` |
| Completeness | `StreamSource.CanonicalAvailable`, `StreamAcceptingScheduler.Accepts` |

Soundness allows read errors and any split. The driver itself checks pending IDs and completion,
so provenance does not assume workers finish. The accepting scheduler is one sufficient policy,
not the only one. Logical coherence across separate source calls remains the embedding's
obligation.

This file holds definitions only, together with the worker and region vocabulary they mention
(`StreamBatch.Issued`, `StreamBatch.Reachable`, `StreamCompleteRegions.Split`).
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleTail

/-- The visitor's custom-section hook returns normally for every state and chunk. It may still
reject; totality excludes only panics and divergence. -/
def HooksTotal {V : Type} (visitor : module.ModuleVisitor V) : Prop :=
  ∀ (v : V) (chunk : types.CustomSection), ∃ r, visitor.on_custom_section v chunk = .ok r

/-- The custom section hooks always return normally and accept. -/
def HooksAccept {V : Type} (visitor : module.ModuleVisitor V) : Prop :=
  ∀ (v : V) (chunk : types.CustomSection),
    ∃ v', visitor.on_custom_section v chunk = .ok (.Ok (), v')

/-- The visitor's `on_custom_section` hook preserves the predicate `P` on its state across
successful calls. Hooks may advance workers, and no fixed work observation is required. -/
def PreservesInvariant {V : Type} (visitor : module.ModuleVisitor V) (P : V → Prop) : Prop :=
  ∀ v chunk v', visitor.on_custom_section v chunk = .ok (.Ok (), v') → P v → P v'

end Itasca.ModuleTail

namespace Itasca.CodeEntry

/-- Parameters plus the maximum local count fit in a `Usize` for every function type. The
environment decoder supplies this. The validator accepts arbitrary environments, but concatenating
parameters and locals cannot be total for a caller-built vector already at machine capacity. -/
def Bounds (env : module.Env) : Prop :=
  ∀ ft ∈ env.types.val, ft.params.val.length + limits.MAX_LOCALS.val ≤ Usize.max

end Itasca.CodeEntry

namespace Itasca.StreamSource

/-- Soundness premise on the source: successful views agree with fixed logical environment, code
and tail bytes. Read errors are permitted; neither availability nor a canonical module split is
assumed. -/
structure Coherent {S : Type} (source : stream.Source S) (state : S)
    (environment code tail : List U8) : Prop where
  environment_eq : ∀ bytes, source.environment state = .ok (.Ok bytes) →
    bytes.val = environment
  code_len_eq : ∀ len, source.code_len state = .ok len → len.val = code.length
  code_eq : ∀ first last bytes, first.val ≤ last.val → last.val ≤ code.length →
    source.code state first last = .ok (.Ok bytes) →
    bytes.val = code.slice first.val last.val
  tail_eq : ∀ bytes, source.tail state = .ok (.Ok bytes) → bytes.val = tail

/-- Successful reads of the given regions. It prescribes successful reads without identifying the
regions with a valid module or requiring canonical splitting. -/
structure Available {S : Type} (source : stream.Source S) (state : S)
    (environment code tail : List U8) : Prop where
  environment_read : ∃ bytes, source.environment state = .ok (.Ok bytes) ∧
    bytes.val = environment
  code_len_read : ∃ len, source.code_len state = .ok len ∧ len.val = code.length
  code_read : ∀ first last, first.val ≤ last.val → last.val ≤ code.length →
    ∃ bytes, source.code state first last = .ok (.Ok bytes) ∧
      bytes.val = code.slice first.val last.val
  tail_read : ∃ bytes, source.tail state = .ok (.Ok bytes) ∧ bytes.val = tail

/-- Termination premise on the source: its callbacks return ordinary modeled results. This allows
Rust errors and says nothing about the bytes. -/
structure CallbacksTotal {S : Type} (source : stream.Source S) (state : S) : Prop where
  environment_returns : ∃ r, source.environment state = .ok r
  code_len_returns : ∃ len, source.code_len state = .ok len
  code_returns : ∀ first last, ∃ r, source.code state first last = .ok r
  tail_returns : ∃ r, source.tail state = .ok r

end Itasca.StreamSource

namespace Itasca.StreamCompleteRegions

/-- `stream.find_code_region` and the slice operations on `data` produce the environment, code and
tail regions of `source`. -/
def Split (data : Slice U8) (source : stream.SliceSource) : Prop :=
  ∃ codePos tailPos,
    stream.find_code_region data = .ok (codePos, tailPos) ∧
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      data ⟨0#usize, codePos⟩ = .ok source.env ∧
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      data ⟨codePos, tailPos⟩ = .ok source.code ∧
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      data ⟨tailPos, Slice.len data⟩ = .ok source.tail

end Itasca.StreamCompleteRegions

namespace Itasca.StreamSource

/-- Completeness premise on the source: it makes the canonical regions of `data` readable, that
is the environment, code and tail split that `stream.find_code_region` computes. This says nothing
about parser success or worker validation. -/
def CanonicalAvailable {S : Type} (source : stream.Source S) (state : S) (data : Slice U8) : Prop :=
  ∃ regions : stream.SliceSource, StreamCompleteRegions.Split data regions ∧
    Available source state regions.env.val regions.code.val regions.tail.val

end Itasca.StreamSource

namespace Itasca.StreamBatch

/-- Immutable description of the exact state issued by the driver. -/
structure Issued where
  module_id : U64
  batch_id : Usize
  env : module.Env
  code : Slice U8
  code_offset : Usize
  first_func : Usize
  num_funcs : Usize
  profile : ValidationProfile

/-- Workers begin with independent zeroed dispatch and validation cursors. -/
def Issued.seed (issued : Issued) : stream.CodeBatch :=
  { module_id := issued.module_id, batch_id := issued.batch_id,
    profile := issued.profile, env := issued.env, code := issued.code, code_offset := issued.code_offset,
    first_func := issued.first_func, num_funcs := issued.num_funcs,
    num_dispatched := 0#usize, dispatch_end := 0#usize,
    num_validated := 0#usize, validated_end := 0#usize, error := none }

/-- Bounds supplied by framing and the actual environment decode, separately
from the operation history of a worker. -/
def Issued.Bounded (issued : Issued) : Prop :=
  0 < issued.num_funcs.val ∧
  issued.first_func.val + issued.num_funcs.val ≤ issued.env.func_type_indices.val.length ∧
  issued.code_offset.val + issued.code.length ≤ limits.MAX_MODULE_BYTES.val

/-- Workers obtainable from the seed of `issued` through actual `stream.CodeBatch.next_entry` and
`stream.CodeBatch.validate_func` executions. No constructor can assign a validation cursor or
assert successful finishing. -/
inductive Reachable (issued : Issued) : stream.CodeBatch → Prop where
  | seed : Reachable issued issued.seed
  | dispatch {before after result} : Reachable issued before →
      stream.CodeBatch.next_entry before = .ok (result, after) → Reachable issued after
  | validate {V : Type} (visitor : code.OpVisitor V) {before after index v v' result} :
      Reachable issued before →
      stream.CodeBatch.validate_func visitor before index v = .ok (result, after, v') →
      Reachable issued after

end Itasca.StreamBatch

namespace Itasca.StreamRetirement

/-- Polling returns an ordinary result in every visitor state. It may report an error or return
an arbitrary record. Termination of retirement needs no batch provenance, worker correctness or
successful finish. -/
def PollTotal {V : Type} (visitor : stream.StreamingVisitor V) : Prop :=
  ∀ state, ∃ r, visitor.poll_code_batch state = .ok r

end Itasca.StreamRetirement

namespace Itasca.StreamScheduler

/-- Termination premise on the scheduler: every callback of the visitor returns an ordinary
result. Submission is only required to return for seeds of bounded issued batches of the selected
profile. Rust errors and malformed returned worker records are allowed, and nothing is assumed
about the workers. This is independent of the soundness provenance contract. -/
structure CallbacksTotal {V : Type} (visitor : stream.StreamingVisitor V)
    (profile : ValidationProfile := .Wasm1) : Prop where
  custom : ModuleTail.HooksTotal visitor.moduleModuleVisitorInst
  region : ∀ v region, ∃ v', visitor.custom_region v region = .ok v'
  environment : ∀ v env, ∃ r, visitor.environment_ready v env = .ok r
  submit : ∀ v (issued : StreamBatch.Issued), issued.Bounded → CodeEntry.Bounds issued.env → issued.profile = profile →
    ∃ r, visitor.submit_code_batch v issued.seed = .ok r
  poll : StreamRetirement.PollTotal visitor
  code_end : ∀ v, ∃ r, visitor.code_end v = .ok r
  tail_ready : ∀ v tail, ∃ r, visitor.tail_ready v tail = .ok r

/-- Soundness premise on the scheduler: returned workers derive from issued seeds through
`StreamBatch.Reachable`. The scheduler tracks the history of issued batches across every
callback, and a polled batch whose module and batch IDs match a historical issued batch is
reachable from it through actual batch operations, which does not mean the worker succeeded.
Unknown, foreign, unfinished and replayed batches are permitted. The driver checks pending IDs and
finish. -/
structure Provenance {V : Type} (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List StreamBatch.Issued → V → Prop)
    (profile : ValidationProfile := .Wasm1) : Prop where
  custom : ∀ id history, ModuleTail.PreservesInvariant
    visitor.moduleModuleVisitorInst (Tracks id history)
  region : ∀ id history v region v', Tracks id history v →
    visitor.custom_region v region = .ok v' → Tracks id history v'
  environment : ∀ id history v env config v', Tracks id history v →
    visitor.environment_ready v env = .ok (.Ok config, v') → Tracks id history v'
  submit : ∀ id history issued v v', Tracks id history v →
    issued.module_id = id → issued.Bounded → CodeEntry.Bounds issued.env → issued.profile = profile →
    (∀ old ∈ history, old.batch_id ≠ issued.batch_id) →
    visitor.submit_code_batch v issued.seed = .ok (.Ok (), v') →
    Tracks id (history ++ [issued]) v'
  poll : ∀ id history v batch v', Tracks id history v →
    visitor.poll_code_batch v = .ok (.Ok batch, v') →
    Tracks id history v' ∧ ∀ issued ∈ history,
      issued.module_id = batch.module_id → issued.batch_id = batch.batch_id →
      StreamBatch.Reachable issued batch
  code_end : ∀ id history v v', Tracks id history v →
    visitor.code_end v = .ok (.Ok (), v') → Tracks id history v'
  tail_ready : ∀ id history v tail v', Tracks id history v →
    visitor.tail_ready v tail = .ok (.Ok (), v') → Tracks id history v'

end Itasca.StreamScheduler

namespace Itasca.StreamAcceptingScheduler

/-- Independent byte, typing, and size premises for an issued batch. -/
structure Valid (issued : StreamBatch.Issued)
    (validationProfile : ValidationProfile := .Wasm1) : Prop where
  validation_profile : issued.profile = validationProfile
  bounded : issued.Bounded
  entry_bounds : CodeEntry.Bounds issued.env
  profile : Profile.Environment validationProfile issued.env
  limits : Profile.EnvironmentWithinLimits issued.env
  entries : ∃ entries, entries.length = issued.num_funcs.val ∧
    ModuleCode.EntriesTyped (profile := validationProfile) issued.env issued.first_func.val entries ∧
    ModuleBinary.Rep (Profile.CodeEncodingWithinLimits validationProfile) entries issued.code.val

/-- Every batch in the queue belongs to module `id` and is `Valid`. -/
def ValidQueue (id : U64) (queue : List StreamBatch.Issued)
    (validationProfile : ValidationProfile := .Wasm1) : Prop :=
  ∀ issued ∈ queue, issued.module_id = id ∧ Valid issued validationProfile

/-- Completeness premise on the scheduler: positive batch settings, accepting callbacks, and
actual `stream.CodeBatch.validate_all` results in any order. Each returned worker is the actual
result of `validate_all` on an issued seed. Successful finish is derived from `Valid` and is not
required of polling. This is one sufficient policy and does not characterize every possible worker
strategy. The visitor state is tracked by `Queued`, which lists the issued batches not yet
polled. -/
structure Accepts {V : Type} (visitor : stream.StreamingVisitor V)
    (config : stream.Config) (Queued : U64 → List StreamBatch.Issued → V → Prop)
    (validationProfile : ValidationProfile := .Wasm1) : Prop where
  batch_positive : 0 < config.batch_bytes.val
  capacity_positive : 0 < config.max_batches.val
  custom_accepts : ModuleTail.HooksAccept visitor.moduleModuleVisitorInst
  custom_preserves : ∀ id queue, ModuleTail.PreservesInvariant
    visitor.moduleModuleVisitorInst (Queued id queue)
  region : ∀ id queue v region, Queued id queue v →
    ∃ v', visitor.custom_region v region = .ok v' ∧ Queued id queue v'
  environment : ∀ id queue v env, Queued id queue v →
    ∃ v', visitor.environment_ready v env = .ok (.Ok config, v') ∧ Queued id queue v'
  submit : ∀ id queue issued v, Queued id queue v → Valid issued validationProfile →
    issued.module_id = id → queue.length < config.max_batches.val →
    ∃ v', visitor.submit_code_batch v issued.seed = .ok (.Ok (), v') ∧
      Queued id (queue ++ [issued]) v'
  poll : ∀ id queue v, Queued id queue v → ValidQueue id queue validationProfile → queue ≠ [] →
    ∃ issued rest after v', (issued :: rest).Perm queue ∧
      visitor.poll_code_batch v = .ok (.Ok after, v') ∧
      stream.CodeBatch.validate_all issued.seed = .ok after ∧ Queued id rest v'
  code_end : ∀ id queue v, Queued id queue v →
    ∃ v', visitor.code_end v = .ok (.Ok (), v') ∧ Queued id queue v'
  tail_ready : ∀ id queue v tail, Queued id queue v →
    ∃ v', visitor.tail_ready v tail = .ok (.Ok (), v') ∧ Queued id queue v'

end Itasca.StreamAcceptingScheduler
