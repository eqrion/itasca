import Itasca.Stream.DriverSound
import Itasca.Stream.DriverTotal
import Itasca.Stream.DriverComplete

/-!
# Streaming validation

Soundness, termination and completeness of `stream.validate_streaming` for both profiles, with
Wasm 1.0 instances (`wasm_*`). Each claim rests on its own embedding premises from
`Itasca/Contracts`: soundness on `StreamSource.Coherent` and `StreamScheduler.Provenance`,
termination on `StreamSource.CallbacksTotal` and `StreamScheduler.CallbacksTotal`, completeness on
`StreamSource.CanonicalAvailable` and `StreamAcceptingScheduler.Accepts`.

The soundness and completeness statements return a `StreamRun.Accepted` record of the driver run
to name the tail the driver delivered to `tail_ready`.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary ModuleElaboration

/-- Acceptance of the streaming driver certifies the concatenated bytes, its returned
environment, and the tail it actually received, and bounds their size by the module cap.
Soundness requires coherent source views and worker provenance. Read errors and callback failures
are allowed, and neither callback termination, a canonical region split nor prevalidated bodies
are needed. -/
theorem stream.validate_streaming.profile_sound {profile : ValidationProfile} {S V : Type}
    (source : stream.Source S) (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List StreamBatch.Issued → V → Prop)
    (hp : StreamScheduler.Provenance visitor Tracks profile)
    (id : U64) (state : S) (v v' : V) (storage env : module.Env)
    (data environment code tail : Slice U8)
    (hsource : StreamSource.Coherent source state environment.val code.val tail.val)
    (hbytes : data.val = environment.val ++ code.val ++ tail.val)
    (hv : Tracks id [] v)
    (h : stream.validate_streaming source visitor id profile state v storage = .ok (.Ok (), v', env)) :
    ∃ run : StreamRun.Accepted source visitor id state v v' env profile,
      ModuleSound.Validated data ⟨env, run.remaining.tail⟩ profile ∧
      data.length ≤ limits.MAX_MODULE_BYTES.val :=
  stream.validate_streaming.sound source visitor Tracks hp id state v v' storage env
    data environment code tail hsource hbytes hv h

/-- `stream.validate_streaming` returns success or an error on arbitrary bytes when the source and
scheduler callbacks return. Neither successful batches, source coherence nor scheduler provenance
is a termination premise. -/
theorem stream.validate_streaming.profile_total {profile : ValidationProfile} {S V : Type}
    (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (moduleId : U64) (state : S)
    (v : V) (storage : module.Env)
    (hs : StreamSource.CallbacksTotal source state) (hv : StreamScheduler.CallbacksTotal visitor profile) :
    ∃ r, stream.validate_streaming source visitor moduleId profile state v storage = .ok r :=
  stream.validate_streaming.total source visitor moduleId state v storage hs hv

/-- Independently encoded, elaborated, typed modules within the selected profile and limits are
accepted by `stream.validate_streaming` under canonical available reads and an accepting
scheduler. The returned environment and delivered tail describe the same raw module, including
public metadata. Completeness fails if reads are unavailable or workers do not accept. -/
theorem stream.validate_streaming.profile_complete {profile : ValidationProfile} {S V : Type}
    (source : stream.Source S) (visitor : stream.StreamingVisitor V)
    (config : stream.Config) (Queued : U64 → List StreamBatch.Issued → V → Prop)
    (ha : StreamAcceptingScheduler.Accepts visitor config Queued profile)
    (id : U64) (state : S) (before : V) (storage : module.Env)
    (data : Slice U8) (raw : ModuleBinary.Module)
    (hb : ModuleEncodingWithinLimits raw data.val profile)
    (hsignatures : ModuleSignaturesWithinLimits raw)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Profile raw profile)
    (hs : StreamSource.CanonicalAvailable source state data) (hv : Queued id [] before) :
    ∃ env after, ∃ run : StreamRun.Accepted source visitor id state before after env profile,
      stream.validate_streaming source visitor id profile state before storage = .ok (.Ok (), after, env) ∧
      Matches env run.remaining.tail raw ∧ AccessorTypes env raw ∧ Queued id [] after :=
  stream.validate_streaming.complete source visitor config Queued ha id state before storage
    data raw hb hsignatures he ht hp hs hv

/-- The Wasm 1.0 instance of `stream.validate_streaming.profile_sound`. -/
theorem stream.validate_streaming.wasm_sound {S V : Type}
    (source : stream.Source S) (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List StreamBatch.Issued → V → Prop)
    (hp : StreamScheduler.Provenance visitor Tracks)
    (id : U64) (state : S) (v v' : V) (storage env : module.Env)
    (data environment code tail : Slice U8)
    (hsource : StreamSource.Coherent source state environment.val code.val tail.val)
    (hbytes : data.val = environment.val ++ code.val ++ tail.val)
    (hv : Tracks id [] v)
    (h : stream.validate_streaming source visitor id .Wasm1 state v storage = .ok (.Ok (), v', env)) :
    ∃ run : StreamRun.Accepted source visitor id state v v' env,
      ModuleSound.Validated data ⟨env, run.remaining.tail⟩ ∧
      data.length ≤ limits.MAX_MODULE_BYTES.val :=
  stream.validate_streaming.profile_sound source visitor Tracks hp id state v v' storage env
    data environment code tail hsource hbytes hv h

/-- The Wasm 1.0 instance of `stream.validate_streaming.profile_total`. -/
theorem stream.validate_streaming.wasm_total {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (moduleId : U64) (state : S)
    (v : V) (storage : module.Env)
    (hs : StreamSource.CallbacksTotal source state) (hv : StreamScheduler.CallbacksTotal visitor) :
    ∃ r, stream.validate_streaming source visitor moduleId .Wasm1 state v storage = .ok r :=
  stream.validate_streaming.profile_total source visitor moduleId state v storage hs hv

/-- The Wasm 1.0 instance of `stream.validate_streaming.profile_complete`. -/
theorem stream.validate_streaming.wasm_complete {S V : Type}
    (source : stream.Source S) (visitor : stream.StreamingVisitor V)
    (config : stream.Config) (Queued : U64 → List StreamBatch.Issued → V → Prop)
    (ha : StreamAcceptingScheduler.Accepts visitor config Queued)
    (id : U64) (state : S) (before : V) (storage : module.Env)
    (data : Slice U8) (raw : ModuleBinary.Module)
    (hb : ModuleEncodingWithinLimits raw data.val)
    (hsignatures : ModuleSignaturesWithinLimits raw)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Profile raw)
    (hs : StreamSource.CanonicalAvailable source state data) (hv : Queued id [] before) :
    ∃ env after, ∃ run : StreamRun.Accepted source visitor id state before after env,
      stream.validate_streaming source visitor id .Wasm1 state before storage = .ok (.Ok (), after, env) ∧
      Matches env run.remaining.tail raw ∧ AccessorTypes env raw ∧ Queued id [] after :=
  stream.validate_streaming.profile_complete source visitor config Queued ha id state before storage
    data raw hb hsignatures he ht hp hs hv

end Itasca
