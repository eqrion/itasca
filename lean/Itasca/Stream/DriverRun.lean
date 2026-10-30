import Itasca.Support.Result
import Itasca.Generated.Funs

/-!
# Accepted driver runs

Unpacks an accepted run of the extracted driver into witnesses for each phase.
`stream.validate_streaming.accepted` and `stream.validate_remaining.accepted` show that an
`Ok` result of `stream.validate_streaming` and of its post-environment phases yields the
`StreamRun.Accepted` and `StreamRun.Remaining` records: the environment read and decode, the code
header, the configuration, the batch submission, the tail read and decode, and the final drain.
The records describe executions of the extracted driver and make no claim about the source or
scheduler.
-/

open Aeneas Aeneas.Std

namespace Itasca.StreamRun

/-- Witnesses of the phases of `stream.validate_remaining` after the environment is decoded,
including the tail handoff. They describe executions of the extracted driver, not an alternate
validator. -/
structure Remaining {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (id : U64) (state : S)
    (env : metadata.Env) (environmentLength : Usize) (before after : V)
    (profile : ValidationProfile := .Wasm1) where
  codeLength : Usize
  codeEnd : Usize
  entries : Usize
  config : stream.Config
  configured : V
  pending : alloc.vec.Vec Usize
  submitted : V
  ended : V
  tailBytes : Slice U8
  moduleEnd : Usize
  region : V
  tail : metadata.Tail
  decodedTail : V
  ready : V
  remaining : alloc.vec.Vec Usize
  length_call : source.code_len state = .ok codeLength
  code_bound : limits.add_offset environmentLength codeLength = .ok (.Ok codeEnd)
  header_call : stream.read_code_header source state codeLength env = .ok (.Ok entries)
  configured_call : visitor.environment_ready before env = .ok (.Ok config, configured)
  batch_bytes_positive : config.batch_bytes ≠ 0#usize
  max_batches_positive : config.max_batches ≠ 0#usize
  submit_call : stream.submit_code_batches source visitor id profile state env codeLength entries config configured =
    .ok (.Ok pending, submitted)
  end_call : visitor.code_end submitted = .ok (.Ok (), ended)
  tail_call : source.tail state = .ok (.Ok tailBytes)
  module_bound : limits.add_offset codeEnd (Slice.len tailBytes) = .ok (.Ok moduleEnd)
  region_call : visitor.custom_region ended .Tail = .ok region
  decode_tail : metadata.validate_tail_with visitor.metadataModuleVisitorInst tailBytes 0#usize env profile region =
    .ok (.Ok tail, decodedTail)
  ready_call : visitor.tail_ready decodedTail tail = .ok (.Ok (), ready)
  drain_call : stream.retire_all_code_batches visitor id ready pending = .ok (.Ok (), after, remaining)

/-- Witnesses of an accepted `stream.validate_streaming`: the environment read, its size bound, the
custom-section region callback, the environment decode, and the `Remaining` phases. -/
structure Accepted {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (id : U64) (state : S)
    (before after : V) (env : metadata.Env)
    (profile : ValidationProfile := .Wasm1) where
  environment : Slice U8
  environmentLength : Usize
  region : V
  decoded : V
  environment_call : source.environment state = .ok (.Ok environment)
  environment_bound : limits.add_offset 0#usize (Slice.len environment) = .ok (.Ok environmentLength)
  region_call : visitor.custom_region before .Environment = .ok region
  decode_environment : metadata.validate_env_with visitor.metadataModuleVisitorInst environment profile region =
    .ok (.Ok (env, environmentLength), decoded)
  remaining : Remaining source visitor id state env environmentLength decoded after profile

end Itasca.StreamRun

namespace Itasca

/-- An accepted `stream.validate_remaining` yields witnesses for each of its phases. -/
theorem stream.validate_remaining.accepted {profile : ValidationProfile} {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (id : U64) (state : S)
    (env : metadata.Env) (envLen : Usize) (v v' : V)
    (h : stream.validate_remaining source visitor id profile state env envLen v = .ok (.Ok (), v')) :
    Nonempty (StreamRun.Remaining source visitor id state env envLen v v' profile) := by
  unfold stream.validate_remaining at h
  obtain ⟨codeLen, hlen, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  obtain ⟨r, hbound, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
  | Ok codeEnd =>
    simp [core.result.Result.Insts.CoreOpsTry.branch] at h
    obtain ⟨r, hheader, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
    | Ok entries =>
      simp at h
      obtain ⟨⟨r, configured⟩, hconfig, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      | Ok config =>
        simp at h
        split at h
        · simp at h
        · rename_i hbytes
          split at h
          · simp at h
          · rename_i hbatches
            obtain ⟨⟨r, submitted⟩, hsubmit, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
            cases r with
            | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
            | Ok pending =>
              simp at h
              obtain ⟨⟨r, ended⟩, hend, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
              cases r with
              | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
              | Ok u =>
                cases u
                simp at h
                obtain ⟨r, htail, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
                cases r with
                | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
                | Ok tailBytes =>
                  simp at h
                  obtain ⟨r, hmodule, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
                  cases r with
                  | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
                  | Ok moduleEnd =>
                    simp at h
                    obtain ⟨region, hregion, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
                    obtain ⟨⟨r, decoded⟩, hdecoded, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
                    cases r with
                    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
                    | Ok tail =>
                      simp at h
                      obtain ⟨⟨r, ready⟩, hready, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
                      cases r with
                      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
                      | Ok u =>
                        cases u
                        simp at h
                        obtain ⟨⟨r, after, remaining⟩, hdrain, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
                        simp at h
                        obtain ⟨rfl, rfl⟩ := h
                        exact ⟨⟨codeLen, codeEnd, entries, config, configured, pending, submitted, ended,
                          tailBytes, moduleEnd, region, tail, decoded, ready, remaining, hlen, hbound,
                          hheader, hconfig, hbytes, hbatches, hsubmit, hend, htail, hmodule, hregion,
                          hdecoded, hready, hdrain⟩⟩

set_option maxHeartbeats 600000 in
/-- An accepted generic driver exposes its decoded environment and the tail delivery it actually
performed. No assumption is made that the visitor state keeps any metadata. -/
theorem stream.validate_streaming.accepted {profile : ValidationProfile} {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (id : U64) (state : S)
    (v v' : V) (initial env : metadata.Env)
    (h : stream.validate_streaming source visitor id profile state v initial = .ok (.Ok (), v', env)) :
    Nonempty (StreamRun.Accepted source visitor id state v v' env profile) := by
  unfold stream.validate_streaming at h
  obtain ⟨r, henv, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
  | Ok environment =>
    simp [core.result.Result.Insts.CoreOpsTry.branch] at h
    obtain ⟨r, hbound, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
    | Ok envLen =>
      simp at h
      obtain ⟨region, hregion, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      obtain ⟨⟨r, decoded⟩, hdecode, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      | Ok pair =>
        obtain ⟨actualEnv, envEnd⟩ := pair
        simp at h
        split at h
        · rename_i heq
          have he : envEnd = envLen := by apply UScalar.eq_of_val_eq; simpa using heq
          subst envEnd
          obtain ⟨⟨r, after⟩, hremaining, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
          simp at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨remaining⟩ := stream.validate_remaining.accepted source visitor id state actualEnv envLen decoded after hremaining
          exact ⟨⟨environment, envLen, region, decoded, henv, hbound, hregion, hdecode, remaining⟩⟩
        · simp at h

end Itasca
