import Itasca.Support.Result
import Itasca.Stream.DriverTotal
import Itasca.Stream.Sync
import Itasca.Stream.SplitTotal
import Itasca.Stream.DriverSound

/-!
# Contiguous adapter soundness and termination

`stream.validate_module_slice` splits a contiguous module with `stream.find_code_region` and runs
`stream.validate_streaming` over a `stream.SliceSource` and the synchronous scheduler; the public
`module.validate_module` is this function. `profile_total` shows it returns on arbitrary bytes and
`profile_sound` shows that acceptance gives `ModuleSound.Validated`. Source and scheduler
obligations are discharged by `stream.SliceSource.coherent` and `StreamSync.provenance`, so no
embedding premise remains. `profile_spec` combines both. The `wasm_` theorems are the Wasm 1.0
instances.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- `stream.validate_module_slice` returns on arbitrary input bytes. Its slice source and
synchronous scheduler satisfy every callback premise. -/
theorem stream.validate_module_slice.profile_total (bytes : Slice U8) (profile : ValidationProfile) :
    ∃ r, stream.validate_module_slice bytes profile = .ok r := by
  obtain ⟨⟨first, last⟩, hsplit, _⟩ := WP.spec_imp_exists (stream.find_code_region.spec bytes)
  obtain ⟨environment, code, tail, he, hc, ht, _⟩ := stream.find_code_region.slices bytes first last hsplit
  obtain ⟨env, henv, _⟩ := WP.spec_imp_exists module.Env.new.spec
  obtain ⟨⟨r, visitor, decoded⟩, hr⟩ := stream.validate_streaming.total
    stream.SliceSource.Insts.ItascaStreamSource stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor
    0#u64 ⟨environment, code, tail⟩ ⟨none, none⟩ env
    (stream.SliceSource.callbacks_total _) (StreamSync.callbacks_total (profile := profile))
  unfold stream.validate_module_slice
  simp only [hsplit, bind_ok, Std.uncurry]
  simp only [he, hc, ht, henv, bind_ok, hr, Std.uncurry]
  cases r with
  | Err e => exact ⟨.Err e, by simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]⟩
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    cases visitor.tail with
    | none => exact ⟨.Err .Host, rfl⟩
    | some tail => exact ⟨.Ok ⟨decoded, tail⟩, rfl⟩

/-- If `stream.validate_module_slice` accepts, the returned environment and tail are those of the
accepted streaming run, and they validate the input bytes. -/
theorem stream.validate_module_slice.profile_sound (bytes : Slice U8) (decoded : module.Module)
    (profile : ValidationProfile)
    (h : stream.validate_module_slice bytes profile = .ok (.Ok decoded)) :
    ModuleSound.Validated bytes decoded profile := by
  obtain ⟨⟨first, last⟩, hsplit, _⟩ := WP.spec_imp_exists (stream.find_code_region.spec bytes)
  obtain ⟨environment, code, tail, he, hc, ht, hbytes⟩ := stream.find_code_region.slices bytes first last hsplit
  obtain ⟨storage, hstorage, _⟩ := WP.spec_imp_exists module.Env.new.spec
  simp only [stream.validate_module_slice, hsplit, bind_ok, Std.uncurry] at h
  simp only [he, hc, ht, hstorage, bind_ok] at h
  obtain ⟨⟨r, visitor, env⟩, hrun, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
  | Ok u =>
    cases u
    simp only [Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at h
    cases hstored : visitor.tail with
    | none => simp [hstored] at h
    | some stored =>
      simp [hstored] at h
      subst decoded
      obtain ⟨run, hvalid, _⟩ := stream.validate_streaming.sound
        stream.SliceSource.Insts.ItascaStreamSource stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor
        StreamSync.Tracks (StreamSync.provenance (profile := profile)) 0#u64 ⟨environment, code, tail⟩ ⟨none, none⟩ visitor
        storage env bytes environment code tail (stream.SliceSource.coherent _) hbytes
        (StreamSync.tracks_empty _ _) hrun
      have hready := run.remaining.ready_call
      rw [StreamSync.tail_ready] at hready
      have hreadyEq : run.remaining.ready = { run.remaining.decodedTail with tail := some run.remaining.tail } := by
        simpa using hready.symm
      have hfinal := StreamSync.retire_all_tail 0#u64 run.remaining.ready visitor
        run.remaining.pending run.remaining.remaining run.remaining.drain_call
      rw [hreadyEq, hstored] at hfinal
      have htail : stored = run.remaining.tail := by simpa using hfinal
      simpa [htail] using hvalid

/-- Arbitrary inputs return normally, and every accepted result is `ModuleSound.Validated`, which
includes the independent module certificate and the returned metadata. -/
theorem stream.validate_module_slice.profile_spec (bytes : Slice U8) (profile : ValidationProfile) :
    stream.validate_module_slice bytes profile ⦃ r => match r with
      | .Ok decoded => ModuleSound.Validated bytes decoded profile
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr⟩ := stream.validate_module_slice.profile_total bytes profile
  rw [hr]
  simp only [WP.spec_ok]
  cases r with
  | Err _ => trivial
  | Ok decoded => exact stream.validate_module_slice.profile_sound bytes decoded profile hr

end Itasca
