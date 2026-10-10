import Itasca.StreamDriverTotal
import Itasca.StreamSync
import Itasca.StreamSliceSplit
import Itasca.StreamValidation

open Aeneas Aeneas.Std

namespace Itasca

/-- The actual contiguous adapter terminates on arbitrary input bytes. Its
concrete source and synchronous worker discharge every callback assumption. -/
theorem stream.validate_module_slice.wasm_total (bytes : Slice U8) :
    ∃ r, stream.validate_module_slice bytes = .ok r := by
  obtain ⟨⟨first, last⟩, hsplit, _⟩ := WP.spec_imp_exists (stream.find_code_region.spec bytes)
  obtain ⟨environment, code, tail, he, hc, ht, _⟩ := stream.find_code_region.slices bytes first last hsplit
  obtain ⟨env, henv, _⟩ := WP.spec_imp_exists module.Env.new.spec
  obtain ⟨⟨r, visitor, decoded⟩, hr⟩ := stream.validate_streaming.wasm_total
    stream.SliceSource.Insts.ItascaStreamSource stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor
    0#u64 ⟨environment, code, tail⟩ ⟨none, none⟩ env
    (stream.SliceSource.callbacks_total _) StreamSync.callbacks_total
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

/-- The synchronous adapter returns precisely the environment and delivered
 tail of the actual accepted streaming run. -/
theorem stream.validate_module_slice.wasm_sound (bytes : Slice U8) (decoded : module.Module)
    (h : stream.validate_module_slice bytes = .ok (.Ok decoded)) :
    ModuleSound.Validated bytes decoded := by
  obtain ⟨⟨first, last⟩, hsplit, _⟩ := WP.spec_imp_exists (stream.find_code_region.spec bytes)
  obtain ⟨environment, code, tail, he, hc, ht, hbytes⟩ := stream.find_code_region.slices bytes first last hsplit
  obtain ⟨storage, hstorage, _⟩ := WP.spec_imp_exists module.Env.new.spec
  simp only [stream.validate_module_slice, hsplit, bind_ok, Std.uncurry] at h
  simp only [he, hc, ht, hstorage, bind_ok, Std.uncurry] at h
  obtain ⟨⟨r, visitor, env⟩, hrun, h⟩ := VisitorErasure.bind_ok_inv _ _ _ h
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
      obtain ⟨run, hvalid, _⟩ := stream.validate_streaming.wasm_sound
        stream.SliceSource.Insts.ItascaStreamSource stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor
        StreamSync.Tracks StreamSync.provenance 0#u64 ⟨environment, code, tail⟩ ⟨none, none⟩ visitor
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

/-- Arbitrary inputs return normally; every accepted result has the complete
independent module certificate and exact returned metadata. -/
theorem stream.validate_module_slice.wasm_spec (bytes : Slice U8) :
    stream.validate_module_slice bytes ⦃ r => match r with
      | .Ok decoded => ModuleSound.Validated bytes decoded
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr⟩ := stream.validate_module_slice.wasm_total bytes
  rw [hr]
  simp only [WP.spec_ok]
  cases r with
  | Err _ => trivial
  | Ok decoded => exact stream.validate_module_slice.wasm_sound bytes decoded hr

end Itasca
