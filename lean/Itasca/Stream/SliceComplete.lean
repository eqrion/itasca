import Itasca.Stream.SliceSound
import Itasca.Stream.DriverComplete
import Itasca.Stream.SyncComplete

/-!
# Contiguous adapter completeness

`stream.validate_module_slice.profile_complete_with_metadata`: every independently encoded,
elaborated and typed module within the selected profile and implementation limits is accepted by
`stream.validate_module_slice`, and the returned environment and tail match the raw module and its
public accessor types. The slice source (`stream.SliceSource.available`) and synchronous scheduler
(`StreamSync.accepts`) discharge the source availability and accepting scheduler premises of the
streaming driver. The `wasm_` theorems are the Wasm 1.0 instances.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary ModuleElaboration

/-- `stream.validate_module_slice` accepts every independently encoded, elaborated, typed module
in the selected profile within the implementation limits. Its slice source and synchronous
scheduler discharge all embedding premises. The returned environment and tail match the raw
module and its public accessor types. -/
theorem stream.validate_module_slice.profile_complete_with_metadata
    (data : Slice U8) (raw : ModuleBinary.Module) (profile : ValidationProfile)
    (hb : ModuleEncodingWithinLimits raw data.val profile)
    (hsignatures : ModuleSignaturesWithinLimits raw profile)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Profile raw profile) :
    ∃ decoded, stream.validate_module_slice data profile = .ok (.Ok decoded) ∧
      Matches decoded.env decoded.tail raw ∧ AccessorTypes decoded.env raw := by
  obtain ⟨⟨first, last⟩, hsplit, _⟩ := WP.spec_imp_exists (stream.find_code_region.spec data)
  obtain ⟨environment, code, tail, henvironment, hcode, htail, _⟩ :=
    stream.find_code_region.slices data first last hsplit
  let regions : stream.SliceSource := ⟨environment, code, tail⟩
  have hcanonical : StreamSource.CanonicalAvailable stream.SliceSource.Insts.ItascaStreamSource
      regions data :=
    ⟨regions, ⟨first, last, hsplit, henvironment, hcode, htail⟩, stream.SliceSource.available regions⟩
  obtain ⟨storage, hstorage, _⟩ := WP.spec_imp_exists module.Env.new.spec
  obtain ⟨env, after, run, hrun, hmatches, hmetadata, _⟩ := stream.validate_streaming.profile_complete
    stream.SliceSource.Insts.ItascaStreamSource stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor
    { batch_bytes := 25000#usize, max_batches := 1#usize } StreamSync.Queued StreamSync.accepts
    0#u64 regions ⟨none, none⟩ storage data raw hb hsignatures he ht hp hcanonical rfl
  refine ⟨⟨env, run.remaining.tail⟩, ?_, hmatches, hmetadata⟩
  have hstored := StreamSync.delivered_tail run.remaining
  unfold stream.validate_module_slice
  simp only [hsplit, bind_ok, Std.uncurry]
  simp only [henvironment, hcode, htail, hstorage, bind_ok]
  dsimp only [regions] at hrun
  simp [hrun, hstored, core.result.Result.Insts.CoreOpsTry.branch]

/-- `stream.validate_module_slice.profile_complete_with_metadata` without the accessor types. -/
theorem stream.validate_module_slice.profile_complete
    (data : Slice U8) (raw : ModuleBinary.Module) (profile : ValidationProfile)
    (hb : ModuleEncodingWithinLimits raw data.val profile)
    (hsignatures : ModuleSignaturesWithinLimits raw profile)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Profile raw profile) :
    ∃ decoded, stream.validate_module_slice data profile = .ok (.Ok decoded) ∧
      Matches decoded.env decoded.tail raw := by
  obtain ⟨decoded, hr, hm, _⟩ := stream.validate_module_slice.profile_complete_with_metadata data raw profile hb hsignatures he ht hp
  exact ⟨decoded, hr, hm⟩

/-- The Wasm 1.0 instance of `stream.validate_module_slice.profile_complete_with_metadata`. -/
theorem stream.validate_module_slice.wasm_complete_with_metadata
    (data : Slice U8) (raw : ModuleBinary.Module)
    (hb : ModuleEncodingWithinLimits raw data.val)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Profile raw) :
    ∃ decoded, stream.validate_module_slice data .Wasm1 = .ok (.Ok decoded) ∧
      Matches decoded.env decoded.tail raw ∧ AccessorTypes decoded.env raw :=
  stream.validate_module_slice.profile_complete_with_metadata data raw .Wasm1 hb
    (fun _ _ => trivial) he ht hp

/-- The Wasm 1.0 instance of `stream.validate_module_slice.profile_complete`. -/
theorem stream.validate_module_slice.wasm_complete
    (data : Slice U8) (raw : ModuleBinary.Module)
    (hb : ModuleEncodingWithinLimits raw data.val)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Profile raw) :
    ∃ decoded, stream.validate_module_slice data .Wasm1 = .ok (.Ok decoded) ∧
      Matches decoded.env decoded.tail raw :=
  stream.validate_module_slice.profile_complete data raw .Wasm1 hb (fun _ _ => trivial) he ht hp

end Itasca
