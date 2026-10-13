import Itasca.Support.Result
import Itasca.Module.Custom.Visitor
import Itasca.Stream.SliceSound
import Itasca.Stream.DriverRegions

/-!
# Contiguous adapter rejection

Shows that errors of the default environment parser and of the code header reader reach the caller
of `module.validate_module` unchanged. `StreamSliceRejection.environment_error` covers an
environment rejection when the splitter places the whole input in the environment region, and
`StreamSliceRejection.code_header_error` covers a code header rejection after the environment
region was accepted. Both are for Wasm 1.0.
-/

open Aeneas Aeneas.Std

namespace Itasca.StreamSliceRejection

/-- A custom-section hook that leaves the state unchanged and succeeds does not change the result
of the environment loop, including its error constructor. -/
theorem environment_loop_noop {V : Type} (visitor : module.ModuleVisitor V)
    (hnoop : ∀ (v : V) (chunk : types.CustomSection),
      visitor.on_custom_section v chunk = .ok (.Ok (), v))
    (data : Slice U8) (v : V) (env : module.Env) (pos : Usize) (lastId : U8)
    (result : core.result.Result (module.Env × Usize) error.Error)
    (h : module.validate_env_with_loop
      module.EmptyModuleVisitor.Insts.ItascaModuleModuleVisitor data .Wasm1 () env pos lastId =
      .ok (result, ())) :
    module.validate_env_with_loop visitor data .Wasm1 v env pos lastId = .ok (result, v) := by
  generalize hn : data.length - pos.val = n
  induction n using Nat.strong_induction_on generalizing env pos lastId with
  | h n ih =>
    unfold module.validate_env_with_loop at h ⊢
    rw [loop] at h ⊢
    simp only [module.validate_env_with_loop.body] at h ⊢
    by_cases hstop : pos ≥ Slice.len data
    · simpa [hstop] using h
    · simp only [hstop, ↓reduceIte] at h ⊢
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (module.read_section_header.spec data pos)
      rw [hr] at h ⊢
      cases r with
      | Err e =>
        simpa [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using h
      | Ok triple =>
        obtain ⟨id, first, last⟩ := triple
        have hspan := hp.span
        have hmeasure : data.length - last.val < n := by scalar_tac
        simp [core.result.Result.Insts.CoreOpsTry.branch] at h ⊢
        by_cases hcustom : id = module.SECTION_CUSTOM
        · simp only [hcustom, ↓reduceIte] at h ⊢
          obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (module.decode_custom_section.spec data first last)
          rw [hr] at h ⊢
          cases r with
          | Err e =>
            simpa [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using h
          | Ok chunk =>
            simp only [bind_ok, module.ModuleVisitor.on_custom_section.default] at h
            simp only [bind_ok, hnoop]
            have hi := ih (data.length - last.val) hmeasure env last lastId
              (by simpa [module.validate_env_with_loop, module.validate_env_with_loop.body,
                module.ModuleVisitor.on_custom_section.default,
                core.result.Result.Insts.CoreOpsTry.branch] using h) rfl
            simpa [module.validate_env_with_loop, module.validate_env_with_loop.body,
              core.result.Result.Insts.CoreOpsTry.branch, hnoop] using hi
        · simp only [hcustom, ↓reduceIte] at h ⊢
          by_cases hcode : id = module.SECTION_CODE
          · simpa [hcode] using h
          · simp only [hcode, ↓reduceIte] at h ⊢
            by_cases hdata : id = module.SECTION_DATA
            · simpa [hdata] using h
            · simp only [hdata, ↓reduceIte] at h ⊢
              obtain ⟨ordered, hord, _⟩ := WP.spec_imp_exists (module.section_order.spec id)
              rw [hord] at h ⊢
              cases ordered with
              | Err e =>
                simpa [core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using h
              | Ok rank =>
                simp only [bind_ok] at h ⊢
                by_cases horder : rank.val ≤ lastId.val
                · simpa [horder] using h
                · simp only [horder, ↓reduceIte, Std.bind_assoc] at h ⊢
                  obtain ⟨⟨read, updated⟩, hr, ht⟩ := ResultFacts.bind_ok_inv _ _ _ h
                  rw [hr]
                  simp only [bind_ok]
                  cases read with
                  | Err e =>
                    simpa [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using ht
                  | Ok consumed =>
                    simp at ht ⊢
                    by_cases he : consumed = last
                    · simp only [he, ↓reduceIte] at ht ⊢
                      have hi := ih (data.length - last.val) hmeasure updated last rank
                        (by simpa [module.validate_env_with_loop, module.validate_env_with_loop.body,
                          core.result.Result.Insts.CoreOpsTry.branch] using ht) rfl
                      simpa [module.validate_env_with_loop, module.validate_env_with_loop.body,
                        core.result.Result.Insts.CoreOpsTry.branch] using hi
                    · have hne : consumed.val ≠ last.val := fun h => he (UScalar.eq_of_val_eq h)
                      simpa [hne] using ht

/-- `module.validate_env_with` with a no-op custom-section hook returns the same result as
`module.validate_env`. -/
theorem environment_noop {V : Type} (visitor : module.ModuleVisitor V)
    (hnoop : ∀ (v : V) (chunk : types.CustomSection),
      visitor.on_custom_section v chunk = .ok (.Ok (), v))
    (data : Slice U8) (v : V)
    (result : core.result.Result (module.Env × Usize) error.Error)
    (h : module.validate_env data .Wasm1 = .ok result) :
    module.validate_env_with visitor data .Wasm1 v = .ok (result, v) := by
  unfold module.validate_env at h
  obtain ⟨⟨read, w⟩, hr, ht⟩ := ResultFacts.bind_ok_inv _ _ _ h
  have ht : read = result := by simpa using ht
  subst read
  cases w
  unfold module.validate_env_with at hr ⊢
  obtain ⟨initial, hi, ht⟩ := ResultFacts.bind_ok_inv _ _ _ hr
  rw [hi]
  simp only [bind_ok]
  obtain ⟨read, hr, ht⟩ := ResultFacts.bind_ok_inv _ _ _ ht
  rw [hr]
  simp only [bind_ok]
  cases read with
  | Err e =>
    simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using ht
  | Ok start =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at ht ⊢
    exact environment_loop_noop visitor hnoop data v initial start 0#u8 result ht

/-- A rejection by the default environment parser is returned unchanged by
`module.validate_module` when the splitter places the entire input in the environment region. -/
theorem environment_error (data : Slice U8) (e : error.Error)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (hsplit : stream.find_code_region data = .ok (Slice.len data, Slice.len data))
    (herror : module.validate_env data .Wasm1 = .ok (.Err e)) :
    module.validate_module data .Wasm1 = .ok (.Err e) := by
  obtain ⟨environment, code, tail, he, hc, ht, _⟩ :=
    stream.find_code_region.slices data (Slice.len data) (Slice.len data) hsplit
  have hwhole : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      data ⟨0#usize, Slice.len data⟩ = .ok data := by
    simp [Slice.index_SliceIndexRangeUsizeSliceInst,
      core.slice.index.SliceIndexRangeUsizeSlice.index]
  have heq : environment = data := by simpa [hwhole] using he.symm
  subst environment
  have htail : tail = code := by simpa [hc] using ht.symm
  subst tail
  obtain ⟨storage, hstorage, _⟩ := WP.spec_imp_exists module.Env.new.spec
  obtain ⟨total, hadd, htotal⟩ := limits.add_offset.complete 0#usize (Slice.len data) (by simpa using hsize)
  have htotal : total = Slice.len data := by apply UScalar.eq_of_val_eq; simpa using htotal
  subst total
  have hparse := environment_noop stream.SyncVisitor.Insts.ItascaModuleModuleVisitor
    (fun _ _ => rfl) data (⟨none, none⟩ : stream.SyncVisitor) (.Err e) herror
  have hrun : stream.validate_streaming stream.SliceSource.Insts.ItascaStreamSource
      stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor 0#u64 .Wasm1
      ⟨data, code, code⟩ ⟨none, none⟩ storage = .ok (.Err e, ⟨none, none⟩, storage) := by
    simp [stream.validate_streaming, stream.SliceSource.Insts.ItascaStreamSource.environment,
      stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor.custom_region, hadd, hparse,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  unfold module.validate_module stream.validate_module_slice
  simp only [hsplit, bind_ok, Std.uncurry]
  simp only [he, hc, hstorage, bind_ok]
  simp [hrun, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- A rejection by `stream.read_code_header` is returned unchanged by `module.validate_module`
after the default environment parser has accepted the whole environment region. -/
theorem code_header_error (data : Slice U8) (regions : stream.SliceSource)
    (env : module.Env) (e : error.Error)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (hsplit : StreamCompleteRegions.Split data regions)
    (henv : module.validate_env regions.env .Wasm1 = .ok (.Ok (env, Slice.len regions.env)))
    (herror : stream.read_code_header stream.SliceSource.Insts.ItascaStreamSource
      regions (Slice.len regions.code) env = .ok (.Err e)) :
    module.validate_module data .Wasm1 = .ok (.Err e) := by
  obtain ⟨first, last, hsplit, he, hc, ht⟩ := hsplit
  obtain ⟨environment, code, tail, he', hc', ht', hbytes⟩ :=
    stream.find_code_region.slices data first last hsplit
  have heq : environment = regions.env := by simpa [he] using he'.symm
  have hcq : code = regions.code := by simpa [hc] using hc'.symm
  have htq : tail = regions.tail := by simpa [ht] using ht'.symm
  rw [heq, hcq, htq] at hbytes
  have hlen := congrArg List.length hbytes
  simp only [List.length_append] at hlen
  obtain ⟨envLen, henvadd, henvLen⟩ := limits.add_offset.complete 0#usize (Slice.len regions.env)
    (by change 0 + regions.env.val.length ≤ _; change data.val.length ≤ _ at hsize; omega)
  have henvLen : envLen = Slice.len regions.env := by apply UScalar.eq_of_val_eq; simpa using henvLen
  subst envLen
  obtain ⟨codeEnd, hcodeadd, _⟩ := limits.add_offset.complete (Slice.len regions.env) (Slice.len regions.code)
    (by change regions.env.val.length + regions.code.val.length ≤ _; change data.val.length ≤ _ at hsize; omega)
  obtain ⟨storage, hstorage, _⟩ := WP.spec_imp_exists module.Env.new.spec
  have hparse := environment_noop stream.SyncVisitor.Insts.ItascaModuleModuleVisitor
    (fun _ _ => rfl) regions.env (⟨none, none⟩ : stream.SyncVisitor)
    (.Ok (env, Slice.len regions.env)) henv
  have hremaining : stream.validate_remaining stream.SliceSource.Insts.ItascaStreamSource
      stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor 0#u64 .Wasm1 regions env (Slice.len regions.env)
      ⟨none, none⟩ = .ok (.Err e, ⟨none, none⟩) := by
    simp [stream.validate_remaining, stream.SliceSource.Insts.ItascaStreamSource.code_len,
      hcodeadd, herror, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  have hrun : stream.validate_streaming stream.SliceSource.Insts.ItascaStreamSource
      stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor 0#u64 .Wasm1 regions ⟨none, none⟩ storage =
      .ok (.Err e, ⟨none, none⟩, env) := by
    simp [stream.validate_streaming, stream.SliceSource.Insts.ItascaStreamSource.environment,
      stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor.custom_region, henvadd, hparse,
      hremaining, core.result.Result.Insts.CoreOpsTry.branch]
  unfold module.validate_module stream.validate_module_slice
  simp only [hsplit, bind_ok, Std.uncurry]
  simp only [he, hc, ht, hstorage, bind_ok]
  simp [hrun, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Itasca.StreamSliceRejection
