import Exec.Store.Preparation.Staging

namespace Exec.Store
open Aeneas Aeneas.Std

@[step] theorem copy_bytes_loop (source : Slice U8) (bytes : alloc.vec.Vec U8)
    (i : Usize) (hi : i.val ≤ source.length) (hprefix : bytes.val = source.val.take i.val) :
    runtime.store.copy_bytes_loop source bytes i ⦃ after => after.val = source.val ⦄ := by
  unfold runtime.store.copy_bytes_loop
  apply loop.spec_decr_nat (fun pair => source.length - pair.2.val)
    (fun pair => pair.2.val ≤ source.length ∧ pair.1.val = source.val.take pair.2.val)
  · intro pair hinv
    rcases pair with ⟨bytes, i⟩
    rcases hinv with ⟨hi, hbytes⟩
    unfold runtime.store.copy_bytes_loop.body
    dsimp only at hi hbytes ⊢
    split
    · rename_i hmore
      have hib : i.val < source.length := by scalar_tac
      have hlen : bytes.length = i.val := by simp [hbytes, Nat.min_eq_left hi]
      have hmax : bytes.length < Usize.max := by scalar_tac
      step as ⟨value, hvalue⟩
      step as ⟨after, hafter⟩
      step as ⟨next, hnext⟩
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hafter, hbytes, hnext, List.take_succ_eq_append_getElem hib, hvalue]
    · rename_i hstop
      have heq : i.val = source.length := by scalar_tac
      simpa [heq] using hbytes
  · exact ⟨hi, hprefix⟩

@[step] theorem copy_bytes_spec {A : Type} (allocator : runtime.platform.Alloc A)
    (ha : Platform.AllocCorrect allocator) (source : Slice U8) :
    runtime.store.copy_bytes allocator source ⦃ answer =>
      answer = .Err (.Exhausted .Allocation) ∨ ∃ bytes, answer = .Ok bytes ∧ bytes.val = source.val ⦄ := by
  unfold runtime.store.copy_bytes
  dsimp only
  obtain ⟨reserved, hr⟩ := reserve_wrapper_eq allocator ha (alloc.vec.Vec.new U8) (Slice.len source)
  rw [hr]
  cases reserved
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · simp [core.result.Result.Insts.CoreOpsTry.branch]
    step with copy_bytes_loop source (alloc.vec.Vec.new U8) 0#usize (by scalar_tac) (by simp) as ⟨bytes, hbytes⟩
    simp [hbytes]

/-- A data segment is copied byte for byte and receives its current store index.
Failures do not change the store; success changes only that data vector and the
selected provisional instance's data-address map. -/
theorem add_instance_data_effect {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (s : runtime.store.Store M) (instanceIndex i : Usize)
    (hinstance : instanceIndex.val < s.instances.length)
    (hi : i.val < (s.instances.val[instanceIndex.val]).module.module.tail.data.length)
    (hroom : s.datas.length < Usize.max)
    (hmaproom : (s.instances.val[instanceIndex.val]).data.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_data ops allocator s instanceIndex i ⦃ result =>
      (∃ error, result = (.Err error, s)) ∨
      ∃ bytes : alloc.vec.Vec U8, ∃ datas : alloc.vec.Vec runtime.store.DataInstance,
      ∃ addresses : alloc.vec.Vec Usize,
        bytes.val = (s.instances.val[instanceIndex.val]).module.module.tail.data.val[i.val].init.val ∧
        datas.val = s.datas.val ++ [⟨bytes⟩] ∧
        addresses.val = (s.instances.val[instanceIndex.val]).data.val ++ [alloc.vec.Vec.len s.datas] ∧
        result = (.Ok (), {s with datas := datas, instances := s.instances.set instanceIndex {(s.instances.val[instanceIndex.val]) with data := addresses}}) ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_data
  step as ⟨inst, hinst⟩
  simp only [runtime.compiler.ExecutableModule.tail, module.Module.tail,
    Itasca.module.Module.impl.tail, bind_ok]
  have hd : i.val < inst.module.module.tail.data.length := by simpa [hinst] using hi
  step as ⟨data, hdata⟩
  step with copy_bytes_spec allocator ha data.init.deref as ⟨copied, hcopied⟩
  rcases hcopied with herr | ⟨bytes, hok, hbytes⟩
  · simp [herr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · rw [hok]
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    obtain ⟨reserved, hr⟩ := reserve_wrapper_eq allocator ha s.datas 1#usize
    rw [hr]
    cases reserved
    · simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    · simp [core.result.Result.Insts.CoreOpsTry.branch]
      step as ⟨datas, hdatas⟩
      step as ⟨inst', back, hinst', hback⟩
      have hm : inst'.data.length < Usize.max := by simpa [hinst'] using hmaproom
      step as ⟨addresses, haddresses⟩
      right
      refine ⟨bytes, ?_, datas, hdatas, addresses, ?_, ?_⟩
      · simpa [hdata, hinst, alloc.vec.Vec.deref] using hbytes
      · simpa [hinst'] using haddresses
      · simp [hback, hinst']

/-- Updating a newly staged instance cannot alter an earlier instance's map.
The copied bytes and appended data address likewise retain every old prefix. -/
theorem add_instance_data_staged {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (before s : runtime.store.Store M) (hprefix : StagedPrefix before s)
    (instanceIndex i : Usize) (hfresh : before.instances.length ≤ instanceIndex.val)
    (hinstance : instanceIndex.val < s.instances.length)
    (hi : i.val < (s.instances.val[instanceIndex.val]).module.module.tail.data.length)
    (hroom : s.datas.length < Usize.max)
    (hmaproom : (s.instances.val[instanceIndex.val]).data.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_data ops allocator s instanceIndex i
      ⦃ _ after => StagedPrefix before after ⦄ := by
  apply WP.spec_mono (add_instance_data_effect ops allocator ha s instanceIndex i hinstance hi hroom hmaproom)
  intro result heffect
  rcases heffect with ⟨error, herr⟩ | ⟨bytes, datas, addresses, hbytes, hdatas, haddresses, hresult⟩
  · simpa [herr] using hprefix
  · rw [hresult]
    constructor
    · exact hprefix.identity
    · exact hprefix.limits
    · exact hprefix.funcs
    · exact hprefix.types
    · exact hprefix.tables
    · exact hprefix.memories
    · exact hprefix.globals
    · simpa [alloc.vec.Vec.set_val_eq, List.take_set_of_le hfresh] using hprefix.instances
    · exact hprefix.elems
    · have hlen : before.datas.length ≤ s.datas.length := by
        have h := congrArg List.length hprefix.datas
        simp only [List.length_take] at h
        change Nat.min before.datas.length s.datas.length = before.datas.length at h
        exact h ▸ Nat.min_le_right _ _
      simpa only [hdatas, List.take_append_of_le_length hlen] using hprefix.datas
    · exact hprefix.externs
    · exact hprefix.instanceItems

end Exec.Store
