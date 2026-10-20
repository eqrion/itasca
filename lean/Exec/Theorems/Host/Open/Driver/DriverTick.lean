import Exec.Theorems.Host.Open.Driver.DriverGuard
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

private theorem prepare_loop_stopped {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (status : Status)
    (stopped : ¬(0<exec.frames.length ∧ status=.Ok ())) :
    prepareLoop memory (inert memory) floats allocator (exec,store,(),status)=.ok (.finished (finishExecution (exec,store,(),status))) := by
  unfold prepareLoop
  dsimp only
  split
  · rename_i active
    have positive : 0<exec.frames.length := by scalar_tac
    cases status with
    | Ok unit => cases unit; exact False.elim (stopped ⟨positive,rfl⟩)
    | Err error => simp [core.result.Result.is_ok,bind_ok]
  · rfl

/-- Every guarded combined tick returns normally and preserves the full store
and continuation invariant. Reentrant host control itself may run forever. -/
theorem tick_guard {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (code : Store.CodeInterpretation) (state : State M) (guard : StateGuard memory view code state) :
    tick memory floats allocator select state ⦃out=>GuardedOutput memory view code state.store out⦄ := by
  obtain ⟨held,modeGuard,stackGuard⟩ := guard
  cases modeEq : state.mode with
  | host host =>
    by_cases nested : ∃index values next,host.code[host.pc]?=some (.invoke index values next)
    · obtain ⟨index,values,next,selected⟩ := nested
      by_cases inside : index.val<state.store.funcs.length
      · apply WP.spec_mono (host_invoke_task memory floats allocator allocation view code select state held host modeEq index values next selected inside)
        rintro out ⟨phase,ready,rfl⟩
        exact ⟨code,.refl held,held,ready,stackGuard⟩
      · simp only [tick,modeEq,selected,if_neg inside]
        exact WP.spec.ret ⟨code,.refl held,held,(by simp [ModeGuard]),stackGuard⟩
    · have onlyLocal : ∀instruction,host.code[host.pc]?=some instruction → Local instruction := by
        intro instruction selected
        cases instruction <;> try trivial
        rename_i index values next
        exact False.elim (nested ⟨index,values,next,selected⟩)
      apply WP.spec_mono (host_local_effect memory floats allocator correct allocation view laws code select state held host modeEq onlyLocal)
      rintro out ⟨next,afterCode,rfl,effect,stack,history,kind⟩
      refine ⟨afterCode,effect,effect.invariant,?_,?_⟩
      · rcases kind with ⟨hostNext,mode,identity,args⟩ | ⟨status,values,mode,issued⟩
        · rw [mode]; trivial
        · rw [mode]; exact issued
      · rw [stack]; exact stackGuard.extend effect
  | preparing phase =>
    rw [modeEq] at modeGuard
    cases phase with
    | done answer =>
      obtain ⟨same,error,status⟩ := modeGuard
      simp only [tick,modeEq]
      refine WP.spec.ret ⟨code,?_,?_,?_,?_⟩
      · rw [same]; exact .refl held
      · rw [same]; exact held
      · exact ⟨rfl,by intro impossible; rw [status] at impossible; cases impossible⟩
      · simpa only [same] using stackGuard
    | waiting phase root results =>
      obtain ⟨signature,ready⟩ := modeGuard
      simp only [tick,modeEq,WP.spec_ok,GuardedOutput]
      exact acceptCall_guard memory view code select state held stackGuard phase root signature results ready
  | wasm exec status root results =>
    rw [modeEq] at modeGuard
    obtain ⟨signature,task⟩ := modeGuard
    by_cases active : 0<exec.frames.length ∧ status=.Ok ()
    · obtain ⟨positive,rfl⟩ := active
      have positiveRaw : exec.frames.len>0#usize := by scalar_tac
      obtain ⟨phase,actual,ready⟩ := WP.spec_imp_exists (task.prepare memory floats allocator correct allocation view laws held positive)
      simp only [tick,modeEq,prepareLoop,if_pos positiveRaw,core.result.Result.is_ok,bind_ok]
      rw [actual,bind_ok]
      simp only [ite_true,bind_ok,WP.spec_ok,GuardedOutput]
      exact (acceptCall_guard memory view code select state held stackGuard phase root signature results ready)
    · have stopped := prepare_loop_stopped memory floats allocator exec state.store status active
      obtain ⟨answer,actual,execEq,storeEq,tokenEq,issued⟩ := WP.spec_imp_exists (task.readback memory allocator allocation results active)
      simp only [tick,modeEq,stopped,bind_ok]
      rw [actual,bind_ok]
      refine WP.spec.ret ⟨code,?_,?_,⟨rfl,?_⟩,?_⟩
      · rw [storeEq]; exact .refl held
      · rw [storeEq]; exact held
      · simpa only [storeEq] using issued
      · simpa only [storeEq] using stackGuard
  | hostReturn status values =>
    rw [modeEq] at modeGuard
    cases stackEq : state.stack with
    | nil =>
      simp only [tick,modeEq,stackEq]
      exact WP.spec.ret ⟨code,.refl held,held,modeGuard⟩
    | cons frame tail =>
      cases frame with
      | host host next =>
        simp only [tick,modeEq,stackEq]
        exact WP.spec.ret ⟨code,.refl held,held,by simp⟩
      | wasm exec address base root results =>
        rw [stackEq] at stackGuard
        obtain ⟨⟨signature,saved⟩,rest⟩ := stackGuard
        obtain ⟨⟨result,finished⟩,actual,task⟩ := WP.spec_imp_exists (saved code state.store (.refl held) status values modeGuard)
        simp only [tick,modeEq,stackEq,actual,bind_ok]
        exact WP.spec.ret ⟨code,.refl held,held,⟨signature,task⟩,rest⟩
  | invokeReturn answer =>
    rw [modeEq] at modeGuard
    obtain ⟨same,issued⟩ := modeGuard
    cases stackEq : state.stack with
    | nil =>
      simp only [tick,modeEq,stackEq]
      refine WP.spec.ret ⟨code,?_,?_,?_⟩
      · rw [Outcome.store,same]; exact .refl held
      · rw [Outcome.store,same]; exact held
      · simpa only [Outcome.store,same] using issued
    | cons frame tail =>
      cases frame with
      | host host next =>
        rw [stackEq] at stackGuard
        simp only [tick,modeEq,stackEq]
        cases status : answer.1 with
        | Ok unit => cases unit; exact WP.spec.ret ⟨code,.refl held,held,trivial,stackGuard⟩
        | Err error => exact WP.spec.ret ⟨code,.refl held,held,(by simp [ModeGuard]),stackGuard⟩
      | wasm exec address base root results =>
        simp only [tick,modeEq,stackEq]
        exact WP.spec.ret ⟨code,.refl held,held,by simp⟩
end Exec.Theorems.OpenReentrantControl
