import Exec.Theorems.Host.Open.Driver.HostEffects
import Exec.Theorems.Host.Open.Driver.ReentrantHistory
import Exec.Theorems.Host.Open.Driver.StackTraces
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std

/-- A finite host-local prefix uses actual ticks and independently excludes
nested invocation at each selected instruction. It permits arbitrary loops. -/
inductive LocalPrefix {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector) :
    Nat → State M → State M → Prop
  | nil (state) : LocalPrefix memory floats allocator select 0 state state
  | next {count state next last} (host : HostState) (mode : state.mode=.host host)
      (onlyLocal : ∀instruction,host.code[host.pc]?=some instruction → Local instruction)
      (actual : tick memory floats allocator select state=.ok (.cont next))
      (tail : LocalPrefix memory floats allocator select count next last) :
      LocalPrefix memory floats allocator select (count+1) state last

theorem LocalPrefix.trace {M F A : Type} {memory : runtime.platform.MemoryBuffer M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A} {select : Selector}
    {count : Nat} {first last : State M} (trace : LocalPrefix memory floats allocator select count first last) :
    Interp.ContinuingTrace (tick memory floats allocator select) count first last := by
  induction trace with
  | nil state => exact .nil _
  | next host mode onlyLocal actual tail ih => exact .next actual ih

/-- Every actual local prefix retains its source-typed store and accumulated
committed effects, even when the remaining host computation diverges. -/
theorem local_prefix_effect {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    {count : Nat} {first last : State M} (trace : LocalPrefix memory floats allocator select count first last)
    (code : Store.CodeInterpretation) (held : ExecutableInv view code first.store) :
    ∃afterCode,Effect view code first.store afterCode last.store ∧ last.stack=first.stack ∧ last.history=first.history := by
  induction trace generalizing code with
  | nil state => exact ⟨code,.refl held,rfl,rfl⟩
  | @next count state next last host mode onlyLocal actual tail ih =>
    have post := host_local_effect memory floats allocator correct allocation view laws code select state held host mode onlyLocal
    rw [actual,WP.spec_ok] at post
    obtain ⟨checked,middleCode,same,effect,stack,history,kind⟩ := post
    cases same
    obtain ⟨afterCode,more,stackMore,historyMore⟩ := ih middleCode effect.invariant
    exact ⟨afterCode,effect.trans more,stackMore.trans stack,historyMore.trans history⟩
end Exec.Theorems.OpenReentrantControl
