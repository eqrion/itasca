import Exec.Theorems.Host.Callbacks.GrowthCallbacks
import Exec.Theorems.Host.Callbacks.AllocationCallbacks

/-! Finite callback composition with a restricted operation vocabulary. Programs
cannot inspect raw stores or carry memory borrows across operations. Each leaf
has independent checked API semantics; sequencing retains effects on rejection. -/
namespace Exec.Theorems.CallbackActions
open Aeneas Aeneas.Std

inductive Program where
  | read (segment : ReadCallbacks.Program)
  | growth (segment : GrowthCallbacks.Program)
  | allocation (segment : AllocationCallbacks.Program)
  | sequence (first next : Program)
  | branch (condition : Bool) (yes no : Program)

abbrev Reply (M : Type) := StoreCallbacks.Reply M
abbrev Effect := @OpenHostControl.Effect

def Program.run {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) : Program → runtime.store.Store M → Result (Reply M)
  | .read segment,store => segment.run memory allocator store
  | .growth segment,store => segment.run memory allocator store
  | .allocation segment,store => segment.run memory allocator store
  | .branch condition yes no,store => if condition then yes.run memory allocator store else no.run memory allocator store
  | .sequence first next,store => do
    let answer ← first.run memory allocator store
    match answer.1 with
    | .Ok () => next.run memory allocator answer.2.1
    | .Err error => .ok (.Err error,answer.2.1,answer.2.2)

/-- Permissions and source effects are inherited from the independently
specified checked operations. A rejected sequence retains the rejecting action's
store and results and executes no continuation. -/
inductive Returns {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation) :
    Program → runtime.store.Store M → core.result.Result Unit runtime.platform.HostError →
      runtime.store.Store M → List runtime.Value → Prop
  | read {segment before status after values}
      (effect : ReadCallbacks.Returns segment before status after values) :
      Returns view code (.read segment) before status after values
  | growth {segment before status after values}
      (effect : GrowthCallbacks.Returns view code segment before status after values) :
      Returns view code (.growth segment) before status after values
  | allocation {segment before status after values}
      (effect : AllocationCallbacks.Returns segment before status after values) :
      Returns view code (.allocation segment) before status after values
  | sequence {first next before middle status after values ignored}
      (head : Returns view code first before (.Ok ()) middle ignored)
      (tail : Returns view code next middle status after values) :
      Returns view code (.sequence first next) before status after values
  | rejected {first next before error after values}
      (head : Returns view code first before (.Err error) after values) :
      Returns view code (.sequence first next) before (.Err error) after values
  | yes {yes no before status after values} (effect : Returns view code yes before status after values) :
      Returns view code (.branch true yes no) before status after values
  | no {yes no before status after values} (effect : Returns view code no before status after values) :
      Returns view code (.branch false yes no) before status after values

/-- Normality, action refinement, public invariant preservation and issued
results follow from the interpreter, rather than a callback-normality premise. -/
theorem Program.correct_owned {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (program : Program) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M)
    (held : ExecutableInv view code store) :
    program.run memory allocator store ⦃ answer =>
      Returns view code program store answer.1 answer.2.1 answer.2.2.val ∧
      Effect view code store answer.2.1 ∧
      ∀ value ∈ answer.2.2.val,Store.ValueInStore answer.2.1 value ⦄ := by
  induction program generalizing store with
  | read segment =>
    exact WP.spec_mono (segment.correct_owned memory allocator allocation view code store held)
      (fun _ post => ⟨.read post.1,post.2⟩)
  | growth segment =>
    exact WP.spec_mono (segment.correct_owned memory allocator allocation view laws code store held)
      (fun _ post => ⟨.growth post.1,post.2⟩)
  | allocation segment =>
    apply WP.spec_mono (segment.correct_owned memory allocator allocation view code store held)
    rintro answer ⟨source,fresh,metadata,extension,externs,issued⟩
    exact ⟨.allocation source,⟨fresh,metadata,extension,externs⟩,issued⟩
  | branch condition yes no hy hn =>
    cases condition with
    | true => exact WP.spec_mono (hy store held) (fun _ post => ⟨.yes post.1,post.2⟩)
    | false => exact WP.spec_mono (hn store held) (fun _ post => ⟨.no post.1,post.2⟩)
  | sequence first next hf hn =>
    obtain ⟨⟨status,after,values⟩,actual,source,effect,issued⟩ := WP.spec_imp_exists (hf store held)
    unfold Program.run
    rw [actual,bind_ok]
    cases status with
    | Ok unit =>
      cases unit
      exact WP.spec_mono (hn after effect.invariant)
        (fun _ post => ⟨.sequence source post.1,effect.trans post.2.1,post.2.2⟩)
    | Err error => exact WP.spec.ret ⟨.rejected source,effect,issued⟩

/-- The issued-result contract follows from the stronger owned-result package. -/
theorem Program.correct {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (program : Program) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M)
    (held : ExecutableInv view code store) :
    program.run memory allocator store ⦃ answer =>
      Returns view code program store answer.1 answer.2.1 answer.2.2.val ∧
      Effect view code store answer.2.1 ∧
      ∀ value ∈ answer.2.2.val,Store.IssuedValue answer.2.1 value ⦄ := by
  apply WP.spec_mono (program.correct_owned memory allocator allocation view laws code store held)
  rintro answer ⟨source,effect,owned⟩
  exact ⟨source,effect,fun value member=>(owned value member).issued⟩

def platform {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (select : U64 → Slice runtime.Value → Program) :
    runtime.platform.Platform Unit M where
  MemoryBufferInst := memory
  interrupt token := .ok (.Continue,token)
  call_host token store identity args _ := do
    let answer ← (select identity args).run memory allocator store
    .ok (answer.1,token,answer.2.1,answer.2.2)

theorem callback_package {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (select : U64 → Slice runtime.Value → Program) (view : M → Slice U8)
    (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (token : Unit) (identity : U64) (args results : Slice runtime.Value) :
    (platform memory allocator select).call_host token store identity args results ⦃ answer =>
      Effect view code store answer.2.2.1 ∧
      ∀ value ∈ answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value ⦄ := by
  unfold platform
  step with (select identity args).correct memory allocator allocation view laws code store held
    as ⟨answer,_,effect,issued⟩
  exact ⟨effect,issued⟩

end Exec.Theorems.CallbackActions
