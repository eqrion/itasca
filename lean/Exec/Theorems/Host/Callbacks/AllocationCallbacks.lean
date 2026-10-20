import Exec.Theorems.Host.Callbacks.StoreCallbackSemantics
import Exec.Theorems.Api.ExecutableInvHost
import Exec.Store.Api.DefineHostEffect

/-! Finite checked callbacks with host allocation/publication. Source effects
separate failed interning, refusal after interning, and actual publication.
Allocation failure may commit a newly interned signature before trapping. -/
namespace Exec.Theorems.AllocationCallbacks
open Aeneas Aeneas.Std

inductive DefineHostResult {M : Type} (before : runtime.store.Store M)
    (type : Itasca.types.FuncType) (identity : U64) : Bool → runtime.store.Store M → Prop
  | intern_failed {error after} (effect : Store.InternEffect before type (.Err error,after)) :
      DefineHostResult before type identity false after
  | refused {signature after} (effect : Store.InternEffect before type (.Ok signature,after)) :
      DefineHostResult before type identity false after
  | published {signature interned functions}
      (effect : Store.InternEffect before type (.Ok signature,interned))
      (room : Store.objectCount interned < interned.limits.max_objects.val)
      (appended : functions.val = interned.funcs.val ++ [⟨signature,.Host identity⟩]) :
      DefineHostResult before type identity true {interned with funcs := functions}

/-- The independent effect permits allocation refusal while keeping all effects
of completed interning, and specifies the exact host entry when publication succeeds. -/
theorem define_host_refines {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (before : runtime.store.Store M) (bound : Store.objectCount before ≤ Usize.max)
    (type : Itasca.types.FuncType) (identity : U64) :
    runtime.store.Store.define_host_with memory allocator before type identity ⦃ out =>
      match out.1 with
      | .Ok _ => DefineHostResult before type identity true out.2
      | .Err _ => DefineHostResult before type identity false out.2 ⦄ := by
  unfold runtime.store.Store.define_host_with
  step with Store.intern_type_effect memory allocator allocation before type bound as ⟨status,interned,effect⟩
  cases status with
  | Err error =>
    simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using DefineHostResult.intern_failed effect
  | Ok signature =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with Store.room_spec memory interned (effect.object_bound bound) as ⟨room,roomEq⟩
    rw [roomEq]
    by_cases space : Store.objectCount interned < interned.limits.max_objects.val
    · simp only [if_pos space,bind_ok]
      obtain ⟨answer,reserveRun⟩ := Store.reserve_wrapper_eq allocator allocation interned.funcs 1#usize
      rw [reserveRun]
      cases answer with
      | false =>
        simpa [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using DefineHostResult.refused effect
      | true =>
        simp only [↓reduceIte,bind_ok]
        have room : interned.funcs.length < Usize.max := by
          unfold Store.objectCount at space
          scalar_tac
        step as ⟨functions,appended⟩
        exact .published effect space appended
    · simpa [if_neg space,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using DefineHostResult.refused effect

inductive Program where
  | base (segment : StoreCallbacks.Program)
  | defineHost (type : Itasca.types.FuncType) (identity : U64) (next : Program)
  | branch (condition : Bool) (yes no : Program)

abbrev Reply (M : Type) := StoreCallbacks.Reply M

def Program.run {M A : Type} (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A) :
    Program → runtime.store.Store M → Result (Reply M)
  | .base segment,store => segment.run memory store
  | .branch condition yes no,store => if condition then yes.run memory allocator store else no.run memory allocator store
  | .defineHost type identity next,store => do
    let answer ← runtime.store.Store.define_host_with memory allocator store type identity
    match answer.1 with
    | .Ok _ => next.run memory allocator answer.2
    | .Err _ => .ok (.Err .Trap,answer.2,Slice.new _)

inductive Returns {M : Type} : Program → runtime.store.Store M →
    core.result.Result Unit runtime.platform.HostError → runtime.store.Store M → List runtime.Value → Prop
  | base {segment before status after values} (effect : StoreCallbacks.Returns segment before status after values) :
      Returns (.base segment) before status after values
  | published {type identity next before middle status after values}
      (effect : DefineHostResult before type identity true middle)
      (tail : Returns next middle status after values) : Returns (.defineHost type identity next) before status after values
  | refused {type identity next before after} (effect : DefineHostResult before type identity false after) :
      Returns (.defineHost type identity next) before (.Err .Trap) after []
  | yes {yes no before status after values} (source : Returns yes before status after values) :
      Returns (.branch true yes no) before status after values
  | no {yes no before status after values} (source : Returns no before status after values) :
      Returns (.branch false yes no) before status after values

/-- All returned outcomes retain the public invariant, raw prefixes, source
extension, externs, and issued results. Native allocation is an explicit law;
callback normality and returned-action decomposition are implementation conclusions. -/
theorem Program.correct_owned {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (program : Program) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store) :
    program.run memory allocator store ⦃ answer =>
      Returns program store answer.1 answer.2.1 answer.2.2.val ∧
      ExecutableInv view code answer.2.1 ∧ Interp.FrameStorePrefix store answer.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code answer.2.1) ∧
      answer.2.1.externs = store.externs ∧
      ∀ value ∈ answer.2.2.val, Store.ValueInStore answer.2.1 value ⦄ := by
  induction program generalizing store with
  | base segment =>
    obtain ⟨answer,actual,fresh,metadata,extension,externs,issued⟩ := WP.spec_imp_exists
      (segment.correct_owned memory view code store held)
    have source := segment.refines memory store
    rw [actual,WP.spec_ok] at source
    rw [Program.run,actual]
    exact WP.spec.ret ⟨.base source,fresh,metadata,extension,externs,issued⟩
  | branch condition yes no hy hn =>
    cases condition with
    | false => exact WP.spec_mono (hn store held) (fun _ post => ⟨.no post.1,post.2⟩)
    | true => exact WP.spec_mono (hy store held) (fun _ post => ⟨.yes post.1,post.2⟩)
  | defineHost type identity next ih =>
    have objectBound : Store.objectCount store ≤ Usize.max := by
      have capacity := held.shape.object_count_bound
      scalar_tac
    obtain ⟨⟨status,after⟩,actual,fresh,_,extension⟩ := WP.spec_imp_exists
      (ExecutableInv.define_host_certified memory allocator allocation view code store held type identity)
    have sourceEffect := define_host_refines memory allocator allocation store objectBound type identity
    have retained := Store.define_host_effect memory allocator allocation store objectBound type identity
    rw [actual,WP.spec_ok] at sourceEffect retained
    have metadata : Interp.FrameStorePrefix store after :=
      ⟨retained.retained.identity,retained.retained.funcs,retained.retained.types,retained.retained.instances⟩
    unfold Program.run
    rw [actual,bind_ok]
    cases status with
    | Ok address =>
      apply WP.spec_mono (ih after fresh)
      rintro answer ⟨source,valid,prefixHeld,extendsStore,externs,issued⟩
      exact ⟨.published sourceEffect source,valid,metadata.trans prefixHeld,Spec.extend_store_trans extension extendsStore,
        externs.trans retained.retained.externs,issued⟩
    | Err error =>
      exact WP.spec.ret ⟨.refused sourceEffect,fresh,metadata,extension,retained.retained.externs,by simp⟩

/-- The issued-result contract follows from the stronger owned-result package. -/
theorem Program.correct {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (program : Program) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store) :
    program.run memory allocator store ⦃ answer =>
      Returns program store answer.1 answer.2.1 answer.2.2.val ∧
      ExecutableInv view code answer.2.1 ∧ Interp.FrameStorePrefix store answer.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code answer.2.1) ∧
      answer.2.1.externs = store.externs ∧
      ∀ value ∈ answer.2.2.val, Store.IssuedValue answer.2.1 value ⦄ := by
  apply WP.spec_mono (program.correct_owned memory allocator allocation view code store held)
  rintro answer ⟨source,certified,metadata,extension,externs,owned⟩
  exact ⟨source,certified,metadata,extension,externs,fun value member=>(owned value member).issued⟩

/-- The allocation-capable selector also receives no raw-store capability. -/
def platform {M A : Type} (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (select : U64 → Slice runtime.Value → Program) : runtime.platform.Platform Unit M where
  MemoryBufferInst := memory
  interrupt token := .ok (.Continue,token)
  call_host token store identity args _ := do
    let answer ← (select identity args).run memory allocator store
    .ok (answer.1,token,answer.2.1,answer.2.2)

theorem sound {M A : Type} (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (select : U64 → Slice runtime.Value → Program)
    (view : M → Slice U8) (code : Store.CodeInterpretation) :
    Platform.HostSound (platform memory allocator select) (ExecutableInv view code) (Store.decodeStore view code) := by
  apply Platform.HostSound.of_invariant (fun _ held => held.source_typed)
  intro token store identity args results held
  unfold platform
  step with (select identity args).correct memory allocator allocation view code store held
    as ⟨answer,_,fresh,_,extension,_,_⟩
  exact ⟨fresh,extension⟩

end Exec.Theorems.AllocationCallbacks
