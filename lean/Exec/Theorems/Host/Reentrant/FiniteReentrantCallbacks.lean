import Exec.Theorems.Host.Reentrant.ReentrantInvocation
import Exec.Theorems.Host.Reentrant.CallbackInstantiation
import Exec.Spec.InvocationExists
import Exec.Code.Module.CompileTotal

/-! Executable finite reentrancy with a separate execution for every nested
invocation. Selectors see only copied arguments; checked operations alone see
the store. Depth stages use already constructed child platforms. -/
noncomputable section
namespace Exec.Theorems.ReentrantCallbacks
open Aeneas Aeneas.Std SpecExt Exec.Interp

inductive Program where
  | base (segment : CallbackActions.Program)
  | action (segment : CallbackActions.Program) (next : Program)
  | invoke (index : Usize) (arguments : Slice PureCallbacks.Literal) (next : Program)
  | compileInstantiate (bytes : Slice U8) (profile : Itasca.ValidationProfile) (limits : runtime.compiler.CompileLimits) (next : Program)
  | branch (condition : Bool) (yes no : Program)

abbrev Reply (M : Type) := StoreCallbacks.Reply M

def arguments (values : Slice PureCallbacks.Literal) : Slice runtime.Value :=
  OpenHostControl.literalValues values

/-- Termination evidence is stated entirely in the source semantics at each
nested call, independently of concrete callback normality or nesting depth. -/
def Program.SourceFinite {M : Type} (view : M → Slice U8) : Program → Prop
  | .base _ => True
  | .action _ next | .compileInstantiate _ _ _ next => next.SourceFinite view
  | .branch condition yes no => if condition then yes.SourceFinite view else no.SourceFinite view
  | .invoke index values next =>
    (∀code store,ExecutableInv view code store → index.val<store.funcs.length →
      ¬Spec.InfiniteSourceWithEvents
        ⟨⟨Store.decodeStore view code store,Spec.invocationFrame⟩,
          vals ((arguments values).val.map sourceValue)++[.CALL_ADDR index.val]⟩) ∧ next.SourceFinite view

/-- Every nested action creates a fresh execution. API rejection/trap retains
the returned store and stops the callback; successful calls resume its code. -/
def Program.run {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (child : runtime.platform.Platform Unit M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) : Program → runtime.store.Store M → Result (Reply M)
  | .base segment,store => segment.run memory allocator store
  | .branch condition yes no,store => if condition then yes.run memory child floats allocator store else no.run memory child floats allocator store
  | .action segment next,store => do
    let answer ← segment.run memory allocator store
    match answer.1 with
    | .Ok () => next.run memory child floats allocator answer.2.1
    | .Err error => .ok (.Err error,answer.2.1,answer.2.2)
  | .compileInstantiate bytes profile limits next,store => do
    let compiled ← runtime.compiler.compile_with allocator bytes profile limits
    match compiled with
    | .Err _ => .ok (.Err .Trap,store,Slice.new _)
    | .Ok module =>
      if module.module.env.start=none then do
        let answer ← runtime.store.instantiate.Store.instantiate_with memory child floats allocator store module (Slice.new _) ()
        match answer.1 with
        | .Ok _ => next.run memory child floats allocator answer.2.1
        | .Err _ => .ok (.Err .Trap,answer.2.1,Slice.new _)
      else .ok (.Err .Trap,store,Slice.new _)
  | .invoke index values next,store =>
    if index.val<store.funcs.length then do
      let fresh ← runtime.interp.Execution.new
      let answer ← runtime.interp.invoke_with memory child floats allocator fresh store () ⟨store.id,index⟩
        (arguments values) (alloc.vec.Vec.new _)
      match answer.1 with
      | .Ok () => next.run memory child floats allocator answer.2.2.1
      | .Err _ => .ok (.Err .Trap,answer.2.2.1,Slice.new _)
    else .ok (.Err .Trap,store,Slice.new _)

/-- Expanded finite semantics retains the nested invocation's complete source
outcome, rather than counting it as an unexplained host store replacement. -/
inductive Returns {M : Type} (view : M → Slice U8) : Program → runtime.store.Store M →
    core.result.Result Unit runtime.platform.HostError → runtime.store.Store M → List runtime.Value → Prop
  | base {segment before status after values code}
      (effect : CallbackActions.Returns view code segment before status after values) :
      Returns view (.base segment) before status after values
  | action {segment next before middle status after values ignored code}
      (head : CallbackActions.Returns view code segment before (.Ok ()) middle ignored)
      (tail : Returns view next middle status after values) :
      Returns view (.action segment next) before status after values
  | rejected {segment next before error after values code}
      (head : CallbackActions.Returns view code segment before (.Err error) after values) :
      Returns view (.action segment next) before (.Err error) after values
  | nested {index values next before answer code exec initial status after returned}
      (source : ExecutableWorldInvocationOutcome view code before exec () (alloc.vec.Vec.new _) initial answer)
      (entry : fun_invoke (Store.decodeStore view code before) index.val ((arguments values).val.map sourceValue) initial)
      (ok : answer.1=.Ok ())
      (tail : Returns view next answer.2.2.1 status after returned) :
      Returns view (.invoke index values next) before status after returned
  | nested_error {index values next before answer code exec initial error}
      (source : ExecutableWorldInvocationOutcome view code before exec () (alloc.vec.Vec.new _) initial answer)
      (entry : fun_invoke (Store.decodeStore view code before) index.val ((arguments values).val.map sourceValue) initial)
      (failed : answer.1=.Err error) :
      Returns view (.invoke index values next) before (.Err .Trap) answer.2.2.1 []
  | compile_refused {bytes profile limits next before} :
      Returns view (.compileInstantiate bytes profile limits next) before (.Err .Trap) before []
  | instantiated_terminal {bytes profile limits next before module raw code afterCode result status after returned}
      {answer : core.result.Result runtime.InstanceAddr runtime.ExecError × runtime.store.Store M × Unit}
      (encoded : Itasca.ModuleBinary.ModuleEncodingWith (Itasca.Profile.CodeEncoding profile) raw bytes.val profile)
      (typed : Module_ok (Itasca.ModuleElaboration.moduleOf raw))
      (effect : EventfulInstantiationSourceOutcome view code afterCode before module (Slice.new _) raw () answer.1 answer.2.1 answer.2.2)
      (ok : answer.1 = .Ok result)
      (tail : Returns view next answer.2.1 status after returned) :
      Returns view (.compileInstantiate bytes profile limits next) before status after returned
  | instantiation_error {bytes profile limits next before module raw code afterCode error}
      {answer : core.result.Result runtime.InstanceAddr runtime.ExecError × runtime.store.Store M × Unit}
      (encoded : Itasca.ModuleBinary.ModuleEncodingWith (Itasca.Profile.CodeEncoding profile) raw bytes.val profile)
      (typed : Module_ok (Itasca.ModuleElaboration.moduleOf raw))
      (effect : EventfulInstantiationSourceOutcome view code afterCode before module (Slice.new _) raw () answer.1 answer.2.1 answer.2.2)
      (failed : answer.1 = .Err error) :
      Returns view (.compileInstantiate bytes profile limits next) before (.Err .Trap) answer.2.1 []
  | missing {index values next before} (outside : ¬index.val<before.funcs.length) :
      Returns view (.invoke index values next) before (.Err .Trap) before []
  | yes {yes no before status after values} (tail : Returns view yes before status after values) :
      Returns view (.branch true yes no) before status after values
  | no {yes no before status after values} (tail : Returns view no before status after values) :
      Returns view (.branch false yes no) before status after values

structure Effect {M : Type} (view : M → Slice U8) (beforeCode : Store.CodeInterpretation)
    (before : runtime.store.Store M) (afterCode : Store.CodeInterpretation) (after : runtime.store.Store M) : Prop
    extends ReturnedWorldEffect view (ExecutableInv view) beforeCode before afterCode after where
  externs : before.externs.length≤after.externs.length

theorem Effect.refl {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} (held : ExecutableInv view code store) : Effect view code store code store :=
  ⟨.refl held held.well_formed,Nat.le_refl _⟩

theorem Effect.trans {M : Type} {view : M → Slice U8} {a b c : Store.CodeInterpretation}
    {s t u : runtime.store.Store M} (first : Effect view a s b t) (second : Effect view b t c u) :
    Effect view a s c u :=
  ⟨first.toReturnedWorldEffect.trans second.toReturnedWorldEffect,Nat.le_trans first.externs second.externs⟩

theorem Program.correct {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (child : runtime.platform.Platform Unit M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀p,child.interrupt p ⦃ _=>True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (package : Package child view)
    (program : Program) (finite : program.SourceFinite view) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store) :
    program.run memory child floats allocator store ⦃ answer =>
      Returns view program store answer.1 answer.2.1 answer.2.2.val ∧
      ∃afterCode,Effect view code store afterCode answer.2.1 ∧
        ∀value∈answer.2.2.val,Store.IssuedValue answer.2.1 value ⦄ := by
  induction program generalizing code store with
  | base segment =>
    apply WP.spec_mono (segment.correct memory allocator allocation view laws code store held)
    rintro answer ⟨source,effect,issued⟩
    exact ⟨.base source,code,⟨⟨(by intro index inst found fn; rfl),effect.invariant,effect.metadata,effect.extension⟩,
      by rw [effect.externs]⟩,issued⟩
  | branch condition yes no hy hn =>
    cases condition with
    | true => exact WP.spec_mono (hy finite code store held) (fun _ post=>⟨.yes post.1,post.2⟩)
    | false => exact WP.spec_mono (hn finite code store held) (fun _ post=>⟨.no post.1,post.2⟩)
  | action segment next ih =>
    obtain ⟨⟨status,after,values⟩,actual,source,effect,issued⟩ := WP.spec_imp_exists
      (segment.correct memory allocator allocation view laws code store held)
    have head : Effect view code store code after :=
      ⟨⟨(by intro index inst found fn; rfl),effect.invariant,effect.metadata,effect.extension⟩,by rw [effect.externs]⟩
    unfold Program.run
    rw [actual,bind_ok]
    cases status with
    | Ok unit =>
      cases unit
      apply WP.spec_mono (ih finite code after effect.invariant)
      rintro answer ⟨tail,afterCode,second,issued⟩
      exact ⟨.action source tail,afterCode,head.trans second,issued⟩
    | Err error => exact WP.spec.ret ⟨.rejected source,code,head,issued⟩
  | compileInstantiate bytes profile limits next ih =>
    obtain ⟨compiled,actual,_⟩ := WP.spec_imp_exists (Code.compile_with_total allocator allocation bytes profile limits)
    unfold Program.run
    rw [actual,bind_ok]
    cases compiled with
    | Err error => exact WP.spec.ret ⟨.compile_refused,code,.refl held,by simp⟩
    | Ok module =>
      simp only []
      split
      · rename_i noStart
        obtain ⟨answer,instRun,afterCode,effect,externs,raw,encoded,typed,source⟩ := WP.spec_imp_exists
          (instantiate_no_start memory child floats allocator correct allocation interrupts view laws package code store held
            module (Slice.new _) (by simp) bytes profile limits actual noStart)
        rw [instRun,bind_ok]
        have head : Effect view code store afterCode answer.2.1 := ⟨effect,by rw [externs]⟩
        cases status : answer.1 with
        | Ok identity =>
          apply WP.spec_mono (ih finite afterCode answer.2.1 effect.invariant)
          rintro final ⟨tail,finalCode,second,issued⟩
          exact ⟨.instantiated_terminal encoded typed source status tail,finalCode,head.trans second,issued⟩
        | Err error => exact WP.spec.ret ⟨.instantiation_error encoded typed source status,afterCode,head,by simp⟩
      · exact WP.spec.ret ⟨.compile_refused,code,.refl held,by simp⟩
  | invoke index values next ih =>
    unfold Program.run
    split
    · rename_i inside
      have issued : Store.ExternalIssued store (.Func ⟨store.id,index⟩) := fun _=>inside
      have argumentIssued : ∀value∈(arguments values).val,Store.IssuedValue store value :=
        (PureCallbacks.Program.returned values).issued store
      have sourceBound : index.val<(Store.decodeStore view code store).FUNCS.length := by
        simpa only [Store.decodeStore,List.length_map] using inside
      obtain ⟨initial,invoked⟩ := Spec.invocation_exists held.well_formed index.val sourceBound
        ((arguments values).val.map sourceValue) (by
          intro value member
          obtain ⟨raw,_,rfl⟩ := List.mem_map.mp member
          exact sourceValue_wf raw)
      have noInfinite : ¬Spec.InfiniteSourceWithEvents initial := by
        rw [Spec.invocation_config invoked]
        exact finite.1 code store held inside
      simp only [runtime.interp.Execution.new,bind_ok]
      obtain ⟨answer,actual,afterCode,effect,externs,source⟩ := WP.spec_imp_exists
        (invoke_terminates memory child floats allocator correct allocation interrupts view laws package code _ store held ()
          ⟨store.id,index⟩ (arguments values) (alloc.vec.Vec.new _) issued argumentIssued initial invoked noInfinite)
      rw [actual,bind_ok]
      have head : Effect view code store afterCode answer.2.2.1 := ⟨effect,externs⟩
      cases status : answer.1 with
      | Ok unit =>
        cases unit
        apply WP.spec_mono (ih finite.2 afterCode answer.2.2.1 effect.invariant)
        rintro final ⟨tail,finalCode,second,issued⟩
        exact ⟨.nested source invoked status tail,finalCode,head.trans second,issued⟩
      | Err error => exact WP.spec.ret ⟨.nested_error source invoked status,afterCode,head,by simp⟩
    · rename_i outside
      exact WP.spec.ret ⟨.missing outside,code,.refl held,by simp⟩


/-- Depth zero rejects calls. Each successor uses a separately constructed
child platform and a fresh execution for nested Wasm. No self-referential host
contract or universal callback-normality premise occurs in this construction. -/
def platform {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (select : Nat → U64 → Slice runtime.Value → Program) : Nat → runtime.platform.Platform Unit M
  | 0 => {
      MemoryBufferInst := memory
      interrupt token := .ok (.Continue,token)
      call_host token store _ _ _ := .ok (.Err .Trap,token,store,Slice.new _) }
  | depth+1 => {
      MemoryBufferInst := memory
      interrupt token := .ok (.Continue,token)
      call_host token store identity args _ := do
        let answer ← (select depth identity args).run memory (platform memory floats allocator select depth) floats allocator store
        .ok (answer.1,token,answer.2.1,answer.2.2) }

theorem platform_interrupts {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (select : Nat → U64 → Slice runtime.Value → Program) (depth : Nat) (token : Unit) :
    (platform memory floats allocator select depth).interrupt token ⦃ _=>True ⦄ := by
  cases depth <;> exact WP.spec.ret trivial

/-- Finite reentrancy is certified by induction on platform depth. Termination
of nested Wasm is supplied separately by independent source semantics. The
complete callback package is a conclusion about these actual implementations. -/
theorem platform_package {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (select : Nat → U64 → Slice runtime.Value → Program) (view : M → Slice U8)
    (laws : Platform.MemoryLaws memory view)
    (finite : ∀depth identity args,(select depth identity args).SourceFinite view) (depth : Nat) :
    Package (platform memory floats allocator select depth) view := by
  induction depth with
  | zero =>
    intro code store held token identity args defaults
    exact WP.spec.ret ⟨code,.refl held held.well_formed,Nat.le_refl _,by simp⟩
  | succ depth ih =>
    intro code store held token identity args defaults
    obtain ⟨answer,actual,source,afterCode,effect,issued⟩ := WP.spec_imp_exists
      ((select depth identity args).correct memory (platform memory floats allocator select depth) floats allocator
        correct allocation (platform_interrupts memory floats allocator select depth) view laws ih
        (finite depth identity args) code store held)
    simp only [platform,actual,bind_ok]
    exact WP.spec.ret ⟨afterCode,effect.toReturnedWorldEffect,effect.externs,issued⟩

/-- The bounded reentrant implementation supplies the ordinary world-aware
callback contract, with generated source typing derived from the retained full
invariant. Dynamic host-result checking remains in the native interpreter. -/
theorem platform_world_sound {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (select : Nat → U64 → Slice runtime.Value → Program) (view : M → Slice U8)
    (laws : Platform.MemoryLaws memory view)
    (finite : ∀depth identity args,(select depth identity args).SourceFinite view) (depth : Nat) :
    HostWorldSound (platform memory floats allocator select depth) view (ExecutableInv view) := by
  intro code store held token identity args defaults
  apply WP.spec_mono (platform_package memory floats allocator correct allocation select view laws finite depth code store held token identity args defaults)
  rintro answer ⟨afterCode,effect,externs,issued⟩
  exact ⟨afterCode,effect.agrees,effect.invariant,effect.extension,effect.invariant.source_typed⟩
end Exec.Theorems.ReentrantCallbacks
