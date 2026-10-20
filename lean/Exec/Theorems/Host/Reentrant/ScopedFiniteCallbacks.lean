import Exec.Theorems.Host.Reentrant.FiniteReentrantCallbacks
import Exec.Theorems.Host.Reentrant.ScopedReentrantInvocation
import Exec.Theorems.Host.Reentrant.CallbackInstantiationNoHost

/-! Finite callbacks scoped to retained function worlds. Source termination is
required only in those worlds, rather than in every arbitrary certified store.
The implementation is the same depth-staged callback interpreter. -/
noncomputable section
namespace Exec.Theorems.ReentrantCallbacks
open Aeneas Aeneas.Std SpecExt Exec.Interp
def Program.SourceFiniteWithin {M : Type} (view : M → Slice U8) (scope : WorldScope M) : Program → Prop
  | .base _ => True
  | .action _ next | .compileInstantiate _ _ _ next => next.SourceFiniteWithin view scope
  | .branch condition yes no => if condition then yes.SourceFiniteWithin view scope else no.SourceFiniteWithin view scope
  | .invoke index values next =>
    (∀code store,ExecutableInv view code store → scope code store → index.val<store.funcs.length →
      ¬Spec.InfiniteSourceWithEvents
        ⟨⟨Store.decodeStore view code store,Spec.invocationFrame⟩,
          vals ((arguments values).val.map sourceValue)++[.CALL_ADDR index.val]⟩) ∧ next.SourceFiniteWithin view scope

theorem Program.correct_within {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (child : runtime.platform.Platform Unit M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀p,child.interrupt p ⦃ _=>True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (scope : WorldScope M) (stable : ScopeStable view scope) (package : ScopedPackage child view scope)
    (program : Program) (finite : program.SourceFiniteWithin view scope) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store) (heldScope : scope code store) :
    program.run memory child floats allocator store ⦃ answer =>
      Returns view program store answer.1 answer.2.1 answer.2.2.val ∧
      ∃afterCode,Effect view code store afterCode answer.2.1 ∧ scope afterCode answer.2.1 ∧
        ∀value∈answer.2.2.val,Store.IssuedValue answer.2.1 value ⦄ := by
  induction program generalizing code store with
  | base segment =>
    apply WP.spec_mono (segment.correct memory allocator allocation view laws code store held)
    rintro answer ⟨source,effect,issued⟩
    exact ⟨.base source,code,⟨⟨(by intro index inst found fn; rfl),effect.invariant,effect.metadata,effect.extension⟩,
      by rw [effect.externs]⟩,stable code store code answer.2.1 effect.metadata (by intro index inst found fn; rfl) effect.extension heldScope,issued⟩
  | branch condition yes no hy hn =>
    cases condition with
    | true => exact WP.spec_mono (hy finite code store held heldScope) (fun _ post=>⟨.yes post.1,post.2⟩)
    | false => exact WP.spec_mono (hn finite code store held heldScope) (fun _ post=>⟨.no post.1,post.2⟩)
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
      apply WP.spec_mono (ih finite code after effect.invariant (stable code store code after head.metadata head.agrees head.extension heldScope))
      rintro answer ⟨tail,afterCode,second,freshScope,issued⟩
      exact ⟨.action source tail,afterCode,head.trans second,freshScope,issued⟩
    | Err error => exact WP.spec.ret ⟨.rejected source,code,head,stable code store code after head.metadata head.agrees head.extension heldScope,issued⟩
  | compileInstantiate bytes profile limits next ih =>
    obtain ⟨compiled,actual,_⟩ := WP.spec_imp_exists (Code.compile_with_total allocator allocation bytes profile limits)
    unfold Program.run
    rw [actual,bind_ok]
    cases compiled with
    | Err error => exact WP.spec.ret ⟨.compile_refused,code,.refl held,heldScope,by simp⟩
    | Ok module =>
      simp only []
      split
      · rename_i noStart
        obtain ⟨answer,instRun,afterCode,effect,externs,raw,encoded,typed,source⟩ := WP.spec_imp_exists
          (instantiate_no_start_without_callbacks memory child floats allocator correct allocation interrupts view laws code store held
            module (Slice.new _) (by simp) bytes profile limits actual noStart)
        rw [instRun,bind_ok]
        have head : Effect view code store afterCode answer.2.1 := ⟨effect,by rw [externs]⟩
        cases status : answer.1 with
        | Ok identity =>
          apply WP.spec_mono (ih finite afterCode answer.2.1 effect.invariant (stable code store afterCode answer.2.1 effect.metadata effect.agrees effect.extension heldScope))
          rintro final ⟨tail,finalCode,second,freshScope,issued⟩
          exact ⟨.instantiated_terminal encoded typed source status tail,finalCode,head.trans second,freshScope,issued⟩
        | Err error => exact WP.spec.ret ⟨.instantiation_error encoded typed source status,afterCode,head,stable code store afterCode answer.2.1 effect.metadata effect.agrees effect.extension heldScope,by simp⟩
      · exact WP.spec.ret ⟨.compile_refused,code,.refl held,heldScope,by simp⟩
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
        exact finite.1 code store held heldScope inside
      simp only [runtime.interp.Execution.new,bind_ok]
      obtain ⟨answer,actual,afterCode,effect,freshScope,externs,source⟩ := WP.spec_imp_exists
        (invoke_scoped_terminates memory child floats allocator correct allocation interrupts view laws scope stable package code _ store held heldScope ()
          ⟨store.id,index⟩ (arguments values) (alloc.vec.Vec.new _) issued argumentIssued initial invoked noInfinite)
      rw [actual,bind_ok]
      have head : Effect view code store afterCode answer.2.2.1 := ⟨effect,externs⟩
      cases status : answer.1 with
      | Ok unit =>
        cases unit
        apply WP.spec_mono (ih finite.2 afterCode answer.2.2.1 effect.invariant freshScope)
        rintro final ⟨tail,finalCode,second,freshScope,issued⟩
        exact ⟨.nested source invoked status tail,finalCode,head.trans second,freshScope,issued⟩
      | Err error => exact WP.spec.ret ⟨.nested_error source invoked status,afterCode,head,freshScope,by simp⟩
    · rename_i outside
      exact WP.spec.ret ⟨.missing outside,code,.refl held,heldScope,by simp⟩


theorem platform_package_within {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (select : Nat → U64 → Slice runtime.Value → Program) (view : M → Slice U8)
    (laws : Platform.MemoryLaws memory view) (scope : WorldScope M) (stable : ScopeStable view scope)
    (finite : ∀depth identity args,(select depth identity args).SourceFiniteWithin view scope) (depth : Nat) :
    ScopedPackage (platform memory floats allocator select depth) view scope := by
  induction depth with
  | zero =>
    intro code store held heldScope token identity args defaults
    exact WP.spec.ret ⟨code,.refl held held.well_formed,heldScope,Nat.le_refl _,by simp⟩
  | succ depth ih =>
    intro code store held heldScope token identity args defaults
    obtain ⟨answer,actual,source,afterCode,effect,freshScope,issued⟩ := WP.spec_imp_exists
      ((select depth identity args).correct_within memory (platform memory floats allocator select depth) floats allocator
        correct allocation (platform_interrupts memory floats allocator select depth) view laws scope stable ih
        (finite depth identity args) code store held heldScope)
    simp only [platform,actual,bind_ok]
    exact WP.spec.ret ⟨afterCode,effect.toReturnedWorldEffect,freshScope,effect.externs,issued⟩

end Exec.Theorems.ReentrantCallbacks
