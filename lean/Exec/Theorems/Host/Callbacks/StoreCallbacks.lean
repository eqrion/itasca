import Exec.Theorems.Host.Callbacks.PureCallbacks
import Exec.Store.Invariant.IssuedArguments
import Exec.Theorems.Api.ExecutableInvWrites

/-! Executable callbacks with checked global writes. The program receives no
raw store or memory borrow. Addresses are checked at each operation before the
extracted API is called; a rejected operation becomes a host trap. -/
namespace Exec.Theorems.StoreCallbacks
open Aeneas Aeneas.Std

inductive Program where
  | terminal (reply : PureCallbacks.Program)
  | writeI32 (index : Usize) (value : U32) (next : Program)
  | branch (condition : Bool) (yes no : Program)

abbrev Reply (M : Type) := core.result.Result Unit runtime.platform.HostError ×
  runtime.store.Store M × Slice runtime.Value

/-- The only store mutation available to a program calls the extracted checked
API. Invalid indices are rejected before indexing; API rejection retains the
returned store and produces a host trap. -/
def Program.run {M : Type} (memory : runtime.platform.MemoryBuffer M) :
    Program → runtime.store.Store M → Result (Reply M)
  | .terminal reply, store => .ok (reply.evaluate.1,store,reply.evaluate.2)
  | .branch condition yes no, store => if condition then yes.run memory store else no.run memory store
  | .writeI32 index value next, store =>
    if index.val < store.globals.length then do
      let answer ← runtime.store.Store.set_global memory store ⟨store.id,index⟩ (.I32 value)
      match answer.1 with
      | .Ok () => next.run memory answer.2
      | .Err _ => .ok (.Err .Trap,answer.2,Slice.new _)
    else .ok (.Err .Trap,store,Slice.new _)

private theorem write_metadata {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (index : Usize) (value : U32)
    (inside : index.val < store.globals.length) :
    runtime.store.Store.set_global memory store ⟨store.id,index⟩ (.I32 value) ⦃ answer =>
      Interp.FrameStoreMetadata store answer.2 ∧ answer.2.externs = store.externs ⦄ := by
  have owned : Store.ValueInStore store (.I32 value) := ⟨trivial,trivial⟩
  by_cases mutable : (store.globals.val[index.val]).ty.mutability = .Var
  · by_cases typed : (store.globals.val[index.val]).ty.valtype = Interp.rawType (.I32 value)
    · apply WP.spec_mono (Store.global_write memory store index (.I32 value) inside mutable typed owned.1)
      rintro answer ⟨words,_,_,same⟩
      rw [same]
      exact ⟨⟨rfl,rfl,rfl,rfl⟩,rfl⟩
    · apply WP.spec_mono (Store.global_write_rejected memory store index (.I32 value) inside owned (Or.inr typed))
      intro answer same
      rw [same]
      exact ⟨.refl _,rfl⟩
  · apply WP.spec_mono (Store.global_write_rejected memory store index (.I32 value) inside owned (Or.inl mutable))
    intro answer same
    rw [same]
    exact ⟨.refl _,rfl⟩

/-- The implementation returns normally, retains source typing and raw frame
prefixes, and issues its results. No callback-normality or decomposition law
is supplied by the caller. -/
theorem Program.correct_owned {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (program : Program) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store) :
    program.run memory store ⦃ answer =>
      ExecutableInv view code answer.2.1 ∧ Interp.FrameStorePrefix store answer.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code answer.2.1) ∧
      answer.2.1.externs = store.externs ∧
      ∀ value ∈ answer.2.2.val, Store.ValueInStore answer.2.1 value ⦄ := by
  induction program generalizing store with
  | terminal reply =>
    exact WP.spec.ret ⟨held,.refl _,Spec.extend_store_refl _ held.well_formed,rfl,reply.in_store _⟩
  | branch condition yes no hy hn => cases condition <;> first | exact hy store held | exact hn store held
  | writeI32 index value next ih =>
    unfold Program.run
    split
    · rename_i inside
      obtain ⟨answer,actual,fresh,_,extension⟩ := WP.spec_imp_exists
        (ExecutableInv.global_write_any_certified memory view code store held index (.I32 value) inside ⟨trivial,trivial⟩)
      have metadata := write_metadata memory store index value inside
      rw [actual,WP.spec_ok] at metadata
      rw [actual,bind_ok]
      cases status : answer.1 with
      | Ok result =>
        cases result
        apply WP.spec_mono (ih answer.2 fresh)
        rintro final ⟨certified,retained,transExtension,externs,issued⟩
        exact ⟨certified,metadata.1.prefix.trans retained,Spec.extend_store_trans extension transExtension,
          externs.trans metadata.2,issued⟩
      | Err error =>
        exact WP.spec.ret ⟨fresh,metadata.1.prefix,extension,metadata.2,by simp⟩
    · exact WP.spec.ret ⟨held,.refl _,Spec.extend_store_refl _ held.well_formed,rfl,by simp⟩

/-- The issued-result contract follows from the stronger owned-result package. -/
theorem Program.correct {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (program : Program) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store) :
    program.run memory store ⦃ answer =>
      ExecutableInv view code answer.2.1 ∧ Interp.FrameStorePrefix store answer.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code answer.2.1) ∧
      answer.2.1.externs = store.externs ∧
      ∀ value ∈ answer.2.2.val, Store.IssuedValue answer.2.1 value ⦄ := by
  apply WP.spec_mono (program.correct_owned memory view code store held)
  rintro answer ⟨certified,metadata,extension,externs,owned⟩
  exact ⟨certified,metadata,extension,externs,fun value member=>(owned value member).issued⟩

end Exec.Theorems.StoreCallbacks
