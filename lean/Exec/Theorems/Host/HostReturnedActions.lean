import Exec.Theorems.Host.HostWorldSound
import Exec.Spec.Extend
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

/-- Store effects retained by returned public actions. This is a conclusion of
an action's proof, not a law imposed on arbitrary callbacks. -/
structure ReturnedWorldEffect {M : Type} (view : M → Slice U8)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (beforeCode : Store.CodeInterpretation) (before : runtime.store.Store M)
    (afterCode : Store.CodeInterpretation) (after : runtime.store.Store M) : Prop where
  agrees : Store.CodeAgreesOn before beforeCode afterCode
  invariant : Inv afterCode after
  metadata : FrameStorePrefix before after
  extension : Extend_store (Store.decodeStore view beforeCode before) (Store.decodeStore view afterCode after)

theorem ReturnedWorldEffect.refl {M : Type} {view : M → Slice U8}
    {Inv : Store.CodeInterpretation → runtime.store.Store M → Prop}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    (valid : Inv code store) (wellFormed : wf_store (Store.decodeStore view code store)) :
    ReturnedWorldEffect view Inv code store code store :=
  ⟨(by intro index inst found fn; rfl),valid,.refl _,Spec.extend_store_refl _ wellFormed⟩

theorem ReturnedWorldEffect.trans {M : Type} {view : M → Slice U8}
    {Inv : Store.CodeInterpretation → runtime.store.Store M → Prop}
    {a b c : Store.CodeInterpretation} {s t u : runtime.store.Store M}
    (first : ReturnedWorldEffect view Inv a s b t)
    (second : ReturnedWorldEffect view Inv b t c u) : ReturnedWorldEffect view Inv a s c u :=
  ⟨first.agrees.trans_prefix first.metadata second.agrees,second.invariant,
    first.metadata.trans second.metadata,Spec.extend_store_trans first.extension second.extension⟩

/-- A concrete action returned, and its returned store has the checked effect.
The arbitrary result type allows invoke, instantiate, and store APIs to keep
using their existing result shapes. No termination follows from this witness. -/
inductive ReturnedWorldAction {M : Type} (view : M → Slice U8)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop) :
    Store.CodeInterpretation → runtime.store.Store M → Store.CodeInterpretation → runtime.store.Store M → Prop
  | returned {α : Type} (run : Result α) (answer : α) (storeOf : α → runtime.store.Store M)
      {beforeCode afterCode before} (actual : run = .ok answer)
      (effect : ReturnedWorldEffect view Inv beforeCode before afterCode (storeOf answer)) :
      ReturnedWorldAction view Inv beforeCode before afterCode (storeOf answer)

/-- A partial-correctness API theorem supplies an action witness only after an
actual return has been established. In particular this does not turn WPdiv into
normality, even when a caller has finite nesting depth. -/
theorem ReturnedWorldAction.of_return {M α : Type} {view : M → Slice U8}
    {Inv : Store.CodeInterpretation → runtime.store.Store M → Prop}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    (run : Result α) (answer : α) (storeOf : α → runtime.store.Store M)
    (safe : run ⦃out => ∃afterCode, ReturnedWorldEffect view Inv code store afterCode (storeOf out)⦄div)
    (actual : run = .ok answer) :
    ∃afterCode, ReturnedWorldAction view Inv code store afterCode (storeOf answer) := by
  rw [actual,WP.dspec_ok] at safe
  obtain ⟨afterCode,effect⟩ := safe
  exact ⟨afterCode,.returned run answer storeOf actual effect⟩

theorem ReturnedWorldAction.effect {M : Type} {view : M → Slice U8}
    {Inv : Store.CodeInterpretation → runtime.store.Store M → Prop}
    {a b : Store.CodeInterpretation} {s t : runtime.store.Store M}
    (action : ReturnedWorldAction view Inv a s b t) : ReturnedWorldEffect view Inv a s b t := by
  cases action with | returned run answer storeOf actual effect => exact effect

/-- A finite sequence of actual returned actions. Connecting a callback's store
updates to this sequence is an explicit embedder obligation below. -/
inductive ReturnedWorldTrace {M : Type} (view : M → Slice U8)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop) :
    Store.CodeInterpretation → runtime.store.Store M → Store.CodeInterpretation → runtime.store.Store M → Prop
  | nil {code store} (valid : Inv code store) (wellFormed : wf_store (Store.decodeStore view code store)) :
      ReturnedWorldTrace view Inv code store code store
  | cons {a b c s t u} (head : ReturnedWorldAction view Inv a s b t)
      (tail : ReturnedWorldTrace view Inv b t c u) : ReturnedWorldTrace view Inv a s c u

theorem ReturnedWorldTrace.effect {M : Type} {view : M → Slice U8}
    {Inv : Store.CodeInterpretation → runtime.store.Store M → Prop}
    {a b : Store.CodeInterpretation} {s t : runtime.store.Store M}
    (trace : ReturnedWorldTrace view Inv a s b t) : ReturnedWorldEffect view Inv a s b t := by
  induction trace with
  | nil valid wellFormed => exact .refl valid wellFormed
  | cons head tail ih => exact head.effect.trans ih

/-- Normal callback control and concrete returned-action decomposition imply
its store contract. Neither premise is established by public API preservation:
a nested invocation may diverge, and arbitrary hooks need not decompose into
these actions. Nested API proofs must use independently justified callback
contracts (for example those already established at smaller nesting depth).
Raw extern/result issuance laws remain separate from this source-store law. -/
theorem HostWorldSound.of_returned_actions {M P : Type}
    {hooks : runtime.platform.Platform P M} {view : M → Slice U8}
    {Inv : Store.CodeInterpretation → runtime.store.Store M → Prop}
    (normal : ∀code store, Inv code store → ∀platform host args results,
      hooks.call_host platform store host args results ⦃_ => True⦄)
    (decomposes : ∀code store, Inv code store → ∀platform host args results answer,
      hooks.call_host platform store host args results = .ok answer →
      ∃afterCode, ReturnedWorldTrace view Inv code store afterCode answer.2.2.1) :
    HostWorldSound hooks view Inv := by
  intro code store valid platform host args results
  obtain ⟨answer,actual,_⟩ := WP.spec_imp_exists (normal code store valid platform host args results)
  obtain ⟨afterCode,trace⟩ := decomposes code store valid platform host args results answer actual
  rw [actual]
  exact WP.spec.ret ⟨afterCode,trace.effect.agrees,trace.effect.invariant,trace.effect.extension⟩
end Exec.Theorems
