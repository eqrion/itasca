import Exec.Store.Invariant.Typing
import Exec.Interp.Relations.Arguments
import Exec.Interp.Calls.CallRegions
import Exec.Interp.Relations.FrameBindings
import Exec.Abs.Invoke

/-! Invocation entry bridges checked API arguments and retained function
metadata to the typed abstract state. Compiler/body certificates remain explicit. -/
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

theorem arguments_typed {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (storeWf : wf_store (Store.decodeStore view code store))
    (args : List runtime.Value) (types : List Itasca.types.ValueType)
    (matched : List.Forall₂ (Interp.ArgumentMatches store.id) args types)
    (owned : ∀ value ∈ args, Store.ValueInStore store value) :
    ResultsTyped (Store.decodeStore view code store) (types.map Interp.sourceType)
      (args.map Interp.sourceValue) := by
  unfold ResultsTyped
  revert owned
  induction matched with
  | nil => intro owned; exact .nil
  | @cons value ty values types head tail ih =>
    intro owned
    apply List.Forall₂.cons
    · rw [← head.2]
      exact Store.value_in_store_typed view code store storeWf value (owned value (by simp))
    · apply ih
      intro v hv
      exact owned v (by simp [hv])

theorem checked_arguments_typed {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (store : runtime.store.Store M)
    (storeWf : wf_store (Store.decodeStore view code store))
    (args : Slice runtime.Value) (types : alloc.vec.Vec Itasca.types.ValueType)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref types) = .ok (.Ok ()))
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value) :
    ResultsTyped (Store.decodeStore view code store) (types.val.map Interp.sourceType)
      (args.val.map Interp.sourceValue) := by
  have h := Interp.check_values_accepts_iff memory store args (alloc.vec.Vec.deref types)
  rw [accepted] at h
  simp only [WP.spec_ok] at h
  apply arguments_typed view code store storeWf args.val types.val _ owned
  simpa [alloc.vec.Vec.deref] using h.mp trivial

theorem argument_type_tags {id : Usize} {args : List runtime.Value} {types : List Itasca.types.ValueType}
    (matched : List.Forall₂ (Interp.ArgumentMatches id) args types) :
    (args.map Interp.sourceValue).map Code.valueType = types.map Interp.sourceType := by
  induction matched with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, Interp.sourceValue_type, head.2, ih]

theorem checked_argument_type_tags {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (args : Slice runtime.Value) (types : alloc.vec.Vec Itasca.types.ValueType)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref types) = .ok (.Ok ())) :
    (args.val.map Interp.sourceValue).map Code.valueType = types.val.map Interp.sourceType := by
  have h := Interp.check_values_accepts_iff memory store args (alloc.vec.Vec.deref types)
  rw [accepted] at h
  simp only [WP.spec_ok] at h
  have matched : List.Forall₂ (Interp.ArgumentMatches store.id) args.val types.val := by
    simpa [alloc.vec.Vec.deref] using h.mp trivial
  exact argument_type_tags matched

end Exec.Theorems

