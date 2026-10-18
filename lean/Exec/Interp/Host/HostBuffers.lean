import Exec.Interp.Relations.InvocationSetup
import Exec.Interp.Relations.Readback
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- The host scratch argument buffer is cleared by the actual extracted loop. -/
@[step] theorem clear_host_arguments (values : alloc.vec.Vec runtime.Value) :
    runtime.interp.call_loop0 values ⦃ after => after.val = [] ⦄ := by
  exact clear_results values

/-- The host scratch result buffer is cleared independently before each call. -/
@[step] theorem clear_host_results (values : alloc.vec.Vec runtime.Value) :
    runtime.interp.call_loop1 values ⦃ after => after.val = [] ⦄ := by
  exact clear_results values

def zeroValue : Itasca.types.ValueType → runtime.Value
  | .I32 => .I32 0#u32
  | .I64 => .I64 0#u64
  | .F32 => .F32 0#u32
  | .F64 => .F64 0#u64
  | .V128 => .V128 0#u128
  | .FuncRef => .FuncRef none
  | .ExternRef => .ExternRef none

@[simp] theorem zeroValue_type (ty : Itasca.types.ValueType) : rawType (zeroValue ty) = ty := by
  cases ty <;> rfl

@[simp] theorem zeroValue_owned (ty : Itasca.types.ValueType) (store : Usize) :
    ValueOwnedFits store (zeroValue ty) := by cases ty <;> trivial

@[simp] theorem zeroValue_exact (ty : Itasca.types.ValueType) : runtime.Value.zero ty = .ok (zeroValue ty) := by
  cases ty <;> rfl

/-- Default host results have exactly the signature's arity and raw types. -/
@[step] theorem host_results_defaults_loop (values : alloc.vec.Vec runtime.Value)
    (types : alloc.vec.Vec Itasca.types.ValueType) (index : Usize)
    (bound : index.val ≤ types.length)
    (prior : values.val = (types.val.take index.val).map zeroValue) :
    runtime.interp.call_loop3 values types index ⦃ after => after.val = types.val.map zeroValue ⦄ := by
  unfold runtime.interp.call_loop3
  apply loop.spec_decr_nat (fun p => types.length - p.2.val)
    (fun p => p.2.val ≤ types.length ∧ p.1.val = (types.val.take p.2.val).map zeroValue)
  · rintro ⟨current, i⟩ ⟨hi, currentEq⟩
    dsimp only at hi currentEq ⊢
    unfold runtime.interp.call_loop3.body
    dsimp only
    split
    · have inBounds : i.val < types.length := by scalar_tac
      have currentLength : current.length = i.val := by
        simp only [alloc.vec.Vec.length, currentEq, List.length_map, List.length_take]
        exact Nat.min_eq_left hi
      step as ⟨ty, found⟩
      rw [zeroValue_exact]
      simp only [bind_ok]
      step as ⟨after, added⟩
      step as ⟨next, nextEq⟩
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [nextEq, List.take_add_one]
      simp only [List.getElem?_eq_getElem inBounds, added, currentEq, found,
        List.map_append, Option.toList_some, List.map_cons, List.map_nil]
    · have same : i.val = types.length := by scalar_tac
      simpa [WP.spec_ok, same] using currentEq
  · exact ⟨bound, prior⟩

@[step] theorem host_results_defaults (values : alloc.vec.Vec runtime.Value)
    (types : alloc.vec.Vec Itasca.types.ValueType) (empty : values.val = []) :
    runtime.interp.call_loop3 values types 0#usize ⦃ after => after.val = types.val.map zeroValue ⦄ := by
  exact host_results_defaults_loop values types 0#usize (by simp) (by simpa using empty)
end Exec.Interp
