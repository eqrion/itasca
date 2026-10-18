import Exec.Interp.FloatCore.LocalInversion
import Exec.Interp.Relations.LocalCapacity
import Exec.Interp.Relations.Capacity

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Even behind forward skips, a local read's destination lies within the
allocation checked for the complete function bytecode. -/
theorem float_core_local_get_capacity
    (compiled : runtime.bytecode.CompiledFunction)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true)
    (C : context) (returns stack : List valtype)
    (labels : List LabelTarget) (index : Nat) (after : List instr)
    (next : Nat) (output : List valtype) (ty : valtype)
    (localType : C.LOCALS[index]? = some ty) :
    ∀ pc, FloatCoreCodeRel C returns compiled.code.val labels stack
      (.LOCAL_GET (.mk_uN index) :: after) pc next output →
      slots C.LOCALS + slots stack + width ty ≤ compiled.slot_count.val := by
  intro pc relation
  generalize measureEq : compiled.code.val.length - pc = measure
  induction measure using Nat.strong_induction_on generalizing pc with
  | h measure ih =>
    rcases Interp.structuredCode_linear_inv (by rfl) relation with skip | branch
    · obtain ⟨target, forward, fetched, continuation⟩ := skip
      have targetBound := continuation.entry_bound
      exact ih (compiled.code.val.length - target.val) (by omega) target.val continuation rfl
    · obtain ⟨middle, emitted, tail, head, fragment, continuation⟩ := branch
      obtain ⟨actual, src, dst, actualType, emittedEq, middleEq, source, position⟩ :=
        Interp.linearEmission_localGet_inv index (Interp.floatCoreEmission_localGet_pure index head)
      have same : actual = ty := Option.some.inj (actualType.symm.trans localType)
      subst actual
      have fetched : compiled.code.val[pc]? = some (move ty dst src) := by
        simpa only [Nat.add_zero] using fragment.fetch (index := 0)
          (by simp only [emittedEq, List.getElem?_cons_zero])
      have valid := well_formed_fetched compiled checked pc _ fetched
      have bound := (move_valid_bounds compiled ty dst src valid).1
      simpa only [position] using bound

end Exec.Code

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- LOCAL_GET needs no independent spare-capacity premise: retained code and
frame certificates establish it for the actual represented local value. -/
theorem float_core_local_get_storage_capacity {M : Type}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {raw : runtime.interp.Frame} {source : Abs.AFrame}
    (binding : FrameBinding store exec raw source)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true)
    {s C targets next output} (index : Nat) (after : List instr)
    (point : FloatFramePoint s raw { source with code := .LOCAL_GET (.mk_uN index) :: after }
      compiled C targets next output)
    (value : val) (lookup : source.locals[index]? = some value) :
    raw.base.val + Code.slots ((source.locals ++ source.vals).map Code.valueType) +
      Code.width (Code.valueType value) ≤ exec.slots.length := by
  have localType : (source.locals.map Code.valueType)[index]? = some (Code.valueType value) := by
    simp only [List.getElem?_map, lookup, Option.map_some]
  have bound := Code.float_core_local_get_capacity compiled checked C source.resultTypes
    (source.vals.map Code.valueType) targets index after next output
    (Code.valueType value) (by simpa only [point.locals] using localType) raw.pc.val point.code.current
  rw [point.locals] at bound
  change Code.slots (source.locals.map Code.valueType) + Code.slots (source.vals.map Code.valueType) + Code.width (Code.valueType value) ≤ compiled.slot_count.val at bound
  have capacity := binding.capacity inst compiled hi hc
  simp only [List.map_append, Code.slots_append]
  omega

end Exec.Interp
