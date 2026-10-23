import Exec.Interp.Control.StructuredLinear
import Exec.Interp.Relations.LocalCertified
import Exec.Interp.Relations.Capacity

namespace Exec.Code
open Aeneas Aeneas.Std

theorem move_valid_bounds (compiled : runtime.bytecode.CompiledFunction)
    (ty : valtype) (dst src : U32)
    (checked : runtime.bytecode.CompiledFunction.instruction_valid compiled (move ty dst src) = .ok true) :
    dst.val + width ty ≤ compiled.slot_count.val ∧ src.val + width ty ≤ compiled.slot_count.val := by
  cases ty <;> simp only [move, width, reduceIte] at checked ⊢
  all_goals first | exact copy_valid_bounds compiled dst src checked | exact copy2_valid_bounds compiled dst src checked

/-- Even behind forward skips, a local read's destination lies within the
allocation checked for the complete function bytecode. -/
theorem local_get_capacity
    (compiled : runtime.bytecode.CompiledFunction)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true)
    (types functions : List functype) (returns locals stack : List valtype)
    (labels : List LabelTarget) (index : Nat) (after : List instr)
    (next : Nat) (output : List valtype) (ty : valtype)
    (localType : locals[index]? = some ty) :
    ∀ pc, CodeRel types functions returns locals compiled.code.val labels stack
      (.LOCAL_GET (.mk_uN index) :: after) pc next output →
      slots locals + slots stack + width ty ≤ compiled.slot_count.val := by
  intro pc relation
  generalize measureEq : compiled.code.val.length - pc = measure
  induction measure using Nat.strong_induction_on generalizing pc with
  | h measure ih =>
    rcases Interp.codeRel_linear_inv (by rfl) relation with skip | branch
    · obtain ⟨target, forward, fetched, continuation⟩ := skip
      have targetBound := continuation.entry_bound
      exact ih (compiled.code.val.length - target.val) (by omega) target.val continuation rfl
    · obtain ⟨middle, emitted, tail, head, fragment, continuation⟩ := branch
      obtain ⟨actual, src, dst, actualType, emittedEq, middleEq, source, position⟩ :=
        Interp.linearEmission_localGet_inv index head
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
theorem local_get_storage_capacity {M : Type}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {raw : runtime.interp.Frame} {source : Abs.AFrame}
    (binding : FrameBinding store exec raw source)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true)
    {functions targets next output} (index : Nat) (after : List instr)
    (point : StructuredFramePoint raw { source with code := .LOCAL_GET (.mk_uN index) :: after }
      compiled functions targets next output)
    (value : val) (lookup : source.locals[index]? = some value) :
    raw.base.val + Code.slots ((source.locals ++ source.vals).map Code.valueType) +
      Code.width (Code.valueType value) ≤ exec.slots.length := by
  have localType : (source.locals.map Code.valueType)[index]? = some (Code.valueType value) := by
    simp only [List.getElem?_map, lookup, Option.map_some]
  have bound := Code.local_get_capacity compiled checked source.module.TYPES functions source.resultTypes
    (source.locals.map Code.valueType) (source.vals.map Code.valueType) targets index after next output
    (Code.valueType value) localType raw.pc.val point.code.current
  have capacity := binding.capacity inst compiled hi hc
  simp only [List.map_append, Code.slots_append]
  omega

end Exec.Interp
