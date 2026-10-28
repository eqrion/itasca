import Itasca.Runtime.Code.Local.Capacity.ChargeAvailability

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- One local declaration accepts from independently bounded reserves, word
width, and remaining local budget. Its exact frame retains every other compiler
field and budget counter. -/
theorem compiler_add_local_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (type : Itasca.types.ValueType)
    (room : compiler.budget.locals.val < compiler.budget.limits.max_locals.val)
    (localsCapacity : compiler.function.locals.length < Usize.max)
    (localsRequest : compiler.function.locals.length + 1 ≤ bound)
    (offsetCapacity : compiler.local_offsets.length < Usize.max)
    (offsetRequest : compiler.local_offsets.length + 1 ≤ bound)
    (slots : compiler.function.local_slots.val + width (Itasca.Translate.valueType type) ≤ U32.max) :
    runtime.compiler.FunctionCompiler.add_local ops compiler type ⦃ out =>
      out.1 = .Ok () ∧ ∃ locals offsets localSlots used,
        out.2 = {compiler with
          budget := {compiler.budget with locals := used}
          function := {compiler.function with locals,local_slots := localSlots}
          local_offsets := offsets} ∧
        locals.val = compiler.function.locals.val ++ [type] ∧
        offsets.val = compiler.local_offsets.val ++ [compiler.function.local_slots] ∧
        localSlots.val = compiler.function.local_slots.val + width (Itasca.Translate.valueType type) ∧
        used.val = compiler.budget.locals.val + 1 ⦄ := by
  unfold runtime.compiler.FunctionCompiler.add_local
  step with charge_counter_available ops .locals compiler.budget room
    as ⟨status,charged,accepted,used,same,usedEq⟩
  rw [accepted]
  subst charged
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with budget_push_available ops bound available {compiler.budget with locals := used}
    compiler.local_offsets compiler.function.local_slots offsetCapacity offsetRequest
    as ⟨status,charged,offsets,accepted,same,appendedOffsets⟩
  subst status charged
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with budget_push_available ops bound available {compiler.budget with locals := used}
    compiler.function.locals type localsCapacity localsRequest
    as ⟨status,charged,locals,accepted,same,appendedLocals⟩
  subst status charged
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with compiler_width type as ⟨word,wordEq⟩
  step as ⟨added,addSpec⟩
  cases added with
  | none => scalar_tac
  | some localSlots =>
    simp only [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok,WP.spec_ok]
    exact ⟨trivial,locals,offsets,localSlots,used,rfl,appendedLocals,appendedOffsets,by scalar_tac,usedEq⟩

end Itasca.Runtime.Code
