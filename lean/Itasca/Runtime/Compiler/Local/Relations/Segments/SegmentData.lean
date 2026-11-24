import Itasca.Runtime.Compiler.Local.Definitions
import Itasca.Runtime.Compiler.Local.Initializer.SegmentEmissionContracts
import Itasca.Runtime.Compiler.Local.Initializer.ExpressionContracts
import Itasca.Runtime.Compiler.Local.Initializer

open Itasca.Representation

/-!
Segment program certificates and the data-emission compatibility theorem.
-/

/-! ## SegmentData -/

section

/-!
Validated data offsets and emitted data-initializer programs.

The emission contract and offset lemmas live in `Initializer.SegmentEmissionContracts`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std

theorem emit_data_program {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module : runtime.compiler.ExecutableModule)
    (budget afterBudget : runtime.compiler.Budget A)
    (before after : runtime.bytecode.CompiledFunction) (index : Usize)
    (segment : Itasca.metadata.Data)
    (found : module.module.tail.data.val[index.val]? = some segment)
    (valid : ∀ memory offset, segment.mode = .Active memory offset →
      Itasca.Module.Constants.Valid module.module.env offset .I32)
    (success : runtime.compiler.initialize.emit_data ops module budget before index =
      .ok (.Ok (), afterBudget, after)) :
    ∃ instructions, DataProgram after index.val segment instructions ∧
      after.code.val = before.code.val ++ instructions ∧
      after = {before with code := after.code, slot_count := after.slot_count} ∧
      (instructions = [] ∧ after.slot_count = before.slot_count ∨
        instructions.length = 5 ∧ after.slot_count = 3#u32) := by
  exact runtime.compiler.initialize.emit_data.inv ops law module budget afterBudget before after index segment found valid success

end Itasca.Compiler

end
