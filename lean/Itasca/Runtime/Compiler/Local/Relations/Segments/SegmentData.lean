import Itasca.Runtime.Compiler.Local.Initializer.SegmentEmissionContracts
import Itasca.Runtime.Compiler.Local.Initializer.ConstantContracts
import Itasca.Runtime.Compiler.Local.Initializer.InitializerElementAppend
import Itasca.Runtime.Compiler.Local.Initializer

/-!
Segment program certificates and the data-emission compatibility theorem.
-/

/-! ## SegmentProgram -/

section

/-! Syntactic programs emitted for active and declarative segments. The
certificate records source segment indices and actual embedded descriptor
lookups; runtime bounds and source typing remain separate obligations. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- The initialization function is the source-ordered concatenation of segment
programs followed by a zero-result return. -/
structure SegmentProgramBody (module : runtime.compiler.ExecutableModule)
    (function : runtime.bytecode.CompiledFunction)
    (elementPrograms dataPrograms : List (List runtime.bytecode.Instr)) : Prop where
  elementCount : elementPrograms.length = module.module.env.elements.length
  dataCount : dataPrograms.length = module.module.tail.data.length
  elements : ∀ index segment, module.module.env.elements.val[index]? = some segment →
    ∃ instructions, elementPrograms[index]? = some instructions ∧ ElementProgram function index segment instructions
  datas : ∀ index segment, module.module.tail.data.val[index]? = some segment →
    ∃ instructions, dataPrograms[index]? = some instructions ∧ DataProgram function index segment instructions
  instructions : function.code.val = elementPrograms.flatten ++ dataPrograms.flatten ++ [.Return 0#u32 0#u32]
  capacity : function.slot_count = 0#u32 ∨ function.slot_count = 3#u32
  activeCapacity : (∃ (index : Nat) (instructions : List runtime.bytecode.Instr), elementPrograms[index]? = some instructions ∧ instructions.length = 5) ∨
    (∃ (index : Nat) (instructions : List runtime.bytecode.Instr), dataPrograms[index]? = some instructions ∧ instructions.length = 5) →
    function.slot_count = 3#u32
  localSlots : function.local_slots = 0#u32
  paramSlots : function.param_slots = 0#u32
  locals : function.locals.val = []

def SegmentProgram (module : runtime.compiler.ExecutableModule) (function : runtime.bytecode.CompiledFunction) : Prop :=
  ∃ elements datas, SegmentProgramBody module function elements datas

end Itasca.Runtime.Compiler

end

/-! ## SegmentData -/

section

/-!
Validated data offsets and emitted data-initializer programs.

The emission contract and offset lemmas live in `Initializer.SegmentEmissionContracts`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

theorem emit_data_program {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module : runtime.compiler.ExecutableModule)
    (budget afterBudget : runtime.compiler.Budget A)
    (before after : runtime.bytecode.CompiledFunction) (index : Usize)
    (segment : Itasca.metadata.Data)
    (found : module.module.tail.data.val[index.val]? = some segment)
    (valid : ∀ memory offset, segment.mode = .Active memory offset →
      Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (success : runtime.compiler.initialize.emit_data ops module budget before index =
      .ok (.Ok (), afterBudget, after)) :
    ∃ instructions, DataProgram after index.val segment instructions ∧
      after.code.val = before.code.val ++ instructions ∧
      after = {before with code := after.code, slot_count := after.slot_count} ∧
      (instructions = [] ∧ after.slot_count = before.slot_count ∨
        instructions.length = 5 ∧ after.slot_count = 3#u32) := by
  exact runtime.compiler.initialize.emit_data.inv ops law module budget afterBudget before after index segment found valid success

end Itasca.Runtime.Compiler

end
