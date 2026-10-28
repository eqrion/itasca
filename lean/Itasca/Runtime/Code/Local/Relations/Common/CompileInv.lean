import Itasca.Runtime.Code.Local.Relations.Common.Rel
import Itasca.Support.TypeTranslation

/-! The layout component of the compiler invariant, stated over the actual
extracted compiler state. Prefix-code, open-label, and fixup preservation are
separate obligations; this file does not assert the final compilation theorem. -/

namespace Itasca.Runtime.Code
open Aeneas.Std

/-- The compiler keeps locals in source order, including function parameters. -/
def compilerLocals {A : Type} (compiler : runtime.compiler.FunctionCompiler A) :
    List valtype := compiler.function.locals.val.map Itasca.Translate.valueType

/-- Slot starts for a typed operand stack, after the fixed local region. -/
def stackOffsets (locals stack : List valtype) : List Nat :=
  (List.range stack.length).map (fun index => slots locals + offset stack index)

/-- Concrete offset vectors agree with the source type layout. Maximum slot
capacity bounds the current height whenever this prefix is reachable. -/
structure CompilerLayout {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (stack : List valtype) : Prop where
  localSlots : compiler.function.local_slots.val = slots (compilerLocals compiler)
  localOffsets : compiler.local_offsets.val.map (fun word => word.val) =
    (List.range (compilerLocals compiler).length).map (offset (compilerLocals compiler))
  operandOffsets : compiler.before.val.map (fun word => word.val) =
    stackOffsets (compilerLocals compiler) stack
  height : compiler.height.val = slots (compilerLocals compiler) + slots stack
  capacity : compiler.reachable = true → compiler.height.val ≤ compiler.function.slot_count.val

theorem CompilerLayout.locals_length {A : Type}
    {compiler : runtime.compiler.FunctionCompiler A} {stack}
    (h : CompilerLayout compiler stack) :
    compiler.local_offsets.val.length = compiler.function.locals.val.length := by
  have := congrArg List.length h.localOffsets
  simpa [compilerLocals] using this

theorem CompilerLayout.operands_length {A : Type}
    {compiler : runtime.compiler.FunctionCompiler A} {stack}
    (h : CompilerLayout compiler stack) : compiler.before.val.length = stack.length := by
  have := congrArg List.length h.operandOffsets
  simpa [stackOffsets] using this

/-- Any declared local starts below the live operand region. The compiler's
copy-elision guard therefore cannot erase a local get, set, or tee transfer. -/
theorem CompilerLayout.local_before_operand_region {A : Type}
    {compiler : runtime.compiler.FunctionCompiler A} {stack index ty}
    (h : CompilerLayout compiler stack)
    (localType : (compilerLocals compiler)[index]? = some ty) :
    offset (compilerLocals compiler) index < compiler.function.local_slots.val := by
  rw [h.localSlots]
  exact offset_lt_slots localType

/-- The current source stack fits the concrete function's allocated slot bound. -/
theorem CompilerLayout.live_slots_fit {A : Type}
    {compiler : runtime.compiler.FunctionCompiler A} {stack}
    (h : CompilerLayout compiler stack) (live : compiler.reachable = true) :
    slots (compilerLocals compiler) + slots stack ≤ compiler.function.slot_count.val := by
  rw [← h.height]
  exact h.capacity live

end Itasca.Runtime.Code
