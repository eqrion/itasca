import Itasca.Runtime.Interp.Machine.Point
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdEmission
import Itasca.Runtime.SourceMachine.Simd.Source

/-!
Inversion of a SIMD code point.

Main declarations: `simd_point_head`. A direct consumer is `Interp.Machine.Simd.Prepare`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas.Std

variable {jumpTables : List Aeneas.Std.U32}
theorem simd_point_head {emission : ContextEmission} {immediates constants C returns code labels stack pc next output}
    (source : instr) (after : List instr)
    (allowed : SourceMachine.SimdInstr source)
    (project : ∀ before emitted result, emission C before source emitted result →
      Compiler.SimdEmission immediates constants C before source emitted result)
    (point : Compiler.StructuredCode.Point (emission C) C.TYPES C.FUNCS returns C.LOCALS
      code jumpTables labels stack (source::after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode.Point (emission C) C.TYPES C.FUNCS returns C.LOCALS
        code jumpTables labels stack (source::after) target.val next output) ∨
    (∃ (instruction : Compiler.Bytecode) (result : List valtype),
      Compiler.SimdEmission immediates constants C stack source [instruction] result ∧
      code[pc]? = some instruction ∧
      Compiler.StructuredCode.Point (emission C) C.TYPES C.FUNCS returns C.LOCALS
        code jumpTables labels result after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : source::after = cursor at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    have projected := project _ _ _ head
    have length := projected.length_one
    cases projected with
    | instruction front input output source opcode operand entry immediate instruction meaning metadata made position =>
      have fetch := fragment.fetch (index := 0) (by rfl)
      obtain ⟨_,_,_,_,nextEq⟩ := fragment
      refine Or.inr ⟨instruction,front++output,.instruction front input output _ opcode operand entry immediate
        instruction meaning metadata made position,by simpa using fetch,?_⟩
      exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
    | constant front bits dst entry metadata position =>
      have fetch := fragment.fetch (index := 0) (by rfl)
      obtain ⟨_,_,_,_,nextEq⟩ := fragment
      refine Or.inr ⟨.ConstV128 dst entry,stack++[.V128],.constant stack bits dst entry metadata position,
        by simpa using fetch,?_⟩
      exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ =>
    cases allowed with
    | pure signature => cases signature <;> simp at sourceEq
    | constant => simp at sourceEq
    | memory signature => cases signature <;> simp at sourceEq
end Itasca.Runtime.Interp.Machine
