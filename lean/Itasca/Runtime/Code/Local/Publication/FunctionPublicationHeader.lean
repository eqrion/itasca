import Itasca.Runtime.Code.Local.Publication.FunctionPublicationRanges
import Itasca.Runtime.Code.Local.Callbacks.Common.Finish

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Non-instruction header checks required for publishing a sourced function.
These facts do not assume that the final checker accepts. -/
structure FunctionPublicationHeader (function : runtime.bytecode.CompiledFunction) : Prop where
  nonsynthetic : ¬ (function.body_start = 0#usize ∧ function.body_end = 0#usize)
  nonempty : 0 < function.code.length
  locals : function.local_slots.val ≤ function.slot_count.val
  params : function.param_slots.val ≤ function.local_slots.val
  last : ∃ start count, function.code.val[function.code.length-1]? = some (.Return start count)

/-- Header and range preservation reduce publication to the validity of each
stored instruction; successful checking is a conclusion. -/
theorem FunctionPublicationHeader.well_formed {function : runtime.bytecode.CompiledFunction}
    (header : FunctionPublicationHeader function) (ranges : FunctionPublicationRanges function)
    (instructions : ∀ (index : Nat) (bound : index < function.code.length),
      runtime.bytecode.CompiledFunction.instruction_valid function function.code.val[index] = .ok true) :
    runtime.bytecode.CompiledFunction.well_formed function = .ok true := by
  obtain ⟨start,count,last⟩ := header.last
  obtain ⟨result,called,rfl⟩ := WP.spec_imp_exists
    (ranges.well_formed header.nonsynthetic header.nonempty header.locals header.params start count last instructions)
  exact called

/-- Once the separately proved bytecode obligations hold, actual compiler
finish succeeds without allocating or changing the retained budget. -/
theorem compiler_finish_publication {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A)
    (closed : compiler.frames.val = [])
    (header : FunctionPublicationHeader compiler.function)
    (ranges : FunctionPublicationRanges compiler.function)
    (instructions : ∀ (index : Nat) (bound : index < compiler.function.code.length),
      runtime.bytecode.CompiledFunction.instruction_valid compiler.function compiler.function.code.val[index] = .ok true) :
    runtime.compiler.FunctionCompiler.finish ops compiler (.Ok ()) = .ok (.Ok compiler.function,compiler.budget) := by
  simp [runtime.compiler.FunctionCompiler.finish,alloc.vec.Vec.is_empty,closed,header.well_formed ranges instructions]

end Itasca.Runtime.Code
