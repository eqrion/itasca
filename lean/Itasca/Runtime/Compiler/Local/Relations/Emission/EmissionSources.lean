import Itasca.Runtime.Compiler.Local.Lowering.Emission.Emit
import Itasca.Runtime.Compiler.Local.Capacity.EmissionGrowth

/-!
Source-offset vector length after a successful emit operation.

Main declarations: `compiler_emit_source_length_success`. A direct consumer is `Compiler.Local.Relations.Control.BranchSuccessEmit`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
theorem compiler_emit_source_length_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (accepted : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (.Ok (), after)) :
    after.function.source_offsets.val.length = before.function.source_offsets.val.length + 1 := by
  have exactEffect := ((runtime.compiler.FunctionCompiler.emit.inv ops before after instruction (.Ok ()) accepted).2 law).2 rfl
  obtain ⟨used, code, sources, same, _, _, coordinates⟩ := exactEffect
  rw [same]
  have lengths := congrArg List.length coordinates
  simpa only [List.length_map, List.length_append, List.length_singleton] using lengths

end Itasca.Runtime.Compiler
