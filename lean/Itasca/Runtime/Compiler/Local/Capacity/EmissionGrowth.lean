import Itasca.Runtime.Compiler.Local.Lowering.Emission.CopyContracts
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty
import Itasca.Runtime.Compiler.Local.Callbacks.MetadataPreservation
import Itasca.Runtime.Compiler.Local.Initializer.SegmentEmissionContracts

/-!
# Emission growth and observation

Successful emission bounds code and source-offset growth. Program-counter observation retains code on rejection as well as success; callback bounds compose these effects.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation
theorem compiler_emit_code_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (accepted : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (.Ok (), after)) :
    after.function.code.val = before.function.code.val ++ [instruction] := by
  have exactEffect := ((runtime.compiler.FunctionCompiler.emit.inv ops before after instruction (.Ok ()) accepted).2 law).2 rfl
  obtain ⟨used, code, sources, same, _, appended, _⟩ := exactEffect
  rw [same]
  exact appended

theorem compiler_observe_code_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.observe ops before state = .ok (status, after)) :
    after.function.code = before.function.code := by
  have frame := compiler_observe_frame ops law before state
  rw [accepted, WP.spec_ok] at frame
  exact congrArg (fun c => c.function.code) frame

theorem compiler_pair_code_result {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (a b : U32)
    (status : core.result.Result U32 Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.pair ops before a b = .ok (status, after)) :
    after.function.code = before.function.code := by
  have frame := (runtime.compiler.FunctionCompiler.pair.inv ops before after a b status accepted).1
  change after = _ at frame
  rw [frame]

/-- Computing a program counter never modifies code, including rejection. -/
theorem compiler_pc_code_result {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A)
    (status : core.result.Result U32 Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.pc ops before = .ok (status, after)) :
    after.function.code = before.function.code := by
  have effect := compiler_pc ops before
  rw [accepted, WP.spec_ok] at effect
  exact congrArg (fun f => f.code) effect.1

end Itasca.Compiler

/-! ## Source offset growth -/

section SourceOffsetGrowth

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation
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

end Itasca.Compiler

end SourceOffsetGrowth
