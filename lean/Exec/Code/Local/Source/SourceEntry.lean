import Exec.Code.Local.Source.SourceLengths
import Exec.Code.Local.Relations.Local.LocalDeclarations
namespace Exec.Code
open Aeneas Aeneas.Std

theorem Emitted.sources {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {instruction : runtime.bytecode.Instr} (emitted : Emitted before after instruction) :
    SourceProgress before after := by
  obtain ⟨budget, code, sources, rfl, codeEq, sourceEq⟩ := emitted
  have lengths := congrArg List.length sourceEq
  simp only [List.length_map, List.length_append, List.length_singleton] at lengths
  simp only [SourceProgress, codeEq, List.length_append, List.length_singleton]
  omega

theorem LocalFrame.sources {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (frame : LocalFrame before after) : SourceProgress before after := by
  rw [frame]
  rfl

theorem ObserveFrame.sources {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (frame : ObserveFrame before after) : SourceProgress before after := by
  rw [frame]
  rfl

theorem SourceAligned.source_fits {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    (aligned : SourceAligned compiler) (codeFits : compiler.function.code.val.length < Usize.max) :
    compiler.function.source_offsets.val.length < Usize.max := by
  change compiler.function.source_offsets.val.length = compiler.function.code.val.length at aligned
  exact aligned.trans_lt codeFits

@[step] theorem compiler_new_sources {A : Type} (ops : runtime.platform.Alloc A)
    (signatures : Slice runtime.compiler.Signature) (functionSlots : Slice U32)
    (budget : runtime.compiler.Budget A) (batchStart : Usize) :
    runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart ⦃ out =>
      SourceAligned out ⦄ := by
  simp [runtime.compiler.FunctionCompiler.new, WP.spec_ok, SourceAligned]
end Exec.Code
