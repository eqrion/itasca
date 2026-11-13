import Itasca.Runtime.Compiler.Local.Source.SourceCursorTactic
import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupAlgebra

/-!
Sections, each formerly its own module: ControlCursor, ControlSources, BranchCertificates.
-/

/-! ## ControlCursor -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
theorem compiler_enter_cursor {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind)
    (blockType : Itasca.signature.BlockType)
    (accepted : runtime.compiler.control.FunctionCompiler.enter ops before state kind blockType = .ok (.Ok (), after)) :
    after.next_source = state.pos := by
  unfold runtime.compiler.control.FunctionCompiler.enter at accepted
  repeat' cursor_step accepted using ops, law
  all_goals try (casesm* core.result.Result Never _ <;> try casesm* Never)
  all_goals repeat' cursor_step accepted using ops, law
theorem compiler_branch_cursor {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (.Ok (), after)) :
    after.next_source = before.next_source := by
  cases conditional <;>
    simp only [runtime.compiler.control.FunctionCompiler.branch, Bool.false_eq_true, ite_false, ite_true] at accepted <;>
    repeat' cursor_step accepted using ops, law
  all_goals try (casesm* core.result.Result Never _ <;> try casesm* Never)
  all_goals repeat' cursor_step accepted using ops, law
theorem compiler_end_cursor {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind)
    (blockType : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end
      ops before state kind blockType = .ok (.Ok (), after)) :
    after.next_source = state.pos := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end at accepted
  repeat' cursor_step accepted using ops, law
  all_goals try (casesm* core.result.Result Never _ <;> try casesm* Never)
  all_goals repeat' cursor_step accepted using ops, law

theorem compiler_else_cursor {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (blockType : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else
      ops before state blockType = .ok (.Ok (), after)) :
    after.next_source = state.pos := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else at accepted
  simp only [core.option.Option.take] at accepted
  repeat' cursor_step accepted using ops, law
  all_goals try (casesm* core.result.Result Never _ <;> try casesm* Never)
  all_goals repeat' cursor_step accepted using ops, law


end Itasca.Runtime.Compiler

end

/-! ## ControlSources -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
theorem compiler_enter_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind)
    (blockType : Itasca.signature.BlockType)
    (accepted : runtime.compiler.control.FunctionCompiler.enter ops before state kind blockType = .ok (.Ok (), after)) :
    SourceProgress before after := by
  unfold runtime.compiler.control.FunctionCompiler.enter at accepted
  repeat' sources_step accepted using ops, law
theorem compiler_branch_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (.Ok (), after)) :
    SourceProgress before after := by
  cases conditional <;>
    simp only [runtime.compiler.control.FunctionCompiler.branch, Bool.false_eq_true, ite_false, ite_true] at accepted <;>
    repeat' sources_step accepted using ops, law
theorem compiler_end_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind)
    (blockType : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end
      ops before state kind blockType = .ok (.Ok (), after)) :
    SourceProgress before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end at accepted
  repeat' sources_step accepted using ops, law

theorem compiler_else_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (blockType : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else
      ops before state blockType = .ok (.Ok (), after)) :
    SourceProgress before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else at accepted
  simp only [core.option.Option.take] at accepted
  repeat' sources_step accepted using ops, law

end Itasca.Runtime.Compiler

end

/-! ## BranchCertificates -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

def BranchHole (code : List Bytecode) (sites : List Usize)
    (pc : Nat) (dst src count : U32) : Prop :=
  if count = 0#u32 ∨ src = dst then
    ∃ site, site ∈ sites ∧ site.val = pc ∧ code[pc]? = some (.Jump 4294967295#u32)
  else
    code[pc]? = some (transferInstruction dst src count) ∧
    ∃ site, site ∈ sites ∧ site.val = pc + 1 ∧ code[pc + 1]? = some (.Jump 4294967295#u32)

end Itasca.Runtime.Compiler

end
