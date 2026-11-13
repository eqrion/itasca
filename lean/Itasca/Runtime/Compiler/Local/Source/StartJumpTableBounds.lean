import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableFrames
import Itasca.Runtime.Compiler.Local.Relations.Table.ControlTablePreservation
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables
import Itasca.Runtime.Compiler.Local.Callbacks.CodeGrowth.CompilerCodeMonotoneLiteral
import Itasca.Runtime.Compiler.Local.Relations.Function.CoreFunctionContext
import Itasca.Runtime.Compiler.Local.Relations.Function.FunctionEnvironment

/-!
Sections, each formerly its own module: TableTransferBounds, JumpTableBounds, StartJumpTableBounds.
-/

/-! ## TableTransferBounds -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Source-selected table arms have a complete transfer region below the
selector. Backedges refer to an already opened loop position. -/
def TableTransferBounds (compiler : runtime.compiler.FunctionCompiler A) : Prop :=
  ∀ depth ∈ compiler.table_depths.val, ∀ (index : Usize) (frame : runtime.compiler.Frame),
    compiler.frames.val[index.val]? = some frame → index.val+depth.val+1 = compiler.frames.val.length →
    frame.height.val+(frameBranchWidth frame).val+1 ≤ compiler.height.val ∧
      (frame.kind = .Loop → frame.start_pc.val ≤ compiler.function.code.length)

/-- Repeated table targets retain source transfer geometry when a previous
stub records exit liveness and adds fixups to the same physical label. -/
theorem TableTransferBounds.advance {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {chosen} (held : TableTransferBounds before) (effect : TableTargetCode before after chosen)
    (depths : after.table_depths = before.table_depths) (height : after.height = before.height) :
    TableTransferBounds after := by
  obtain ⟨fragment,appended,_⟩ := effect.code_prefix
  have growth : before.function.code.length ≤ after.function.code.length := by
    change before.function.code.val.length ≤ after.function.code.val.length
    rw [appended,List.length_append]
    omega
  have length := effect.frame_length
  intro depth member index frame lookup position
  rw [depths] at member
  rw [length] at position
  have retain (old : frame.height.val+(frameBranchWidth frame).val+1 ≤ before.height.val ∧
      (frame.kind = .Loop → frame.start_pc.val ≤ before.function.code.length)) :
      frame.height.val+(frameBranchWidth frame).val+1 ≤ after.height.val ∧
        (frame.kind = .Loop → frame.start_pc.val ≤ after.function.code.length) :=
    ⟨by simpa only [height] using old.1,fun loop => (old.2 loop).trans growth⟩
  cases effect with
  | loop selected original source found selectedPosition kind operands code frames =>
    rw [frames] at lookup
    exact retain (held depth member index frame lookup position)
  | forward selected original source fixups site found selectedPosition kind operands code frames appended sitePosition =>
    by_cases same : selected.val = index.val
    · have bound := (List.getElem?_eq_some_iff.mp found).1
      have actual := lookup
      rw [frames,← same,List.getElem?_set_self bound] at actual
      have equal := Option.some.inj actual
      subst frame
      have old := held depth member selected original found (by simpa only [same] using position)
      apply retain
      exact old
    · rw [frames,List.getElem?_set_ne same] at lookup
      exact retain (held depth member index frame lookup position)

end Itasca.Runtime.Compiler

end

/-! ## JumpTableBounds -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Every stored jump-table target is inside the currently emitted code. -/
def JumpTableBounds (compiler : runtime.compiler.FunctionCompiler A) : Prop :=
  ∀ target ∈ compiler.function.jump_tables.val, target.val < compiler.function.code.val.length

/-- Table preservation and code growth retain all existing target bounds. -/
theorem JumpTableBounds.retained {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (held : JumpTableBounds before)
    (tables : after.function.jump_tables.val = before.function.jump_tables.val)
    (code : before.function.code.val.length ≤ after.function.code.val.length) : JumpTableBounds after := by
  intro target member
  rw [tables] at member
  exact (held target member).trans_le code

/-- Successful emission retains side-table targets while extending code. -/
theorem Emitted.jump_table_bounds {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {instruction : runtime.bytecode.Instr} (emitted : Emitted before after instruction)
    (held : JumpTableBounds before) : JumpTableBounds after := by
  obtain ⟨budget,code,sources,rfl,appended,_⟩ := emitted
  intro target member
  have bounded := held target member
  change target.val < code.val.length
  rw [appended]
  simp only [List.length_append,List.length_singleton]
  omega

/-- Actual observation leaves both code and jump-table targets fixed. -/
theorem compiler_observe_jump_table_bounds {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (held : JumpTableBounds before)
    (called : runtime.compiler.FunctionCompiler.observe ops before state = .ok (.Ok (),after)) :
    JumpTableBounds after := by
  apply held.retained (after := after) (congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called))
    (compiler_observe_code_mono ops law before after state (.Ok ()) called)

end Itasca.Runtime.Compiler

end

/-! ## StartJumpTableBounds -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Actual construction and function-start leave the jump table empty, so no
completed function or source-body execution premise is needed for its bounds. -/
theorem compiler_start_jump_table_bounds {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (signatures : Slice runtime.compiler.Signature)
    (functionSlots : Slice U32) (budget : runtime.compiler.Budget A) (batchStart : Usize)
    (initial started : runtime.compiler.FunctionCompiler A)
    (ctx : Itasca.code.Context) (typeIndex : U32) (signature : runtime.compiler.Signature)
    (bodyBegin bodyEnd : Usize)
    (lookup : signatures.val[typeIndex.val]? = some signature)
    (beginFits : batchStart.val+bodyBegin.val ≤ Usize.max)
    (endFits : batchStart.val+bodyEnd.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (begun : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial ctx typeIndex bodyBegin bodyEnd = .ok (.Ok (),started)) : JumpTableBounds started := by
  have newPost := compiler_new ops signatures functionSlots budget batchStart
  rw [created,WP.spec_ok] at newPost
  obtain ⟨layout,emptyLocals,emptyOperands,emptyMaps,emptyFrames,emptyCode,reachable,sigs,widths,coordinate⟩ := newPost
  have startPost := compiler_function_start_raw ops law initial ctx typeIndex signature bodyBegin bodyEnd
    (by simpa only [sigs] using lookup) (by simpa only [coordinate] using beginFits)
    (by simpa only [coordinate] using endFits) emptyLocals layout emptyOperands
    (by simp [emptyMaps]; scalar_tac) (by simp [emptyFrames]; scalar_tac)
  rw [begun,WP.spec_ok] at startPost
  obtain ⟨_,_,_,tables⟩ := startPost rfl
  have jumpTables := congrArg CompilerTables.jumpTables tables
  change started.function.jump_tables.val = initial.function.jump_tables.val at jumpTables
  have initialEmpty : initial.function.jump_tables.val = [] := by
    simp only [runtime.compiler.FunctionCompiler.new,Result.ok.injEq] at created
    subst initial
    rfl
  intro target member
  rw [jumpTables,initialEmpty] at member
  cases member

end Itasca.Runtime.Compiler

end
