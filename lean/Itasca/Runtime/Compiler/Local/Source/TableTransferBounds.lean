import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableFrames
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableArguments

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
