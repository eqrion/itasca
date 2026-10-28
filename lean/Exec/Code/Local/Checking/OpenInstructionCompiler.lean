import Exec.Code.Local.Relations.Common.FunctionStartRaw
import Exec.Code.Local.Relations.Common.FunctionEntry
import Exec.Code.Local.Checking.OpenInstructionAppend

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- A pending branch site has a physical owner that will patch its target.
The code check also covers instructions outside semantically reachable paths. -/
def PendingInstructionSite (compiler : runtime.compiler.FunctionCompiler A) (index : Nat) : Prop :=
  ∃ frame ∈ compiler.frames.val, ∃ site : Usize, site.val = index ∧
    (frame.if_pc = some site ∨ site ∈ frame.fixups.val)

def CompilerInstructionPrefix (compiler : runtime.compiler.FunctionCompiler A) : Prop :=
  OpenInstructionPrefix compiler.function (PendingInstructionSite compiler)

/-- Actual fresh construction and function-start establish the empty checked
prefix without assuming an accepted instruction trace or function certificate. -/
theorem compiler_start_instruction_prefix {A : Type} (ops : runtime.platform.Alloc A)
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
      ops initial ctx typeIndex bodyBegin bodyEnd = .ok (.Ok (),started)) : CompilerInstructionPrefix started := by
  have newPost := compiler_new ops signatures functionSlots budget batchStart
  rw [created,WP.spec_ok] at newPost
  obtain ⟨layout,emptyLocals,emptyOperands,emptyMaps,emptyFrames,emptyCode,reachable,sigs,widths,coordinate⟩ := newPost
  have startPost := compiler_function_start_raw ops law initial ctx typeIndex signature bodyBegin bodyEnd
    (by simpa only [sigs] using lookup) (by simpa only [coordinate] using beginFits)
    (by simpa only [coordinate] using endFits) emptyLocals layout emptyOperands
    (by simp [emptyMaps]; scalar_tac) (by simp [emptyFrames]; scalar_tac)
  rw [begun,WP.spec_ok] at startPost
  obtain ⟨_,code,_⟩ := startPost rfl
  intro index instruction found
  rw [code,emptyCode] at found
  simp at found

end Itasca.Runtime.Code
