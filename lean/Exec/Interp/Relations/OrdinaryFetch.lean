import Exec.Interp.Relations.PrefixDispatch
import Exec.Code.Local.Control.Common.StructuredComposition
import Exec.Interp.Control.StructuredPoint

namespace Exec.Interp
open Aeneas.Std

/-- Operations handled by ordinary dispatch, excluding erased syntax and
function-stack transitions. -/
def OrdinarySource : instr → Prop
  | .NOP | .DROP | .BLOCK _ _ | .CALL _ | .RETURN => False
  | _ => True

theorem PrefixInstruction.move (ty : valtype) (dst src : U32) :
    PrefixInstruction (Code.move ty dst src) := by
  unfold Code.move
  split
  · exact .copy2 _ _
  · exact .copy _ _

theorem PrefixInstruction.transfer (dst src count : U32) :
    PrefixInstruction (Code.transferInstruction dst src count) := by
  unfold Code.transferInstruction
  split
  · exact .copy _ _
  · split
    · exact .copy2 _ _
    · exact .copyN _ _ _

theorem linear_first_prefix {locals before op emitted after}
    (head : Code.LinearEmission locals before op emitted after) (ordinary : OrdinarySource op) :
    ∃ instruction, emitted[0]? = some instruction ∧ PrefixInstruction instruction := by
  cases head with
  | nop => exact False.elim ordinary
  | drop => exact False.elim ordinary
  | const32 => exact ⟨_, rfl, .const32 _ _⟩
  | const64 => exact ⟨_, rfl, .const64 _ _⟩
  | binary => exact ⟨_, rfl, .integer _ _ _ _⟩
  | numeric => exact ⟨_, rfl, .numeric _ _ _ _⟩
  | eqz32 => exact ⟨_, rfl, .eqz32 _ _ _⟩
  | eqz64 => exact ⟨_, rfl, .eqz64 _ _ _⟩
  | localGet => exact ⟨_, rfl, .move _ _ _⟩
  | localSet => exact ⟨_, rfl, .move _ _ _⟩
  | localTee => exact ⟨_, rfl, .move _ _ _⟩

theorem branch_first_prefix (dst src count target : U32) :
    ∃ instruction, (Code.branchInstructions dst src count target)[0]? = some instruction ∧
      PrefixInstruction instruction := by
  unfold Code.branchInstructions
  split
  · exact ⟨_, rfl, .jump _⟩
  · exact ⟨_, rfl, .transfer _ _ _⟩

theorem branchIf_first_prefix (dst src count target cond resume : U32) :
    ∃ instruction, (Code.branchIfInstructions dst src count target cond resume)[0]? = some instruction ∧
      PrefixInstruction instruction := by
  unfold Code.branchIfInstructions
  split
  · exact ⟨_, rfl, .jumpNonzero _ _⟩
  · exact ⟨_, rfl, .jumpZero _ _⟩

/-- The retained compiler relation supplies the actual fetched class; callers
do not assume that a dispatch preserves another frame's storage. -/
theorem codeRel_ordinary_fetch {types functions returns locals code labels stack op source pc next output}
    (relation : Code.CodeRel types functions returns locals code labels stack (op :: source) pc next output)
    (ordinary : OrdinarySource op) :
    ∃ instruction, code[pc]? = some instruction ∧ PrefixInstruction instruction := by
  cases relation with
  | linear head fragment rest =>
    obtain ⟨instruction, first, allowed⟩ := linear_first_prefix head ordinary
    exact ⟨instruction, by simpa only [Nat.add_zero] using fragment.fetch first, allowed⟩
  | skip forward fetched rest => exact ⟨_, fetched, .jump _⟩
  | block => exact False.elim ordinary
  | loop signature head body rest bounds => exact ⟨_, head, .loopHead⟩
  | ifElse signature condition guard yes skip no rest bounds => exact ⟨_, guard, .jumpZero _ _⟩
  | branch lookup live layout fragment remaining scope =>
    obtain ⟨instruction, first, allowed⟩ := branch_first_prefix _ _ _ _
    exact ⟨instruction, by simpa only [Nat.add_zero] using fragment.fetch first, allowed⟩
  | branchIf lookup live layout condition fragment rest =>
    obtain ⟨instruction, first, allowed⟩ := branchIf_first_prefix _ _ _ _ _ _
    exact ⟨instruction, by simpa only [Nat.add_zero] using fragment.fetch first, allowed⟩
  | call => exact False.elim ordinary
  | unreachable fetched => exact ⟨_, fetched, .unreachable⟩
  | return_ => exact False.elim ordinary

theorem step_ordinary_prefix {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (functions : List functype)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (f : Abs.AFrame) (op : instr) (source : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (point : StructuredFramePoint raw { f with code := op :: source } compiled functions targets next output)
    (ordinary : OrdinarySource op)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P)
    (returned : runtime.interp.step memory hooks floats allocator exec store platform = .ok out) :
    SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val := by
  obtain ⟨instruction, fetched, allowed⟩ := codeRel_ordinary_fetch point.code.current ordinary
  exact step_prefix memory hooks floats allocator exec store platform index raw inst compiled instruction
    last hf hi hc fetched allowed out returned

end Exec.Interp
