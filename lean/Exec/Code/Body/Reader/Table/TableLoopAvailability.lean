import Exec.Code.Body.Reader.Table.TableLabelCollectionReplay
import Exec.Code.Body.Reader.Table.TableSourceFrame
import Exec.Code.Local.Capacity.BranchTableAvailability

namespace Exec.Code
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- The full actual Wasm 2 table loop accepts an independent source run.
All streamed label callbacks and the final lowering callback are constructed
from source target geometry, exact decoding, and numeric resource bounds. -/
theorem compiler_table_reader_loop_available {A V : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st : code.OpIterState) (out : code.BodyState)
    (data : Slice U8) (env : module.Env) (count : U32) (all : List U32)
    (shape : Control.Shape st) (empty : compiler.table_depths.val = []) (length : all.length = count.val+1)
    (decoded : BrTable.LabelsDecoded data st.pos all out.core.pos)
    (capacity : CallbackCapacity compiler out.core bound (2*(count.val+1)+1))
    (branches : compiler.budget.branches.val+(count.val+1) ≤ compiler.budget.limits.max_branch_table_entries.val)
    (scratchCapacity : count.val+1 ≤ Usize.max) (scratchReserve : count.val+1 ≤ bound)
    (depthCount : count.val+1 ≤ U32.max)
    (aligned : compiler.reachable = true → SourceAligned compiler)
    (depthsValid : compiler.reachable = true → ∀ depth ∈ all, depth.val < compiler.frames.val.length)
    (widths : compiler.reachable = true → ∀ depth ∈ all,
      ∀ (index : Usize) (frame : runtime.compiler.Frame), compiler.frames.val[index.val]? = some frame →
        index.val+depth.val+1 = compiler.frames.val.length → (frameBranchWidth frame).val+1 ≤ compiler.height.val)
    (fixups : compiler.reachable = true → FixupBudget compiler.frames.val compiler.function.code.val.length)
    (tables : compiler.reachable = true → compiler.function.jump_tables.val.length ≤ compiler.function.code.val.length)
    (selector : U32)
    (selectorAt : compiler.reachable = true → compiler.before.val[compiler.before.val.length-1]? = some selector)
    (reference : code.branch_table_with_loop source st data env .Wasm2 before count none .Empty 0#u32 =
      .ok (.Ok (),out,after)) :
    code.branch_table_with_loop (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env .Wasm2 compiler count none .Empty 0#u32 ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => match counter with
            | .instructions => 2*(count.val+1)+1 | .branches => count.val+1 | _ => 0) ⦄ := by
  refine compiler_table_loop_collect_available ops law bound allocation source before after compiler st out data env
    .Wasm2 count all empty length decoded (by omega) (by omega) (by omega)
    (fun _ _ targetAfter => CompilationBudgetEffect compiler.budget targetAfter.budget
      (fun counter => match counter with
        | .instructions => 2*(count.val+1)+1 | .branches => count.val+1 | _ => 0)) ?_ reference
  intro state current marked depth ts sourceBefore sourceAfter collected read values controls mark _
  have markedEq := source_table_loop_marked source data env .Wasm2 count 0#u32 none .Empty st out before after (by simp)
    shape reference state.core marked values controls (read.cursor length) mark
  subst marked
  have whole := read.complete length
  have depthLength := read.length
  obtain ⟨budget,depths,frame,_,effect⟩ := collected
  have unchangedInstructions := effect.uncharged .instructions (by simp)
  change budget.instructions = compiler.budget.instructions at unchangedInstructions
  have sameLimits := effect.limits
  have capacityCurrent : CallbackCapacity current out.core bound (2*(count.val+1)+1) := by
    rw [frame]
    refine ⟨capacity.pc,capacity.codeCapacity,capacity.sourceCapacity,capacity.codeReserve,capacity.sourceReserve,
      capacity.coordinate,?_,capacity.operands,capacity.slots⟩
    change budget.instructions.val+(2*(count.val+1)+1) ≤ budget.limits.max_instructions.val
    rw [unchangedInstructions,sameLimits]
    exact capacity.instructions
  have branchRoom : current.budget.branches.val < current.budget.limits.max_branch_table_entries.val := by
    have used := (effect.counts .branches).2
    simp only [ChargeCounter.used,ite_true] at used
    rw [frame]
    simp only
    rw [sameLimits]
    omega
  have callback := compiler_on_br_table_available ops law bound allocation current out.core depth ts selector
    (by simpa only [depthLength] using capacityCurrent) branchRoom
    (by change current.table_depths.val.length < Usize.max; omega)
    (by change current.table_depths.val.length+1 ≤ bound; omega)
    (by omega)
    (by simpa only [SourceAligned,frame] using aligned)
    (by intro live depth member
        rw [← whole] at member
        simpa only [frame] using depthsValid (by simpa only [frame] using live) depth member)
    (by intro live depth member
        rw [← whole] at member
        simpa only [frame] using widths (by simpa only [frame] using live) depth member)
    (by simpa only [frame] using fixups)
    (by simpa only [frame] using tables)
    (by simpa only [frame] using selectorAt)
  apply WP.spec_mono callback
  intro result held
  refine ⟨held.1,?_⟩
  have bufferLength : depths.val.length = count.val := by simpa only [frame] using depthLength
  have lowerEffect := held.2
  rw [frame] at lowerEffect
  exact (effect.trans lowerEffect).weaken (by intro counter; cases counter <;> simp [bufferLength])

end Exec.Code
