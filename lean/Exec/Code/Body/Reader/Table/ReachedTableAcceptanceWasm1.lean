import Exec.Code.Body.Reader.Table.ReadTableAvailabilityWasm1
import Exec.Code.Body.Reader.Table.ReaderTableDispatchWasm1
import Exec.Code.Body.Reader.Table.ReaderTableDecoded
import Exec.Code.Local.Callbacks.Table.CompilerTableBoundary
import Exec.Code.Local.Capacity.BranchTableAvailability
import Exec.Code.Body.Control.Table.StructuredBranchIfLayoutWithTables

namespace Exec.Code
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- The collecting Wasm 1 table reader and final lowering callback accept from
independent validation, source operand geometry, and numeric resource bounds. -/
theorem reached_br_table_available_wasm1 {jumpTables : List U32} {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A V : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (source : code.OpVisitor V) (before after : V) (out : code.OpIterState)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial compiler
      types functions returns locals parents current st.vals.val p.start.val)
    (same : ReaderScopeZipperWasm1 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm1.Frames.Saved.vals))
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (depths : List U32) (fallback : U32)
    (encoded : BrTable.Decoded data st.pos depths fallback out.pos)
    (capacity : CallbackCapacity compiler out bound (2*(depths.length+1)+1))
    (branches : compiler.budget.branches.val+(depths.length+1) ≤ compiler.budget.limits.max_branch_table_entries.val)
    (scratchCapacity : depths.length+1 ≤ Usize.max) (scratchReserve : depths.length+1 ≤ bound)
    (depthCount : depths.length+1 ≤ U32.max)
    (boundary : CompilerTableBoundary compiler)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (reference : code.step source st data env ctx code.OP_BR_TABLE before = .ok (.Ok (),out,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_BR_TABLE compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => match counter with
            | .instructions => 2*(depths.length+1)+1 | .branches => depths.length+1 | _ => 0) ⦄ := by
  obtain ⟨actual,common,middle,read,callback⟩ := reader_table_dispatch_wasm1 source st out data env ctx before after reference
  obtain ⟨actualDepths,actualDecoded⟩ := reader_table_decoded_wasm1 source p before middle out actual common read
  obtain ⟨depthsEq,fallbackEq,_⟩ := actualDecoded.unique encoded
  subst actualDepths actual
  have geometry : ∃ selector : U32,
      (compiler.reachable = true → compiler.before.val[compiler.before.val.length-1]? = some selector) ∧
      (compiler.reachable = true → ∀ depth ∈ depths++[fallback], depth.val < compiler.frames.val.length) ∧
      (compiler.reachable = true → ∀ depth ∈ depths++[fallback],
        ∀ (frameIndex : Usize) (frame : runtime.compiler.Frame), compiler.frames.val[frameIndex.val]? = some frame →
          frameIndex.val+depth.val+1 = compiler.frames.val.length →
          (frameBranchWidth frame).val+1 ≤ compiler.height.val) := by
    by_cases live : compiler.reachable = true
    · obtain ⟨stack,stackEq,inputs⟩ := reader_table_inputs_wasm1 source p same fronts invariant.entryChain
        (invariant.live live).1 (invariant.known live) (monomorphic live) before middle out fallback common
        depths fallback out.pos encoded read
      have layout := (invariant.live live).2.layout
      rw [stackEq] at layout
      obtain ⟨selector,selectorAt,_⟩ := layout.condition
      refine ⟨selector,fun _ => selectorAt,?_,?_⟩
      · intro _ depth member
        obtain ⟨scope,discarded,selected,_,input⟩ := inputs depth member
        have selected' : (current :: parents.reverse)[depth.val]? = some scope := by
          simpa only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append] using selected
        obtain ⟨frameIndex,frame,sourceAt,condition,found,position,_⟩ :=
          invariant.branch_if_coordinates live depth.val scope selected' discarded stackEq input
        omega
      · intro _ depth member frameIndex frame found position
        obtain ⟨scope,discarded,selected,_,input⟩ := inputs depth member
        have selected' : (current :: parents.reverse)[depth.val]? = some scope := by
          simpa only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append] using selected
        obtain ⟨actualIndex,actualFrame,sourceAt,condition,actualFound,actualPosition,shape,_,_,width,_⟩ :=
          invariant.branch_if_coordinates live depth.val scope selected' discarded stackEq input
        have sameIndex : frameIndex = actualIndex := UScalar.eq_of_val_eq (by omega)
        subst actualIndex
        rw [found] at actualFound
        have sameFrame := Option.some.inj actualFound
        subst actualFrame
        calc
          _ = slots scope.branchTypes+1 := congrArg (fun n => n+1) shape.toScopeFrameShape.branch_width
          _ ≤ compiler.height.val := by omega
    · exact ⟨0#u32,(fun impossible => False.elim (live impossible)),
        (fun impossible => False.elim (live impossible)),(fun impossible => False.elim (live impossible))⟩
  obtain ⟨selector,selectorAt,depthsValid,widths⟩ := geometry
  obtain ⟨⟨reply,final,collected⟩,readCalled,accepted,sameOut,collectedPrefix,exactBuffer⟩ := WP.spec_imp_exists
    (compiler_read_br_table_available_wasm1 ops law bound allocation source before middle compiler st out data
      fallback common depths encoded boundary.depths (by omega) (by omega) (by omega) read)
  dsimp only at accepted sameOut collectedPrefix exactBuffer
  subst reply final
  obtain ⟨budget,buffer,frame,length,effect⟩ := collectedPrefix
  have unchangedInstructions := effect.uncharged .instructions (by simp)
  change budget.instructions = compiler.budget.instructions at unchangedInstructions
  have sameLimits := effect.limits
  have bufferLength : collected.table_depths.val.length = depths.length := by rw [exactBuffer]
  have capacityCurrent : CallbackCapacity collected out bound (2*(depths.length+1)+1) := by
    rw [frame]
    refine ⟨capacity.pc,capacity.codeCapacity,capacity.sourceCapacity,capacity.codeReserve,capacity.sourceReserve,
      capacity.coordinate,?_,capacity.operands,capacity.slots⟩
    change budget.instructions.val+(2*(depths.length+1)+1) ≤ budget.limits.max_instructions.val
    rw [unchangedInstructions,sameLimits]
    exact capacity.instructions
  have branchRoom : collected.budget.branches.val < collected.budget.limits.max_branch_table_entries.val := by
    have used := (effect.counts .branches).2
    simp only [ChargeCounter.used,ite_true] at used
    rw [frame]
    simp only
    rw [sameLimits]
    omega
  have available := compiler_on_br_table_available ops law bound allocation collected out fallback
    (Control.resultView common) selector
    (by simpa only [bufferLength] using capacityCurrent) branchRoom
    (by change collected.table_depths.val.length < Usize.max; omega)
    (by change collected.table_depths.val.length+1 ≤ bound; omega)
    (by omega)
    (by simpa only [SourceAligned,frame] using (fun _ => invariant.sources))
    (by intro live depth member
        rw [exactBuffer] at member
        simpa only [frame] using depthsValid (by simpa only [frame] using live) depth member)
    (by intro live depth member
        rw [exactBuffer] at member
        simpa only [frame] using widths (by simpa only [frame] using live) depth member)
    (by simpa only [frame] using (fun _ => fixups))
    (by simpa only [frame] using (fun _ => boundary.targets))
    (by simpa only [frame] using selectorAt)
  obtain ⟨⟨status,compiled⟩,called,ok,lowerEffect⟩ := WP.spec_imp_exists available
  dsimp only at ok lowerEffect
  subst status
  apply WP.exists_imp_spec
  refine ⟨(.Ok (),out,compiled),?_,rfl,rfl,?_⟩
  · rw [code.step_br_table.dispatch,readCalled]
    simp [CoreVisitor.run,core.result.Result.Insts.CoreOpsTry.branch,called,code.visit]
  · rw [frame] at lowerEffect
    exact (effect.trans lowerEffect).weaken (by
      intro counter
      have bufferLength' : buffer.val.length = depths.length := by simpa only [frame] using bufferLength
      cases counter <;> simp [bufferLength'])

end Exec.Code
