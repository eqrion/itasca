import Exec.Code.Local.Callbacks.Table.CompilerTableBoundary
import Exec.Code.Body.Reader.Table.TableLoopAvailability
import Exec.Code.Body.Reader.Table.ReaderTableInputsWasm2
import Exec.Code.Body.Control.Table.StructuredBranchIfLayout
import Itasca.Wasm2.Trace.TableBytes

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Full Wasm 2 table reading accepts from independent source validation,
retained frame/operand geometry, and explicit numeric resource bounds. Both
live and dead tables include every label and the separately decoded fallback. -/
theorem reached_profile_br_table_available_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A V : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (source : code.OpVisitor V) (before after : V) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial compiler
      types functions returns locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (depths : List U32) (fallback : U32)
    (encoded : BrTable.Decoded data st.core.pos depths fallback out.core.pos)
    (capacity : CallbackCapacity compiler out.core bound (2*(depths.length+1)+1))
    (branches : compiler.budget.branches.val+(depths.length+1) ≤ compiler.budget.limits.max_branch_table_entries.val)
    (scratchCapacity : depths.length+1 ≤ Usize.max) (scratchReserve : depths.length+1 ≤ bound)
    (depthCount : depths.length+1 ≤ U32.max)
    (boundary : CompilerTableBoundary compiler)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (reference : code.step_profile source st data env ctx index .Wasm2 14#u8 before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 14#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => match counter with
            | .instructions => 2*(depths.length+1)+1 | .branches => depths.length+1 | _ => 0) ⦄ := by
  rw [Wasm2.CallbackTrace.dispatch_br_table] at reference ⊢
  obtain ⟨C,outer,spine,header,base,typed,controls,blocks,values⟩ := p.opened
  obtain ⟨count,first,selectorType,popped,all,arity,countDecoded,popCall,popControls,popPos,
    countEq,allDecoded,targets⟩ := reader_table_targets_wasm2 source before after st out data env
      _ p.current.ctrl controls p.opened.shape.core reference
  obtain ⟨sourceCount,sourceFirst,last,countSource,lengthSource,labelsSource,defaultSource⟩ := encoded
  obtain ⟨rfl,rfl⟩ := countDecoded.unique countSource
  have allEq : all = depths++[fallback] := (allDecoded.unique (labelsSource.snoc defaultSource)
    (by simp only [List.length_append,List.length_singleton]; omega)).1
  have geometry : ∃ selector : U32,
      (compiler.reachable = true → compiler.before.val[compiler.before.val.length-1]? = some selector) ∧
      (compiler.reachable = true → ∀ depth ∈ all, depth.val < compiler.frames.val.length) ∧
      (compiler.reachable = true → ∀ depth ∈ all,
        ∀ (frameIndex : Usize) (frame : runtime.compiler.Frame), compiler.frames.val[frameIndex.val]? = some frame →
          frameIndex.val+depth.val+1 = compiler.frames.val.length →
          (frameBranchWidth frame).val+1 ≤ compiler.height.val) := by
    by_cases live : compiler.reachable = true
    · have encoded : BrTable.Decoded data st.core.pos depths fallback out.core.pos :=
        ⟨count,first,last,countSource,lengthSource,labelsSource,defaultSource⟩
      obtain ⟨stack,stackEq,inputs⟩ := reader_table_inputs_wasm2 source p same fronts invariant.entryChain
        (invariant.live live).1 (invariant.known live) (monomorphic live) before after out depths fallback
        out.core.pos encoded reference
      have layout := (invariant.live live).2.layout
      rw [stackEq] at layout
      obtain ⟨selector,selectorAt,_⟩ := layout.condition
      refine ⟨selector,fun _ => selectorAt,?_,?_⟩
      · intro _ depth member
        rw [allEq] at member
        obtain ⟨scope,discarded,selected,_,input⟩ := inputs depth member
        have selected' : (current :: parents.reverse)[depth.val]? = some scope := by
          simpa only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append] using selected
        obtain ⟨frameIndex,frame,sourceAt,condition,found,position,_⟩ :=
          invariant.branch_if_coordinates live depth.val scope selected' discarded stackEq input
        omega
      · intro _ depth member frameIndex frame found position
        rw [allEq] at member
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
  have poppedShape := code.pop_with_type.total {st.core with pos := first} .I32
    (show Control.Shape {st.core with pos := first} from ⟨p.opened.shape.core.ordered,p.opened.shape.core.bounded⟩)
  rw [popCall,WP.spec_ok] at poppedShape
  have readCount := reader.read_u32_leb.complete data st.core.pos count first countSource
  unfold code.branch_table_with at reference ⊢
  rw [readCount] at reference ⊢
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry] at reference ⊢
  rw [popCall] at reference ⊢
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry] at reference ⊢
  have accepted := compiler_table_reader_loop_available ops law bound allocation source before after compiler popped out
    data env count all poppedShape.1 boundary.depths countEq (by simpa only [popPos] using allDecoded)
    (by simpa only [lengthSource] using capacity) (by simpa only [lengthSource] using branches)
    (by omega) (by omega) (by omega) (fun _ => invariant.sources) depthsValid widths
    (fun _ => fixups) (fun _ => boundary.targets) selector selectorAt reference
  obtain ⟨⟨reply,resultOut,targetAfter⟩,called,ok,sameResult,effect⟩ := WP.spec_imp_exists accepted
  dsimp only at ok sameResult effect
  subst reply resultOut
  apply WP.exists_imp_spec
  refine ⟨(.Ok (),out,targetAfter),called,rfl,rfl,?_⟩
  exact effect.weaken (by intro counter; cases counter <;> simp [lengthSource])

end Itasca.Runtime.Code
