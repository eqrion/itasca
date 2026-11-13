import Itasca.Runtime.Compiler.Local.Lowering.Control.LoweringTrap
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackBounds
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchSafety
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupBudget
import Itasca.Runtime.Compiler.Local.Relations.Operations.PairSafety
import Itasca.Runtime.Compiler.Local.Lowering.Calls.LoweringCall
import Itasca.Runtime.Compiler.Local.Relations.Calls.StatefulCallbacks
import Itasca.Runtime.Compiler.Local.Relations.Calls.IndirectCallMetadata
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulLowered

/-!
Sections, each formerly its own module: BranchCallbackSafety, CallSafety, IndirectCallInversion, IndirectCallExclusions.
-/

/-! ## BranchCallbackSafety -/

section

/-!
Normal return of direct and conditional branch callbacks. The conditional proof covers underflow and empty/nonempty transfer cases before lifting to actual callback dispatch.
-/

/-! ## Branch If Safety -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

private theorem branch_if_underflow_total {A} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (frame : runtime.compiler.Frame)
    (index : Usize) (depth : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (underflow : compiler.height.val <
      (match frame.kind with | .Loop => frame.params | _ => frame.results).val + 1) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true ⦃ _ => True ⦄ := by
  cases kindEq : frame.kind
  all_goals simp only [kindEq] at underflow
  all_goals
    unfold runtime.compiler.control.FunctionCompiler.branch
    step as ⟨last, lastValue⟩
    step as ⟨d, dValue⟩
    step as ⟨actualIndex, indexValue⟩
    have indexEq : actualIndex = index := by
      apply UScalar.eq_of_val_eq
      simp [alloc.vec.Vec.len] at lastValue
      scalar_tac
    subst actualIndex
    have inBounds := (List.getElem?_eq_some_iff.mp lookup).1
    step as ⟨found, foundValue⟩
    have foundEq : found = frame := foundValue.trans (List.getElem?_eq_some_iff.mp lookup).2
    rw [foundEq]
    simp only [kindEq, bind_ok, Bool.false_eq_true, ite_false, ite_true]
    step as ⟨sum, sumValue⟩
    cases sum with
    | none => simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | some sum =>
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step as ⟨source, sourceValue⟩
      cases source with
      | none => simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | some source => simp at sumValue sourceValue; omega

@[step] theorem compiler_branch_if_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth condition : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (pcBound : compiler.function.code.val.length + 3 < 2^32)
    (codeFits : compiler.function.code.val.length + 3 ≤ Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length + 3 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true ⦃ _ => True ⦄ := by
  let resume : U32 := UScalar.ofNatCore (compiler.function.code.val.length + 3) pcBound
  by_cases loop : frame.kind = .Loop
  · by_cases enough : frame.params.val + 1 ≤ compiler.height.val
    · let source : U32 := UScalar.ofNatCore (compiler.height.val - (frame.params.val + 1)) (by scalar_tac)
      have sourcePosition : source.val + frame.params.val + 1 = compiler.height.val := by
        change compiler.height.val - (frame.params.val + 1) + frame.params.val + 1 = compiler.height.val
        omega
      by_cases elided : frame.params = 0#u32 ∨ source = frame.height
      · exact WP.spec_mono (branch_if_elided_loop ops law compiler frame index depth source condition
          lookup position loop elided sourcePosition conditionAt (by omega) (by omega) coordinateFits) (by simp)
      · have nonempty : frame.params ≠ 0#u32 := fun h => elided (.inl h)
        have different : source ≠ frame.height := fun h => elided (.inr h)
        exact WP.spec_mono (branch_if_transfer_loop ops law compiler frame index depth source condition resume
          lookup position loop nonempty different sourcePosition conditionAt rfl codeFits sourceFits coordinateFits) (by simp)
    · exact branch_if_underflow_total ops compiler frame index depth lookup position (by simp [loop]; omega)
  · by_cases enough : frame.results.val + 1 ≤ compiler.height.val
    · let source : U32 := UScalar.ofNatCore (compiler.height.val - (frame.results.val + 1)) (by scalar_tac)
      have sourcePosition : source.val + frame.results.val + 1 = compiler.height.val := by
        change compiler.height.val - (frame.results.val + 1) + frame.results.val + 1 = compiler.height.val
        omega
      by_cases elided : frame.results = 0#u32 ∨ source = frame.height
      · exact WP.spec_mono (branch_if_elided_forward ops law compiler frame index depth source condition
          lookup position loop elided sourcePosition conditionAt fixupsFit (by omega) (by omega) coordinateFits) (by simp)
      · have nonempty : frame.results ≠ 0#u32 := fun h => elided (.inl h)
        have different : source ≠ frame.height := fun h => elided (.inr h)
        exact WP.spec_mono (branch_if_transfer_forward ops law compiler frame index depth source condition resume
          lookup position loop nonempty different sourcePosition conditionAt rfl fixupsFit codeFits sourceFits coordinateFits) (by simp)
    · exact branch_if_underflow_total ops compiler frame index depth lookup position (by cases kindEq : frame.kind <;> simp_all)

end Itasca.Runtime.Compiler

end

/-! ## Branch If Safety Complete -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
private theorem branch_if_empty_total {A} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (frame : runtime.compiler.Frame)
    (index : Usize) (depth : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (empty : compiler.before.val = []) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true ⦃ _ => True ⦄ := by
  cases kindEq : frame.kind
  all_goals
    unfold runtime.compiler.control.FunctionCompiler.branch
    step as ⟨last, lastValue⟩
    step as ⟨d, dValue⟩
    step as ⟨actualIndex, indexValue⟩
    have indexEq : actualIndex = index := by
      apply UScalar.eq_of_val_eq
      simp [alloc.vec.Vec.len] at lastValue
      scalar_tac
    subst actualIndex
    have inBounds := (List.getElem?_eq_some_iff.mp lookup).1
    step as ⟨found, foundValue⟩
    have foundEq : found = frame := foundValue.trans (List.getElem?_eq_some_iff.mp lookup).2
    rw [foundEq]
    simp only [kindEq, bind_ok, Bool.false_eq_true, ite_false, ite_true]
    step as ⟨sum, sumValue⟩
    cases sum with
    | none => simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | some sum =>
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step as ⟨source, sourceValue⟩
      cases source with
      | none => simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | some source =>
        simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          runtime.compiler.FunctionCompiler.operand, runtime.compiler.operand_at,
          alloc.vec.Vec.deref, Slice.len, empty,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

@[step] theorem compiler_branch_if_total_raw {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (pcBound : compiler.function.code.val.length + 3 < 2^32)
    (codeFits : compiler.function.code.val.length + 3 ≤ Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length + 3 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true ⦃ _ => True ⦄ := by
  by_cases empty : compiler.before.val = []
  · exact branch_if_empty_total ops compiler frame index depth lookup position empty
  · have positive : 0 < compiler.before.val.length := List.length_pos_iff.mpr empty
    let condition := compiler.before.val[compiler.before.val.length-1]
    have conditionAt : compiler.before.val[compiler.before.val.length-1]? = some condition := by
      simp [condition,show compiler.before.val.length-1 < compiler.before.val.length by omega]
    exact compiler_branch_if_total ops law compiler frame index depth condition lookup position conditionAt
      fixupsFit pcBound codeFits sourceFits coordinateFits
end Itasca.Runtime.Compiler

end

/-! ## Branch Callback Safety -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem branch_depth_target (frames : alloc.vec.Vec runtime.compiler.Frame) (depth : U32)
    (bound : depth.val < frames.val.length) :
    ∃ index : Usize, ∃ frame, frames.val[index.val]? = some frame ∧
      index.val + depth.val + 1 = frames.val.length := by
  let index := Usize.ofNatCore (frames.val.length-depth.val-1) (by
    have h := (alloc.vec.Vec.len frames).hBounds
    change frames.val.length < 2^UScalarTy.Usize.numBits at h
    omega)
  have inside : index.val < frames.val.length := by
    change frames.val.length-depth.val-1 < frames.val.length
    omega
  refine ⟨index,frames.val[index.val],by simp [inside],?_⟩
  change frames.val.length-depth.val-1+depth.val+1=frames.val.length
  omega

@[step] theorem compiler_br_callback_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (types : Itasca.signature.ResultType)
    (depthFits : depth.val < compiler.frames.val.length)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (codeFits : compiler.function.code.val.length+2 ≤ Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length+2 ≤ Usize.max)
    (coordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops compiler state depth types ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
  split
  · obtain ⟨index,frame,lookup,position⟩ := branch_depth_target compiler.frames depth depthFits
    step with compiler_branch_total ops law compiler frame index depth lookup position
      (fixups.lookup lookup (by omega)) codeFits sourceFits coordinate as ⟨status,after⟩
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      exact compiler_observe_stack ops law {after with reachable := false} state
  · exact compiler_observe_stack ops law compiler state

@[step] theorem compiler_br_if_callback_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (types : Itasca.signature.ResultType)
    (depthFits : depth.val < compiler.frames.val.length)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (pcBound : compiler.function.code.val.length+3 < 2^32)
    (codeFits : compiler.function.code.val.length+3 ≤ Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length+3 ≤ Usize.max)
    (coordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops compiler state depth types ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
  split
  · obtain ⟨index,frame,lookup,position⟩ := branch_depth_target compiler.frames depth depthFits
    step with compiler_branch_if_total_raw ops law compiler frame index depth lookup position
      (fixups.lookup lookup (by omega)) pcBound codeFits sourceFits coordinate as ⟨status,after⟩
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      exact compiler_observe_stack ops law after state
  · exact compiler_observe_stack ops law compiler state
end Itasca.Runtime.Compiler

end

end

/-! ## CallSafety -/

section

/-! Call callback safety includes checked arithmetic and operand rejections. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

@[step] theorem compiler_call_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (index : U32)
    (indexBound : index.val < compiler.func_param_slots.val.length)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 16#u16 index 0#u32 0#u128 ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  by_cases reachable : compiler.reachable = true
  · have run : runtime.compiler.lower.FunctionCompiler.op ops compiler state 16#u16 index 0#u32 0#u128 = (do
        let i ← lift (UScalar.cast .Usize index)
        let slots ← Slice.index_usize compiler.func_param_slots i
        let o ← lift (U32.checked_sub compiler.height slots)
        let r ← core.option.Option.ok_or o Itasca.error.VisitError.OutOfMemory
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val =>
          runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state (.Call index val)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame Itasca.error.VisitError) residual
          Result.ok (r1, compiler)) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos reachable]
      rfl
    rw [run]
    step as ⟨i, hi⟩
    have bound : i.val < compiler.func_param_slots.length := by scalar_tac
    step as ⟨slots, hslots⟩
    cases difference : U32.checked_sub compiler.height slots with
    | none => simp [lift,difference,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | some base =>
      simp only [difference,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,lift,bind_ok]
      exact finish_op_observed ops law compiler state _ codeFits sourceFits coordinateFits
  · unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_neg reachable]
    exact compiler_observe_stack ops law compiler state

@[step] theorem compiler_indirect_call_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (typeIndex tableIndex : U32)
    (indexBound : typeIndex.val < compiler.signatures.val.length)
    (pairFits : compiler.function.indirect.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 17#u16 typeIndex tableIndex 0#u128 ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  by_cases reachable : compiler.reachable = true
  · rw [lower_indirect_call_dispatch ops compiler state typeIndex tableIndex reachable]
    unfold indirectCallLowering
    step as ⟨i, hi⟩
    have bound : i.val < compiler.signatures.length := by scalar_tac
    step as ⟨signature, hsignature⟩
    cases added : U32.checked_add signature.param_slots 1#u32 with
    | none => simp [lift,added,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | some total =>
      simp only [added,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,lift,bind_ok]
      cases subtracted : U32.checked_sub compiler.height total with
      | none => simp [lift,subtracted,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | some base =>
        simp only [subtracted,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,lift,bind_ok]
        step with compiler_pair_total ops law compiler tableIndex typeIndex pairFits
          as ⟨answer,paired,budget,pairs,effect⟩
        subst paired
        cases answer with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok entry =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
          step with compiler_operand_total ops _ 1#usize as ⟨answer,_⟩
          cases answer with
          | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok selector =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
            exact finish_op_observed ops law _ state _ codeFits sourceFits coordinateFits
  · unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_neg reachable]
    exact compiler_observe_stack ops law compiler state

@[step] theorem compiler_on_call_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (index : U32)
    (indexBound : index.val < compiler.func_param_slots.val.length)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_call compiler state index ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ :=
  compiler_call_total ops law compiler state index indexBound codeFits sourceFits coordinateFits

@[step] theorem compiler_on_call_indirect_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (typeIndex tableIndex : U32)
    (indexBound : typeIndex.val < compiler.signatures.val.length)
    (pairFits : compiler.function.indirect.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_call_indirect compiler state typeIndex tableIndex ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ :=
  compiler_indirect_call_total ops law compiler state typeIndex tableIndex indexBound pairFits codeFits sourceFits coordinateFits

end Itasca.Runtime.Compiler

end

/-! ## IndirectCallInversion -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std

theorem IndirectCallEmission.invert {pairs C before emitted after table type}
    (head : IndirectCallEmission pairs C before (.CALL_INDIRECT (.mk_uN table) (.mk_uN type)) emitted after) :
    ∃ (front params results : List valtype) (typeIndex tableIndex entry index base : U32) (bounds : limits),
      typeIndex.val = type ∧ tableIndex.val = table ∧
      before = (front ++ params) ++ [.I32] ∧ after = front ++ results ∧
      emitted = [.CallIndirect entry index base] ∧
      C.TYPES[type]? = some ⟨.mk_list params,.mk_list results⟩ ∧
      C.TABLES[table]? = some (.mk_tabletype bounds .FUNCREF) ∧
      pairs[entry.val]? = some (tableIndex,typeIndex) ∧
      base.val = slots C.LOCALS + slots front ∧ index.val = base.val + slots params := by
  generalize sourceEq : instr.CALL_INDIRECT (.mk_uN table) (.mk_uN type) = source at head
  cases head with
  | call front params results typeIndex tableIndex entry index base bounds signature tableFound pair basePosition indexPosition =>
    cases sourceEq
    exact ⟨front,params,results,typeIndex,tableIndex,entry,index,base,bounds,rfl,rfl,rfl,rfl,rfl,
      signature,tableFound,pair,basePosition,indexPosition⟩
end Itasca.Runtime.Compiler

end

/-! ## IndirectCallExclusions -/

section

namespace Itasca.Runtime.Compiler

theorem linear_emission_not_indirect {locals before emitted after table type}
    (head : LinearEmission locals before (.CALL_INDIRECT table type) emitted after) : False := by
  generalize equal : instr.CALL_INDIRECT table type = instruction at head
  cases head with
  | binary stack ty op a b left right => cases op <;> cases equal
  | numeric stack op a b left right => cases op <;> cases equal
  | _ => cases equal

theorem scalar_emission_not_indirect {C before emitted after table type}
    (head : ScalarEmission C before (.CALL_INDIRECT table type) emitted after) : False := by
  generalize equal : instr.CALL_INDIRECT table type = instruction at head
  cases head with
  | linear h => rw [← equal] at h; exact linear_emission_not_indirect h
  | load stack op argument address offset memory available sourceOffset slot => cases op <;> cases equal
  | store stack op argument address value offset memory available sourceOffset addressSlot valueSlot => cases op <;> cases equal
  | float stack op left right leftSlot rightSlot => cases op <;> cases equal
  | _ => cases equal

theorem stateful_emission_not_indirect {pairs C before emitted after table type}
    (head : StatefulEmission pairs C before (.CALL_INDIRECT table type) emitted after) : False := by
  generalize equal : instr.CALL_INDIRECT table type = instruction at head
  cases head with
  | instruction stack input output op signature first second a b entry firstSlot secondSlot arguments pair =>
    cases op <;> cases equal
end Itasca.Runtime.Compiler

end
