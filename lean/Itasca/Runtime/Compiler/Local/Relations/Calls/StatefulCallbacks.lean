import Itasca.Runtime.Compiler.Local.Relations.Operations.PairSuccess
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulSuccess
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulOpcode
import Itasca.Runtime.Equations

/-!
Sections, each formerly its own module: IndirectCallLowering, IndirectCallOperands, StatefulCallbacks.
-/

/-! ## IndirectCallLowering -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Aeneas.Std.Result Itasca.ResultFacts
set_option maxRecDepth 4096

noncomputable def indirectCallLowering {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (a b : U32) :
    Result (core.result.Result Unit Itasca.error.VisitError × runtime.compiler.FunctionCompiler A) := do
  let i ← lift (UScalar.cast .Usize a)
  let signature ← Slice.index_usize before.signatures i
  let o ← lift (U32.checked_add signature.param_slots 1#u32)
  let r ←
    core.option.Option.ok_or o _root_.Itasca.error.VisitError.OutOfMemory
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let o1 ← lift (U32.checked_sub before.height val)
    let r1 ←
      core.option.Option.ok_or o1
        _root_.Itasca.error.VisitError.OutOfMemory
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let (r2, paired) ←
        runtime.compiler.FunctionCompiler.pair ops before b a
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let r3 ←
          runtime.compiler.FunctionCompiler.operand ops paired
            1#usize
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          runtime.compiler.lower.FunctionCompiler.finish_op
            ops paired state (runtime.bytecode.Instr.CallIndirect
            val2 val3 val1)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r4 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
              residual
          ok (r4, paired)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r3 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
            residual
        ok (r3, paired)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
          residual
      ok (r2, before)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
        residual
    ok (r1, before)

theorem lower_indirect_call_dispatch {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (a b : U32)
    (reachable : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 17#u16 a b 0#u128 =
      indirectCallLowering ops before state a b := by
  unfold runtime.compiler.lower.FunctionCompiler.op
  rw [if_pos reachable]
  rfl

theorem lower_indirect_call_eq {A : Type} (ops : runtime.platform.Alloc A)
    (before paired : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (a b total base entry index : U32) (signature : runtime.compiler.Signature)
    (reachable : before.reachable = true)
    (read : Slice.index_usize before.signatures (UScalar.cast .Usize a) = .ok signature)
    (added : U32.checked_add signature.param_slots 1#u32 = some total)
    (subtracted : U32.checked_sub before.height total = some base)
    (pair : runtime.compiler.FunctionCompiler.pair ops before b a = .ok (.Ok entry,paired))
    (operand : runtime.compiler.FunctionCompiler.operand ops paired 1#usize = .ok (.Ok index)) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 17#u16 a b 0#u128 =
      runtime.compiler.lower.FunctionCompiler.finish_op ops paired state (.CallIndirect entry index base) := by
  rw [lower_indirect_call_dispatch ops before state a b reachable]
  simp only [indirectCallLowering,lift,bind_ok,read,added,subtracted,pair,operand,uncurry_apply_pair,
    core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch]

/-- A successful indirect call exposes the actual pair allocation after its
checked argument-base arithmetic. -/
theorem lower_indirect_call_pair_success {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (a b total base : U32) (signature : runtime.compiler.Signature)
    (reachable : before.reachable = true)
    (read : Slice.index_usize before.signatures (UScalar.cast .Usize a) = .ok signature)
    (added : U32.checked_add signature.param_slots 1#u32 = some total)
    (subtracted : U32.checked_sub before.height total = some base)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 17#u16 a b 0#u128 = .ok (.Ok (),after)) :
    ∃ entry paired, runtime.compiler.FunctionCompiler.pair ops before b a = .ok (.Ok entry,paired) := by
  rw [lower_indirect_call_dispatch ops before state a b reachable] at accepted
  simp only [indirectCallLowering,lift,bind_ok,read,added,subtracted,
    core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch] at accepted
  obtain ⟨⟨result,paired⟩,pair,rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error => simp [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok entry => exact ⟨entry,paired,pair⟩
end Itasca.Runtime.Compiler

end

/-! ## IndirectCallOperands -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- An indirect call's table selector is the final i32 operand; its argument
base is determined by the source parameters, including two-word vectors. -/
theorem indirect_call_arithmetic {A : Type}
    (compiler : runtime.compiler.FunctionCompiler A) (front params : List valtype)
    (signature : runtime.compiler.Signature)
    (layout : CompilerLayout compiler ((front ++ params) ++ [.I32]))
    (parameterWidth : signature.param_slots.val = slots params) :
    ∃ total base : U32,
      U32.checked_add signature.param_slots 1#u32 = some total ∧
      U32.checked_sub compiler.height total = some base ∧
      base.val = slots (compilerLocals compiler) + slots front := by
  have height : compiler.height.val = slots (compilerLocals compiler) + slots front + slots params + 1 := by
    simpa [slots_append,slots,width,Nat.add_assoc] using layout.height
  have addSpec := U32.checked_add_bv_spec signature.param_slots 1#u32
  cases added : U32.checked_add signature.param_slots 1#u32 with
  | none =>
    simp only [added] at addSpec
    have bound := compiler.height.hBounds
    scalar_tac
  | some total =>
    simp only [added] at addSpec
    have subSpec := U32.checked_sub_bv_spec compiler.height total
    cases subtracted : U32.checked_sub compiler.height total with
    | none =>
      simp only [subtracted] at subSpec
      scalar_tac
    | some base =>
      simp only [subtracted] at subSpec
      refine ⟨total,base,rfl,subtracted,?_⟩
      scalar_tac

theorem indirect_call_operand {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (front params : List valtype)
    (layout : CompilerLayout compiler ((front ++ params) ++ [.I32])) :
    ∃ index : U32, runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok index) ∧
      index.val = slots (compilerLocals compiler) + slots front + slots params := by
  obtain ⟨r,read,index,rfl,position⟩ := WP.spec_imp_exists
    (compiler_operand ops compiler _ layout 1#usize (by decide) (by change 1 ≤ _; simp only [List.length_append,List.length_singleton]; omega))
  refine ⟨index,read,?_⟩
  have take : (((front ++ params) ++ [valtype.I32]).take (((front ++ params) ++ [valtype.I32]).length - 1)) = front ++ params := by
    rw [List.length_append, List.length_singleton, Nat.add_sub_cancel]
    exact List.take_left
  change index.val = slots (compilerLocals compiler) + offset ((front ++ params) ++ [valtype.I32]) (((front ++ params) ++ [valtype.I32]).length - 1) at position
  simpa only [offset, take, slots_append, Nat.add_assoc] using position
end Itasca.Runtime.Compiler

end

/-! ## StatefulCallbacks -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

def statefulCallback {V : Type} (visitor : code.OpVisitor V) (before : V)
    (state : code.OpIterState) (op : SourceMachine.Stateful.Instruction) (a b : U32) :=
  match op with
  | .refNull .FUNCREF => visitor.on_ref_null before state .FuncRef
  | .refNull .EXTERNREF => visitor.on_ref_null before state .ExternRef
  | .refFunc _ => visitor.on_ref_func before state a
  | .refIsNull => visitor.on_ref_is_null before state
  | .tableGet _ => visitor.on_table_get before state a
  | .tableSet _ => visitor.on_table_set before state a
  | .tableSize _ => visitor.on_table_size before state a
  | .tableGrow _ => visitor.on_table_grow before state a
  | .tableFill _ => visitor.on_table_fill before state a
  | .tableCopy .. => visitor.on_table_copy before state a b
  | .tableInit .. => visitor.on_table_init before state a b
  | .elemDrop _ => visitor.on_elem_drop before state a
  | .memorySize => visitor.on_memory_size before state
  | .memoryGrow => visitor.on_memory_grow before state
  | .memoryFill => visitor.on_memory_fill before state
  | .memoryCopy => visitor.on_memory_copy before state
  | .memoryInit _ => visitor.on_memory_init before state a
  | .dataDrop _ => visitor.on_data_drop before state a

/-- The actual visitor forwards precisely the retained descriptor opcode and
immediates; paired table instructions keep their compiler argument order. -/
theorem stateful_callback_lower {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    (op : SourceMachine.Stateful.Instruction) (a b : U32) (arguments : StatefulArguments op a b) :
    statefulCallback (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before state op a b =
      runtime.compiler.lower.FunctionCompiler.op ops before state (statefulOpcode op) a b 0#u128 := by
  cases op <;> simp only [StatefulArguments,statefulArguments] at arguments
  all_goals try (rename_i ty; cases ty <;> simp only [statefulArguments] at arguments)
  all_goals obtain ⟨ha,hb⟩ := arguments
  all_goals try (have zero : b = 0#u32 := (UScalar.eq_equiv _ _).mpr hb; subst b)
  all_goals try (have zero : a = 0#u32 := (UScalar.eq_equiv _ _).mpr ha; subst a)
  all_goals try (have one : a = 1#u32 := (UScalar.eq_equiv _ _).mpr ha; subst a)
  all_goals try rfl
  all_goals simp only [statefulCallback,runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_ref_null,bind_ok,Bool.false_eq_true,↓reduceIte]
  all_goals rfl

end Itasca.Runtime.Compiler

end
