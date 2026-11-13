import Itasca.Runtime.Compiler.Body.Reader.Safety.Run
import Itasca.Runtime.Compiler.Body.Relations.Calls.ControlCallbackReady
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulSafety
import Itasca.Wasm2.Bulk.Total
import Itasca.Runtime.Compiler.Local.Lowering.Literal.LiteralSafety
import Itasca.Runtime.Compiler.Local.Relations.Global.GlobalSafety
import Itasca.Runtime.Compiler.Local.Relations.Operations.PairSafety
import Itasca.Wasm2.Scalar.Env
import Itasca.Visitor.BodyReplay

/-!
Sections, each formerly its own module: BulkSafety, LiteralSafety, ReferenceSafety.
-/

/-! ## BulkSafety -/

section

/-!
The extracted bulk dispatcher returns for every subopcode and immediate, including reader rejection, allocation rejection and unknown subopcodes.

Main declarations: `compiler_reader_bulk_total`. A direct consumer is `Compiler.Body.Reader.Safety.OrdinarySafety`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2

/-- The extracted bulk dispatcher returns for every subopcode and immediate,
including reader rejection, allocation rejection and unknown subopcodes. -/
theorem compiler_reader_bulk_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (opcode : U32)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step_bulk (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env opcode compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_bulk.eq_runs]
  unfold bulkStep
  split
  · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
    · exact WP.spec_mono (code.read_memory_init.total st data env shape) (by simp)
    · intro state value read
      exact compiler_stateful_total ops law compiler state (.memoryInit 0) value 0#u32
        ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits
  · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
    · exact WP.spec_mono (code.take_data_index.total st data env shape) (by simp)
    · intro state value read
      exact compiler_stateful_total ops law compiler state (.dataDrop 0) value 0#u32
        ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits
  · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
    · exact WP.spec_mono (code.read_memory_copy.total st data env shape) (by simp)
    · intro state value read
      exact compiler_stateful_total ops law compiler state (.memoryCopy) 0#u32 0#u32
        ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits
  · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
    · exact WP.spec_mono (code.read_memory_fill.total st data env shape) (by simp)
    · intro state value read
      exact compiler_stateful_total ops law compiler state (.memoryFill) 0#u32 0#u32
        ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits
  · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
    · exact WP.spec_mono (code.read_table_init.total st data env shape) (by simp)
    · intro state value read
      exact compiler_stateful_total ops law compiler state (.tableInit 0 0) value.1 value.2
        ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits
  · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
    · exact WP.spec_mono (code.take_element.total st data env shape) (by simp)
    · intro state value read
      exact compiler_stateful_total ops law compiler state (.elemDrop 0) value.1 0#u32
        ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits
  · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
    · exact WP.spec_mono (code.read_table_copy.total st data env shape) (by simp)
    · intro state value read
      exact compiler_stateful_total ops law compiler state (.tableCopy 0 0) value.1 value.2
        ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits
  · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
    · exact WP.spec_mono (code.read_table_grow.total st data env shape capacity) (by simp)
    · intro state value read
      exact compiler_stateful_total ops law compiler state (.tableGrow 0) value 0#u32
        ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits
  · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
    · exact WP.spec_mono (code.read_table_size.total st data env shape capacity) (by simp)
    · intro state value read
      exact compiler_stateful_total ops law compiler state (.tableSize 0) value 0#u32
        ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits
  · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
    · exact WP.spec_mono (code.read_table_fill.total st data env shape) (by simp)
    · intro state value read
      exact compiler_stateful_total ops law compiler state (.tableFill 0) value 0#u32
        ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits
  · simp
end Itasca.Runtime.Compiler

end

/-! ## LiteralSafety -/

section

/-!
Normal return of constant and basic scalar reader callbacks.

Main declarations: `compiler_reader_i32_const_total` and `compiler_reader_nop_total`. A direct consumer is `Compiler.Body.Reader.Safety.ScalarSafety`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem compiler_reader_i32_const_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_I32_CONST compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [OpDispatch.dispatch_i32_const]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Wasm2.ScalarReaders.i32_const st data shape capacity) (by simp)
  · intro state value read
    exact compiler_on_i32_const_total ops law compiler state value ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_i64_const_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_I64_CONST compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [OpDispatch.dispatch_i64_const]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Wasm2.ScalarReaders.i64_const st data shape capacity) (by simp)
  · intro state value read
    exact compiler_on_i64_const_total ops law compiler state value ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_f32_const_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_F32_CONST compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [OpDispatch.dispatch_f32_const]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Wasm2.ScalarReaders.f32_const st data shape capacity) (by simp)
  · intro state value read
    exact compiler_on_f32_const_total ops law compiler state value ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_f64_const_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_F64_CONST compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [OpDispatch.dispatch_f64_const]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Wasm2.ScalarReaders.f64_const st data shape capacity) (by simp)
  · intro state value read
    exact compiler_on_f64_const_total ops law compiler state value ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_drop_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_DROP compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [OpDispatch.dispatch_drop]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Wasm2.ScalarReaders.drop st shape capacity) (by simp)
  · intro state value read
    exact compiler_on_drop_total ops law compiler state value

theorem compiler_reader_select_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_SELECT compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_select.dispatch]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Wasm2.ScalarReaders.select st shape capacity) (by simp)
  · intro state value read
    exact compiler_select_raw_total ops law compiler state st.vals.val false ready.observed ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_global_get_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_GLOBAL_GET compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_global_get.dispatch]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Wasm2.ScalarReaders.global_get st data env shape capacity) (by simp)
  · intro state value read
    exact compiler_global_get_total ops law compiler state value ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_global_set_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_GLOBAL_SET compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_global_set.dispatch]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Wasm2.ScalarReaders.global_set st data env shape capacity) (by simp)
  · intro state value read
    exact compiler_global_set_total ops law compiler state value st.vals.val ready.observed ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_unreachable_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_UNREACHABLE compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [OpDispatch.dispatch_unreachable]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact by
      unfold code.read_unreachable
      step with code.mark_unreachable_total st shape
  · intro state value read
    exact compiler_on_unreachable_total ops law compiler state ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_nop_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_NOP compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [OpDispatch.dispatch_nop]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact by simp
  · intro state value read
    exact compiler_on_nop_total ops law compiler state
end Itasca.Runtime.Compiler

end

/-! ## ReferenceSafety -/

section

/-!
Normal return of reference, typed-select and memory/table metadata reader operations.

Main declarations: `compiler_reader_typed_select_total` and `compiler_reader_memory_grow_total`. A direct consumer is `Compiler.Body.Reader.Safety.ScalarSafety`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem compiler_reader_typed_select_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 28#u8 compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_wasm2.typed_select]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (code.read_typed_select.total st data shape capacity) (by simp)
  · intro state value read
    exact compiler_select_raw_total ops law compiler state st.vals.val true ready.observed
      ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_table_get_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 37#u8 compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_wasm2.table_get]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (code.read_table_get.total st data env shape capacity) (by simp)
  · intro state value read
    exact compiler_stateful_total ops law compiler state (.tableGet 0) value 0#u32
      ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_table_set_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 38#u8 compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_wasm2.table_set]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (code.read_table_set.total st data env shape) (by simp)
  · intro state value read
    exact compiler_stateful_total ops law compiler state (.tableSet 0) value 0#u32
      ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_ref_null_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 208#u8 compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_wasm2.ref_null]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (code.read_ref_null.total st data shape capacity) (by simp)
  · intro state value read
    cases value
    · simpa only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
        runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_ref_null,bind_ok,
        Bool.false_eq_true,↓reduceIte,statefulOpcode] using
        compiler_stateful_total ops law compiler state (.refNull .FUNCREF) 0#u32 0#u32
          ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits
    · simpa only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
        runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_ref_null,bind_ok,
        Bool.false_eq_true,↓reduceIte,statefulOpcode] using
        compiler_stateful_total ops law compiler state (.refNull .EXTERNREF) 1#u32 0#u32
          ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_ref_is_null_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 209#u8 compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_wasm2.ref_is_null]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (code.read_ref_is_null.total st shape capacity) (by simp)
  · intro state value read
    exact compiler_stateful_total ops law compiler state (.refIsNull) 0#u32 0#u32
      ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_ref_func_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 210#u8 compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_wasm2.ref_func]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (code.read_ref_func.total st data env shape capacity) (by simp)
  · intro state value read
    exact compiler_stateful_total ops law compiler state (.refFunc 0) value 0#u32
      ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_memory_size_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_MEMORY_SIZE compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_memory_size.dispatch]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Wasm2.ScalarReaders.memory_size st data env shape capacity) (by simp)
  · intro state value read
    exact compiler_stateful_total ops law compiler state .memorySize 0#u32 0#u32
      ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_memory_grow_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_MEMORY_GROW compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_memory_grow.dispatch]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Wasm2.ScalarReaders.memory_grow st data env shape capacity) (by simp)
  · intro state value read
    exact compiler_stateful_total ops law compiler state .memoryGrow 0#u32 0#u32
      ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits
end Itasca.Runtime.Compiler

end
