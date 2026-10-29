import Itasca.Runtime.Compiler.Body.Reader.Safety.Run
import Itasca.Runtime.Compiler.Body.Relations.Calls.OrdinaryCallbackReady
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulSafety
import Itasca.Wasm2.Bulk.Total

/-!
Normal return of reference, typed-select and memory/table metadata reader operations.

Main declarations: `compiler_reader_typed_select_total` and `compiler_reader_memory_grow_total`. A direct consumer is `Compiler.Body.Reader.Safety.ScalarSafety`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem compiler_reader_typed_select_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
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
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
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
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
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
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
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
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
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
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
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
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
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
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
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
