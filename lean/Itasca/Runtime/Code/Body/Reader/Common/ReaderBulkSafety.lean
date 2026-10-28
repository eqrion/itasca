import Itasca.Runtime.Code.Body.Reader.Common.ReaderSafety
import Itasca.Runtime.Code.Body.Relations.Calls.OrdinaryCallbackReady
import Itasca.Runtime.Code.Local.Relations.Common.StatefulSafety
import Itasca.Wasm2.Bulk.Total
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2

/-- The extracted bulk dispatcher returns for every subopcode and immediate,
including reader rejection, allocation rejection and unknown subopcodes. -/
theorem compiler_reader_bulk_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (opcode : U32)
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
end Itasca.Runtime.Code
