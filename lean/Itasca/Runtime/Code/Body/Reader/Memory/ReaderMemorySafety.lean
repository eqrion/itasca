import Itasca.Runtime.Code.Body.Reader.Common.ReaderSafety
import Itasca.Runtime.Code.Body.Relations.Calls.OrdinaryCallbackReady
import Itasca.Runtime.Code.Local.Relations.Memory.MemorySafety
import Itasca.Runtime.Code.Body.Reader.Memory.MemoryReaderFacts
import Itasca.Wasm2.Scalar.ReadersTotal

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem compiler_reader_memory_load_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max)
    (op : Abs.Memory.Load) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (memoryLoadOpcode op)) compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  have facts := memory_load_reader_facts ops compiler st op ⟨0#u32,0#u32⟩
  rw [code.step_memory.dispatch _ st data env ctx compiler _ _ facts.1, facts.2.1]
  simp only [Bool.false_eq_true,↓reduceIte]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Wasm2.ScalarReaders.load st data env _ _ shape capacity) (by simp)
  · intro state arg read
    rw [(memory_load_reader_facts ops compiler state op arg).2.2.2.2.1]
    exact compiler_memory_load_total ops law compiler state op arg.offset arg.align
      ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_memory_store_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max)
    (op : Abs.Memory.Store) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (memoryStoreOpcode op)) compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  have facts := memory_store_reader_facts ops compiler st op ⟨0#u32,0#u32⟩
  rw [code.step_memory.dispatch _ st data env ctx compiler _ _ facts.1, facts.2.1]
  simp only [↓reduceIte]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Wasm2.ScalarReaders.store st data env _ _ shape capacity) (by simp)
  · intro state arg read
    rw [(memory_store_reader_facts ops compiler state op arg).2.2.2.2.1]
    exact compiler_memory_store_total ops law compiler state op arg.offset arg.align
      ready.codeFits ready.sourceFits ready.coordinateFits

end Itasca.Runtime.Code
