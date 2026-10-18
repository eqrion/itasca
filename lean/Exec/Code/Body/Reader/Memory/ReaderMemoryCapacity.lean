import Exec.Code.Body.Reader.Memory.MemoryReaderFacts
import Exec.Code.Local.Relations.Common.CoreLoweringEffects
import Exec.Code.Body.Reader.Integer.ReaderInteger
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_memory_load_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (operation : Abs.Memory.Load)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (memoryLoadOpcode operation)) before = .ok (.Ok (),out,after)) :
    CapacityStep before after out := by
  have meaning := (memory_load_reader_facts ops before out operation ⟨0#u32,0#u32⟩).1
  rw [code.step_memory.dispatch _ _ _ _ _ _ _ (memoryLoadMeaning operation) meaning] at accepted
  obtain ⟨arg,_,called⟩ := reader_run_success _ _ _ _ _ accepted
  rw [(memory_load_reader_facts ops before out operation arg).2.2.2.2.1] at called
  exact compiler_core_capacity ops law before after out (.load operation arg.offset arg.align) called

theorem reader_memory_load_capacity_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (operation : Abs.Memory.Load)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (memoryLoadOpcode operation)) before = .ok (.Ok (),out,after)) :
    CapacityStep before after out.core := by
  obtain ⟨_,_,_,_,_,ordinary,base,sign,misc⟩ := memory_load_reader_facts ops before out.core operation ⟨0#u32,0#u32⟩
  obtain ⟨_,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index _ before after
    ordinary base sign misc rfl accepted
  exact reader_memory_load_capacity ops law before after st.core out.core data env ctx operation run

theorem reader_memory_store_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (operation : Abs.Memory.Store)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (memoryStoreOpcode operation)) before = .ok (.Ok (),out,after)) :
    CapacityStep before after out := by
  have meaning := (memory_store_reader_facts ops before out operation ⟨0#u32,0#u32⟩).1
  rw [code.step_memory.dispatch _ _ _ _ _ _ _ (memoryStoreMeaning operation) meaning] at accepted
  obtain ⟨arg,_,called⟩ := reader_run_success _ _ _ _ _ accepted
  rw [(memory_store_reader_facts ops before out operation arg).2.2.2.2.1] at called
  exact compiler_core_capacity ops law before after out (.store operation arg.offset arg.align) called

theorem reader_memory_store_capacity_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (operation : Abs.Memory.Store)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (memoryStoreOpcode operation)) before = .ok (.Ok (),out,after)) :
    CapacityStep before after out.core := by
  obtain ⟨_,_,_,_,_,ordinary,base,sign,misc⟩ := memory_store_reader_facts ops before out.core operation ⟨0#u32,0#u32⟩
  obtain ⟨_,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index _ before after
    ordinary base sign misc rfl accepted
  exact reader_memory_store_capacity ops law before after st.core out.core data env ctx operation run
end Exec.Code
