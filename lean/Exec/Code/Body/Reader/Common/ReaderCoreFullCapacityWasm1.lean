import Exec.Code.Local.Capacity.LiteralCapacity
import Exec.Code.Local.Relations.Common.CoreLoweringEffects
import Exec.Code.Body.Reader.Float.ReaderFloatConstantLowering
import Exec.Code.Body.Reader.Memory.ReaderMemoryEmissions
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem reader_select_full_capacity_wasm1 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 27#u8 before = .ok (.Ok (),out,after)) :
    CapacityStep before after out := by
  have run := accepted
  have dispatch := dispatch_select (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  exact compiler_core_capacity ops law before after out (.select false) callback

theorem reader_global_get_full_capacity_wasm1 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 35#u8 before = .ok (.Ok (),out,after)) :
    CapacityStep before after out := by
  have run := accepted
  have dispatch := dispatch_global_get (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  exact compiler_core_capacity ops law before after out (.globalGet value) callback

theorem reader_global_set_full_capacity_wasm1 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 36#u8 before = .ok (.Ok (),out,after)) :
    CapacityStep before after out := by
  have run := accepted
  have dispatch := dispatch_global_set (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  exact compiler_core_capacity ops law before after out (.globalSet value) callback

theorem reader_f32_const_full_capacity_wasm1 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 67#u8 before = .ok (.Ok (),out,after)) :
    CapacityStep before after out := by
  have run := accepted
  have dispatch := dispatch_f32_const (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f32_const ops before out value = _ at callback
  rw [callback_float32_eq] at callback
  exact compiler_op65_capacity ops law before after out _ _ _ callback

theorem reader_f64_const_full_capacity_wasm1 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 68#u8 before = .ok (.Ok (),out,after)) :
    CapacityStep before after out := by
  have run := accepted
  have dispatch := dispatch_f64_const (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f64_const ops before out value = _ at callback
  rw [callback_float64_eq] at callback
  exact compiler_op66_capacity ops law before after out _ _ _ callback

theorem reader_memory_load_full_capacity_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (op : Abs.Memory.Load)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryLoadOpcode op))
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (memoryLoadOpcode op)) before = .ok (.Ok (),out,after)) :
    CapacityStep before after out := by
  obtain ⟨meaning,_,_,_,_,ordinary,base,sign,misc⟩ := memory_load_reader_facts ops before out op ⟨0#u32,0#u32⟩
  obtain ⟨arg,values,callback,read,post⟩ := reader_memory_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out _ (memoryLoadMeaning op)
    byte meaning accepted
  obtain ⟨_,kind,ty,source,callbackEq,_,_,_,_⟩ := memory_load_reader_facts ops before out op arg
  rw [callbackEq] at callback
  exact compiler_core_capacity ops law before after out (.load op arg.offset arg.align) callback

theorem reader_memory_store_full_capacity_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (op : Abs.Memory.Store)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryStoreOpcode op))
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (memoryStoreOpcode op)) before = .ok (.Ok (),out,after)) :
    CapacityStep before after out := by
  obtain ⟨meaning,_,_,_,_,ordinary,base,sign,misc⟩ := memory_store_reader_facts ops before out op ⟨0#u32,0#u32⟩
  obtain ⟨arg,values,callback,read,post⟩ := reader_memory_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out _ (memoryStoreMeaning op)
    byte meaning accepted
  obtain ⟨_,kind,ty,source,callbackEq,_,_,_,_⟩ := memory_store_reader_facts ops before out op arg
  rw [callbackEq] at callback
  exact compiler_core_capacity ops law before after out (.store op arg.offset arg.align) callback
end Exec.Code
