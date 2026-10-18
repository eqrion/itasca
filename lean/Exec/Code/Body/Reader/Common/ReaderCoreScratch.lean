import Exec.Code.Body.Reader.Common.ReaderLiteralScratch
import Exec.Code.Local.Callbacks.Table.CompilerTableScratchScalar
import Exec.Code.Body.Reader.Float.ReaderFloatConstantLowering
import Exec.Code.Body.Reader.Memory.ReaderMemoryEmissions
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem reader_select_depths_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 27#u8 before = .ok (.Ok (),out,after)) :
    after.table_depths = before.table_depths := by
  obtain ⟨_,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index 27#u8 before after
    (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
  have dispatch := dispatch_select (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st.core data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  exact compiler_core_depths ops law before after out.core (.select false) callback

theorem reader_global_get_depths_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 35#u8 before = .ok (.Ok (),out,after)) :
    after.table_depths = before.table_depths := by
  obtain ⟨_,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index 35#u8 before after
    (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
  have dispatch := dispatch_global_get (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st.core data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  exact compiler_core_depths ops law before after out.core (.globalGet value) callback

theorem reader_global_set_depths_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 36#u8 before = .ok (.Ok (),out,after)) :
    after.table_depths = before.table_depths := by
  obtain ⟨_,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index 36#u8 before after
    (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
  have dispatch := dispatch_global_set (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st.core data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  exact compiler_core_depths ops law before after out.core (.globalSet value) callback

theorem reader_f32_const_depths_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 67#u8 before = .ok (.Ok (),out,after)) :
    after.table_depths = before.table_depths := by
  obtain ⟨_,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index 67#u8 before after
    (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
  have dispatch := dispatch_f32_const (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st.core data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f32_const ops before out.core value = _ at callback
  rw [callback_float32_eq] at callback
  exact compiler_op65_depths ops law before after out.core _ _ _ callback

theorem reader_f64_const_depths_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 68#u8 before = .ok (.Ok (),out,after)) :
    after.table_depths = before.table_depths := by
  obtain ⟨_,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index 68#u8 before after
    (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
  have dispatch := dispatch_f64_const (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st.core data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f64_const ops before out.core value = _ at callback
  rw [callback_float64_eq] at callback
  exact compiler_op66_depths ops law before after out.core _ _ _ callback

theorem reader_memory_load_depths_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals) (op : Abs.Memory.Load)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryLoadOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (memoryLoadOpcode op)) before = .ok (.Ok (),out,after)) :
    after.table_depths = before.table_depths := by
  obtain ⟨meaning,_,_,_,_,ordinary,base,sign,misc⟩ := memory_load_reader_facts ops before out.core op ⟨0#u32,0#u32⟩
  obtain ⟨capacity,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals,p.ft.results⟩ index _ before after ordinary base sign misc contextLocals accepted
  obtain ⟨arg,values,callback,read,post⟩ := reader_memory_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core _ (memoryLoadMeaning op)
    capacity byte meaning run
  obtain ⟨_,kind,ty,source,callbackEq,_,_,_,_⟩ := memory_load_reader_facts ops before out.core op arg
  rw [callbackEq] at callback
  exact compiler_core_depths ops law before after out.core (.load op arg.offset arg.align) callback

theorem reader_memory_store_depths_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals) (op : Abs.Memory.Store)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryStoreOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (memoryStoreOpcode op)) before = .ok (.Ok (),out,after)) :
    after.table_depths = before.table_depths := by
  obtain ⟨meaning,_,_,_,_,ordinary,base,sign,misc⟩ := memory_store_reader_facts ops before out.core op ⟨0#u32,0#u32⟩
  obtain ⟨capacity,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals,p.ft.results⟩ index _ before after ordinary base sign misc contextLocals accepted
  obtain ⟨arg,values,callback,read,post⟩ := reader_memory_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core _ (memoryStoreMeaning op)
    capacity byte meaning run
  obtain ⟨_,kind,ty,source,callbackEq,_,_,_,_⟩ := memory_store_reader_facts ops before out.core op arg
  rw [callbackEq] at callback
  exact compiler_core_depths ops law before after out.core (.store op arg.offset arg.align) callback
end Exec.Code
