import Itasca.Runtime.Store.Instantiation.PreparedRun
import Itasca.Runtime.Store.Preparation.PreparationFunctionPayload
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca.ModuleEnv

theorem PreparedRun.function_payload {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {before : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {platform : P} {ready : runtime.store.Store M}
    (trace : PreparedRun memory hooks floats allocator view before module platform ready)
    (law : Platform.AllocCorrect allocator) (shape : Shape view before)
    {tables memories} (cache : Cache module.module.env tables memories) :
    trace.typed.funcs = before.funcs ∧ trace.typeInst.module = module ∧ trace.typeInst.funcs = trace.seed.funcs ∧
    TypeEntries trace.typed module.module.env.types.val trace.typeInst.types.val ∧
    FunctionPayload trace.typed trace.functions trace.typeInst before.instances.len module.module.env.func_type_indices.val.length ∧
    trace.functions.funcs.length = before.funcs.length + module.module.env.func_type_indices.val.length ∧
    trace.funcInst.funcs.val.map (fun a => a.index.val) = trace.seed.funcs.val.map (fun a => a.index.val) ++
      List.range' before.funcs.length module.module.env.func_type_indices.val.length := by
  have result := preparation_function_payload memory allocator law view before trace.seed shape trace.maps
    (by simpa only [trace.source] using cache) before.instances.len trace.typed trace.functions trace.typeInst trace.funcInst
    trace.typeRun trace.functionRun
  simpa only [trace.source] using result
end Itasca.Runtime.Store
