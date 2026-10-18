import Exec.Code.Local.Capacity.BranchTableCapacity
import Exec.Code.Body.Reader.Table.ReaderTableDispatchWasm1
import Exec.Code.Body.Reader.Table.ReaderTableWasm1
import Exec.Code.Body.Reader.Table.ReaderTableWasm2
import Itasca.Wasm2.Trace.TableBytes
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_table_capacity_wasm1 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_BR_TABLE before=.ok (.Ok (),out,after)) : CapacityStep before after out := by
  obtain ⟨fallback,common,collected,read,callback⟩ := reader_table_dispatch_wasm1
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx before after accepted
  obtain ⟨count,first,defaultStart,defaultEnd,depths,budget,buffer,_,_,_,_,same,_⟩ :=
    compiler_read_br_table_wasm1 ops law before collected st out data fallback common read
  subst collected
  exact compiler_br_table_capacity ops law {before with budget,table_depths:=buffer} after out fallback
    (Control.resultView common) callback

theorem reader_table_capacity_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 0x0e#u8 before=.ok (.Ok (),out,after)) : CapacityStep before after out.core := by
  rw [Wasm2.CallbackTrace.dispatch_br_table] at accepted
  obtain ⟨count,first,selector,popped,depths,fallback,types,defaultStart,readState,budget,buffer,
    _,_,_,_,_,_,_,callback⟩ := compiler_read_br_table_wasm2 ops law before after st out data env accepted
  exact compiler_br_table_capacity ops law {before with budget,table_depths:=buffer} after out.core fallback types callback
end Exec.Code
