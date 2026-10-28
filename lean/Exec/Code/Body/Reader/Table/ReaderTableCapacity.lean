import Exec.Code.Local.Capacity.BranchTableCapacity
import Exec.Code.Body.Reader.Table.ReaderTableWasm2
import Itasca.Wasm2.Trace.TableBytes
import Exec.Code.Body.Reader.Table.ReaderTableSuffix
import Exec.Code.Local.Relations.Table.BranchTableOperands
import Exec.Code.Body.Reader.Table.ReaderTableSource
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem reader_table_capacity_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 0x0e#u8 before=.ok (.Ok (),out,after)) : CapacityStep before after out.core := by
  rw [Wasm2.CallbackTrace.dispatch_br_table] at accepted
  obtain ⟨count,first,selector,popped,depths,fallback,types,defaultStart,readState,budget,buffer,
    _,_,_,_,_,_,_,callback⟩ := compiler_read_br_table ops law before after st out data env _ accepted
  exact compiler_br_table_capacity ops law {before with budget,table_depths:=buffer} after out.core fallback types callback
end Itasca.Runtime.Code
