import Itasca.Runtime.Compiler.Local.Capacity.BranchTableCapacity
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchTableWasm2
import Itasca.Wasm2.Trace.TableBytes
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchTableSuffix
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableOperands
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchTableSource

/-!
Compiler capacity after reading a br_table label vector.

Main declarations: `reader_table_capacity_wasm2`. A direct consumer is `Compiler.Body.Capacity.ExecutableFunctionCapacity`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_table_capacity_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 0x0e#u8 before=.ok (.Ok (),out,after)) : CapacityStep before after out.core := by
  rw [Wasm2.CallbackTrace.dispatch_br_table] at accepted
  obtain ⟨count,first,selector,popped,depths,fallback,types,defaultStart,readState,budget,buffer,
    _,_,_,_,_,_,_,callback⟩ := compiler_read_br_table ops law before after st out data env _ accepted
  exact compiler_br_table_capacity ops law {before with budget,table_depths:=buffer} after out.core fallback types callback
end Itasca.Runtime.Compiler
