import Itasca.Runtime.Representation.StoreCapacity
import Itasca.Runtime.Interp.Relations.SourceCallCause
import Itasca.Runtime.SourceMachine.DecodeDepth
import Itasca.Runtime.Interp.Machine.Resources.CallErrors
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- The type and function tables used by the integer/control trace match the
source module and its issued function signatures. The selected signature also
matches the source function itself; no compiled slot counter appears here. -/
structure SourceCapacityEnvironment (store : _root_.store) (function : funcinst)
    (env : Itasca.module.Env) (typeIndex : U32) : Prop where
  types : function.MODULE.TYPES = env.types.val.map Store.decodeFuncType
  functions : Interp.FunctionsMatch store function.MODULE (env.func_types.val.map Store.decodeFuncType)
  signature : ∃ signature, env.types.val[typeIndex.val]? = some signature ∧
    function.TYPE = Store.decodeFuncType signature

end Itasca.Runtime.Interp
