import Itasca.Runtime.Representation.FunctionTable
import Itasca.Runtime.Interp.Relations.SuspendedPoint
import Itasca.Runtime.Interp.Calls.ReturnRegions
import Itasca.Runtime.Interp.Calls.CallFrames

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Code safety and exact retained store lookups for a concrete frame. -/
structure FrameProgram {M : Type} (store : runtime.store.Store M)
    (raw : runtime.interp.Frame) (compiled : runtime.bytecode.CompiledFunction)
    (locals results : List valtype) (functions : List functype) : Prop where
  lookup : ∃ inst, store.instances.val[raw.instance.val]? = some inst ∧
    inst.module.functions.val[raw.function.val]? = some compiled ∧
    FunctionTable store inst functions
  checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true
  fetchBound : compiled.code.val.length ≤ U32.max
  localSlots : compiled.local_slots.val = Compiler.slots locals
  epilogue : ∃ pc count : U32, compiled.code.val.length = pc.val + 1 ∧
    compiled.code.val[pc.val]? = some (.Return compiled.local_slots count)

end Itasca.Runtime.Interp
