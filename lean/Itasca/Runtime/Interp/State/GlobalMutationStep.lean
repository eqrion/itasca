import Itasca.Runtime.Interp.State.GlobalMutation
import Itasca.Runtime.Interp.State.GlobalCoreStep
import Itasca.Runtime.Interp.State.GlobalCoreOperands
import Itasca.Runtime.Interp.Relations.Capacity
import Itasca.Runtime.Compiler.Local.Capacity.GlobalCapacity
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem dispatch_global_set_mutation
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (src index : U32) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (f : Abs.AFrame) (front : List val) (value : val)
    (platform : P) (frameIndex : Usize)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (slots : FrameSlots exec raw f) (values : f.vals = front ++ [value])
    (position : src.val = Code.slots ((f.locals ++ front).map Code.valueType))
    (mutable : object.ty.mutability = .Var)
    (typed : sourceType object.ty.valtype = Code.valueType value) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
      (Code.globalSetInstruction (decide (Code.width (sourceType object.ty.valtype) = 2)) src index)
      ⦃ out => GlobalMutation store out.2.2.1 value ⦄ := by
  classical
  have handler : (if decide (Code.width (sourceType object.ty.valtype) = 2) then
      runtime.interp.execute_global_set2 memory exec store raw.instance raw.base src index
      else runtime.interp.execute_global_set memory exec store raw.instance raw.base src index)
      ⦃ out => GlobalMutation store out.2.2 value ⦄ := by
    simp only [sourceType_width_two]
    by_cases vector : object.ty.valtype = .V128
    · simp only [vector,decide_true,ite_true]
      exact global_set2_mutation memory exec store raw src index inst address object f front value
        found mapped issued slots values position vector mutable typed
    · simp only [vector,decide_false,ite_false]
      exact global_set_mutation memory exec store raw src index inst address object f front value
        found mapped issued slots values position vector mutable typed
  apply WP.spec_mono (dispatch_globalSet memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
    (decide (Code.width (sourceType object.ty.valtype) = 2)) src index handler)
  exact fun _ effect => effect.1

theorem step_global_set_mutation
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (src index : U32) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (f : Abs.AFrame) (front : List val) (value : val)
    (platform : P) (frameIndex : Usize)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (slots : FrameSlots exec raw f) (values : f.vals = front ++ [value])
    (position : src.val = Code.slots ((f.locals ++ front).map Code.valueType))
    (mutable : object.ty.mutability = .Var)
    (typed : sourceType object.ty.valtype = Code.valueType value)
    (compiled : runtime.bytecode.CompiledFunction)
    (last : frameIndex.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (fetched : compiled.code.val[raw.pc.val]? = some (Code.globalSetInstruction (decide (Code.width (sourceType object.ty.valtype) = 2)) src index))
    (pcBound : raw.pc.val < U32.max) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out => GlobalMutation store out.2.2.1 value ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform frameIndex raw inst compiled
    (Code.globalSetInstruction (decide (Code.width (sourceType object.ty.valtype) = 2)) src index) last frameFound found codeFound fetched pcBound
  intro pc pcNext
  exact dispatch_global_set_mutation memory hooks floats allocator
    {exec with frames := exec.frames.set frameIndex {raw with pc := pc}} store raw src index inst address object f front value
    platform frameIndex found mapped issued slots values position mutable typed

end Itasca.Runtime.Interp
