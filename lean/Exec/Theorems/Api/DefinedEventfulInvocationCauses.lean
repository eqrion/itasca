import Exec.Theorems.Composition.Eventful.EventfulDispatchCauses
import Exec.Theorems.Composition.Supported.SupportedEntryOutcomes
import Exec.Interp.Invocation.InvokeResourceCauses
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- Invocation errors retain setup, entry, reached-dispatch, or readback
witnesses. Reached machines retain the current invariant after host callbacks. -/
def DefinedEventfulInvocationCause {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (Inv : runtime.store.Store M → Prop)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (ambient : frame) (address : runtime.FuncAddr) (signature : Itasca.types.FuncType)
    (instanceIndex functionIndex : Usize) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (after : runtime.store.Store M) (error : runtime.ExecError) : Prop :=
  (after=store ∧ InvocationResourceCause allocator exec store signature results error) ∨
  (after=store ∧ ∃ prepared p out inst compiled,
    prepared.store=store.id ∧ prepared.frames.val=[] ∧ ValuesAt prepared.slots.val 0 (args.val.map sourceValue) ∧
    store.instances.val[instanceIndex.val]?=some inst ∧ inst.module.functions.val[functionIndex.val]?=some compiled ∧
    runtime.interp.call memory hooks floats allocator prepared store p address 0#usize=.ok out ∧
    out.1=.Err error ∧ out.2.2.1=after ∧ CallCause allocator hooks prepared store p 0#usize compiled error) ∨
  (∃ initial : EventfulMachine emission allowed M P view code (signature.results.val.map sourceType),
    initial.store=store ∧ Inv initial.store ∧ initial.source.ambient=ambient ∧
    StepH ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ [] (Abs.decode initial.source) ∧
    ∃ result, result.2.2.2.2.2.1=after ∧
      EventfulLoopFailure memory hooks floats allocator Inv (EventfulDispatchCause memory hooks floats allocator) initial result error) ∨
  (error=.Exhausted .Allocation ∧ ∃ values events,
    ResultsTyped (Store.decodeStore view code after) (signature.results.val.map sourceType) values ∧
    StepsH ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ events
      ⟨⟨Store.decodeStore view code after,ambient⟩,vals values⟩ ∧
    ∃ n : Usize,n.val=signature.results.length-results.length ∧ allocator.reserve results n=.ok (false,results))
end Exec.Theorems
