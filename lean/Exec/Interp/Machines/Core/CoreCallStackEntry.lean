import Exec.Interp.Machines.Core.CoreCallCertificate
import Exec.Interp.Machines.Core.CoreCallStack

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Actual defined-function entry preserves the complete prepared caller stack
and activates the callee's compiler certificate. -/
theorem call_wasm_core_stack {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (base : Usize)
    (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (instanceIndex functionIndex : Usize) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (epilogue : U32)
    (s : _root_.store) (C : context) (bindings : Abs.ModuleBindings s (Store.decodeInstance store inst) C)
    (declared : List valtype) (body : List instr)
    (args defaults : List val)
    (certificate : Code.CoreFunctionCode C
      (signature.params.val.map sourceType) declared (signature.results.val.map sourceType) body compiled epilogue)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (hi : store.instances.val[instanceIndex.val]? = some inst)
    (hc : inst.module.functions.val[functionIndex.val]? = some compiled)
    (functionTable : FunctionTable store inst C.FUNCS)
    (identity : exec.store = store.id)
    (arguments : ValuesAt exec.slots.val base.val args)
    (argumentTypes : args.map Code.valueType = signature.params.val.map sourceType)
    (default : Abs.defaultLocals (declared.map local.LOCAL) = some defaults)
    (raws : List runtime.interp.Frame) (sources : List Abs.AFrame)
    (frames : exec.frames.val = raws.reverse)
    (saved : CoreSavedFrames store s exec raws sources (signature.results.val.map sourceType) base.val) :
    runtime.interp.call memory hooks floats allocator exec store platform address base ⦃ out =>
      out.2.2.1 = store ∧ (out.1 = .Ok () →
        CoreFrameStackRel store s out.2.1
          (callCallee address.index.val (Store.decodeInstance store inst)
            (signature.results.val.map sourceType) args defaults body :: sources) ∧
        out.2.1.frames.val.getLast? = some ⟨instanceIndex, functionIndex, 0#u32, base⟩ ∧
        CoreReadyTop store s out.2.1 (callCallee address.index.val (Store.decodeInstance store inst)
          (signature.results.val.map sourceType) args defaults body)) ⦄ := by
  apply WP.spec_mono (call_wasm_core_certified memory hooks floats allocator allocation interrupts
    exec store platform address base function signature instanceIndex functionIndex inst compiled epilogue
    s C bindings declared body args defaults certificate hf hs hw hi hc identity arguments argumentTypes default)
  intro out result
  refine ⟨result.1, ?_⟩
  intro success
  obtain ⟨effect, binding, slots, point⟩ := result.2 success
  have localSlots : compiled.local_slots.val = compiled.param_slots.val + Code.slots declared := by
    rw [certificate.2.localSlots, Code.slots_append, certificate.2.parameterSlots]
  have program : FrameProgram store ⟨instanceIndex, functionIndex, 0#u32, base⟩ compiled
      ((callCallee address.index.val (Store.decodeInstance store inst)
        (signature.results.val.map sourceType) args defaults body).locals.map Code.valueType)
      (signature.results.val.map sourceType) C.FUNCS := by
    refine ⟨⟨inst, hi, hc, functionTable⟩, certificate.2.checked, certificate.2.fetchBound, ?_, ?_⟩
    · simpa only [callCallee, List.map_append, argumentTypes,
        defaultLocals_types declared defaults default] using certificate.2.localSlots
    · obtain ⟨count, fetched⟩ := certificate.2.returnCode
      exact ⟨epilogue, count, certificate.2.endPosition, fetched⟩
  have top : out.2.1.frames.val.getLast? = some ⟨instanceIndex, functionIndex, 0#u32, base⟩ := by
    rw [effect.1]; simp
  refine ⟨?_, top, _, compiled, C,
    [Code.functionRootLabel (signature.results.val.map sourceType) compiled epilogue], epilogue.val,
    signature.results.val.map sourceType, top, program, point⟩
  apply CoreFrameStackRel.call_enter effect _ frames saved _ (by omega) certificate.2.capacity
  exact ⟨binding, slots, compiled, C,
    [Code.functionRootLabel (signature.results.val.map sourceType) compiled epilogue], epilogue.val,
    signature.results.val.map sourceType, false, program, .ready point⟩

end Exec.Interp
