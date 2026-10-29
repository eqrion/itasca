import Itasca.Runtime.Interp.Machine.Functions.FunctionCode
import Itasca.Runtime.Interp.Calls.CallRefinement
import Itasca.Runtime.Interp.Machine.Point
import Itasca.Runtime.Interp.Machine.Calls.CallStack

/-!
Defined-function callee certification and stack entry. The body point and call certificate assemble the frame-stack relation for the newly entered Wasm callee.
-/

/-! ## Call Certificate -/

section

namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas Aeneas.Std

/-- The compiler's complete function certificate supplies the initial callee
point, including implicit body-label branch and normal continuations. -/
theorem function_callee_point
    (s : _root_.store) (moduleInst : moduleinst) (C : context)
    (bindings : Abs.ModuleBindings s moduleInst C)
    (params declared results : List valtype) (body : List instr)
    (compiled : runtime.bytecode.CompiledFunction) (epilogue : U32)
    (certificate : FunctionCode C params declared results body compiled epilogue)
    (address : Nat) (instanceIndex functionIndex base : Usize)
    (args defaults : List val)
    (argumentTypes : args.map Code.valueType = params)
    (default : Abs.defaultLocals (declared.map local.LOCAL) = some defaults) :
    FramePoint s ⟨instanceIndex, functionIndex, 0#u32, base⟩
      (callCallee address moduleInst results args defaults body) compiled C
      [Code.functionRootLabel results compiled epilogue] epilogue.val results := by
  refine ⟨bindings,?_,?_,?_⟩
  · simpa only [callCallee,List.map_append,argumentTypes,defaultLocals_types declared defaults default] using certificate.1
  · constructor
    · rfl
    · intro depth label lookup
      cases depth with
      | zero =>
        have same : label = ⟨results, results, [], 0, []⟩ := by simpa [callCallee] using lookup.symm
        subst label
        refine ⟨Code.functionRootLabel results compiled epilogue, rfl, ?_⟩
        constructor <;> rfl
      | succ depth => simp [callCallee] at lookup
  · have localTypes : (args ++ defaults).map Code.valueType = params ++ declared := by
      rw [List.map_append, argumentTypes, defaultLocals_types declared defaults default]
    simpa [callCallee, localTypes] using certificate.entry

/-- Actual successful defined-call entry establishes the complete callee data
and code point from a syntactic function certificate. No execution-correctness
premise is added to the certificate. -/
theorem call_wasm_certified {M P F A : Type}
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
    (certificate : FunctionCode C
      (signature.params.val.map sourceType) declared (signature.results.val.map sourceType) body compiled epilogue)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (hi : store.instances.val[instanceIndex.val]? = some inst)
    (hc : inst.module.functions.val[functionIndex.val]? = some compiled)
    (identity : exec.store = store.id)
    (arguments : ValuesAt exec.slots.val base.val args)
    (argumentTypes : args.map Code.valueType = signature.params.val.map sourceType)
    (default : Abs.defaultLocals (declared.map local.LOCAL) = some defaults) :
    runtime.interp.call memory hooks floats allocator exec store platform address base ⦃ out =>
      out.2.2.1 = store ∧ (out.1 = .Ok () →
        let raw : runtime.interp.Frame := ⟨instanceIndex, functionIndex, 0#u32, base⟩
        let source := callCallee address.index.val (Store.decodeInstance store inst)
          (signature.results.val.map sourceType) args defaults body
        CallEntryEffect exec out.2.1 instanceIndex functionIndex base compiled ∧
        FrameBinding store out.2.1 raw source ∧ FrameSlots out.2.1 raw source ∧
        FramePoint s raw source compiled C
          [Code.functionRootLabel (signature.results.val.map sourceType) compiled epilogue]
          epilogue.val (signature.results.val.map sourceType)) ⦄ := by
  have localSlots : compiled.local_slots.val = compiled.param_slots.val + Code.slots declared := by
    rw [certificate.2.localSlots, Code.slots_append, certificate.2.parameterSlots]
  have params : compiled.param_slots.val ≤ compiled.local_slots.val := by omega
  have tags : (args ++ defaults).map Code.valueType = compiled.locals.val.map sourceType := by
    have translation : Itasca.Translate.valueType = sourceType := by funext ty; cases ty <;> rfl
    rw [List.map_append, argumentTypes, defaultLocals_types declared defaults default]
    simpa only [translation] using certificate.2.locals.symm
  apply WP.spec_mono (call_wasm_effect memory hooks floats allocator allocation interrupts exec store platform
    address base function instanceIndex functionIndex inst compiled hf hw hi hc params certificate.2.capacity)
  intro out effect
  refine ⟨effect.1, ?_⟩
  intro success
  have entered := effect.2 success
  refine ⟨entered, ?_, ?_, ?_⟩
  · exact entered.callee_binding store exec out.2.1 address function signature instanceIndex functionIndex base
      inst compiled args defaults body identity tags hf hs hw hi hc
  · have values := entered.callee_values arguments
      (by rw [argumentTypes, certificate.2.parameterSlots]) localSlots certificate.2.capacity default
    simpa [FrameSlots, callCallee] using values
  · exact function_callee_point s (Store.decodeInstance store inst) C bindings _ declared _ body compiled epilogue
      certificate address.index.val instanceIndex functionIndex base args defaults argumentTypes default

end Itasca.Runtime.Interp.StructuredMachine

end

/-! ## Call Stack Entry -/

section

namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas Aeneas.Std

/-- Actual defined-function entry preserves the complete prepared caller stack
and activates the callee's compiler certificate. -/
theorem call_wasm_stack {M P F A : Type}
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
    (certificate : FunctionCode C
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
    (saved : SavedFrames store s exec raws sources (signature.results.val.map sourceType) base.val) :
    runtime.interp.call memory hooks floats allocator exec store platform address base ⦃ out =>
      out.2.2.1 = store ∧ (out.1 = .Ok () →
        FrameStackRel store s out.2.1
          (callCallee address.index.val (Store.decodeInstance store inst)
            (signature.results.val.map sourceType) args defaults body :: sources) ∧
        out.2.1.frames.val.getLast? = some ⟨instanceIndex, functionIndex, 0#u32, base⟩ ∧
        ReadyTop store s out.2.1 (callCallee address.index.val (Store.decodeInstance store inst)
          (signature.results.val.map sourceType) args defaults body)) ⦄ := by
  apply WP.spec_mono (call_wasm_certified memory hooks floats allocator allocation interrupts
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
  apply FrameStackRel.call_enter effect _ frames saved _ (by omega) certificate.2.capacity
  exact ⟨binding, slots, compiled, C,
    [Code.functionRootLabel (signature.results.val.map sourceType) compiled epilogue], epilogue.val,
    signature.results.val.map sourceType, false, program, .ready point⟩

end Itasca.Runtime.Interp.StructuredMachine

end
