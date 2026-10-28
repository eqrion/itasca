import Itasca.Runtime.Interp.StructuredMachine.FunctionCode
import Itasca.Runtime.Interp.Calls.CallRefinement
import Itasca.Runtime.Interp.StructuredMachine.Point

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
