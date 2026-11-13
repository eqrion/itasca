import Itasca.Runtime.Interp.Machine.SuspendedPoint
import Itasca.Runtime.Compiler.Local.Relations.Calls.IndirectCallInversion
import Itasca.Runtime.Interp.Machine.Functions.CompiledFunctions
import Itasca.Runtime.SourceMachine.CallSafety
import Itasca.Runtime.Interp.Machine.Frames.FrameStack
import Itasca.Runtime.Interp.Calls.IndirectResolve

/-!
Sections, each formerly its own module: IndirectPoint, CallLookup, CallStack, CallStackEntry.
-/

/-! ## IndirectPoint -/

section

/-!
The indirect call head is independent of the following instruction family. The projection is purely syntactic and is discharged by each cumulative emission.

Main declarations: `indirect_point_head`. A direct consumer is `Interp.Machine.Calls.IndirectOperands`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas.Std
variable {jumpTables : List Aeneas.Std.U32}

/-- The indirect call head is independent of the following instruction family.
The projection is purely syntactic and is discharged by each cumulative emission. -/
theorem indirect_point_head {emission : ContextEmission} {pairs C returns code labels stack pc next output}
    (table type : Nat) (after : List instr)
    (project : ∀ before emitted result,
      emission C before (.CALL_INDIRECT (.mk_uN table) (.mk_uN type)) emitted result →
        Compiler.IndirectCallEmission pairs C before (.CALL_INDIRECT (.mk_uN table) (.mk_uN type)) emitted result)
    (point : Compiler.StructuredCode.Point (emission C) C.TYPES C.FUNCS returns C.LOCALS
      code jumpTables labels stack (.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode.Point (emission C) C.TYPES C.FUNCS returns C.LOCALS
        code jumpTables labels stack (.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after) target.val next output) ∨
    (∃ (front params results : List valtype) (typeIndex tableIndex entry index base : U32) (bounds : limits),
      typeIndex.val = type ∧ tableIndex.val = table ∧ stack = (front ++ params) ++ [.I32] ∧
      C.TYPES[type]? = some ⟨.mk_list params,.mk_list results⟩ ∧
      C.TABLES[table]? = some (.mk_tabletype bounds .FUNCREF) ∧
      pairs[entry.val]? = some (tableIndex,typeIndex) ∧
      base.val = Compiler.slots C.LOCALS + Compiler.slots front ∧ index.val = base.val + Compiler.slots params ∧
      code[pc]? = some (.CallIndirect entry index base) ∧
      Compiler.StructuredCode.Point (emission C) C.TYPES C.FUNCS returns C.LOCALS
        code jumpTables labels (front ++ results) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨front,params,results,typeIndex,tableIndex,entry,index,base,bounds,typeEq,tableEq,stackEq,resultEq,emitted,
      signature,tableFound,pair,basePosition,indexPosition⟩ := (project _ _ _ head).invert
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨front,params,results,typeIndex,tableIndex,entry,index,base,bounds,rfl,rfl,rfl,
      signature,tableFound,pair,basePosition,indexPosition,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => simp at sourceEq
end Itasca.Runtime.Interp.Machine

end

/-! ## CallLookup -/

section

/-!
Lookup of a defined function from its compilation certificate.

Main declarations: `CompiledFunctions.defined`. A direct consumer is `Interp.Machine.Calls.IndirectSelected`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

theorem CompiledFunctions.defined {M : Type} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} (compiledFunctions : CompiledFunctions code store)
    (view : M → Slice U8) (typed : CoreFunctionsTyped view code store)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (instanceIndex functionIndex : Usize)
    (lookup : store.funcs.val[address.index.val]? = some function)
    (defined : function.code = .Wasm instanceIndex functionIndex) :
    ∃ inst compiled signature declared body epilogue,
      store.instances.val[instanceIndex.val]? = some inst ∧
      inst.module.functions.val[functionIndex.val]? = some compiled ∧
      store.types.val[function.signature.val]? = some signature ∧
      FunctionTable store inst (inst.module.module.env.func_types.val.map Store.decodeFuncType) ∧
      FunctionCode (Compiler.moduleFunctionContext inst.module
        (signature.params.val.map sourceType++declared) (signature.results.val.map sourceType))
        (signature.params.val.map sourceType) declared (signature.results.val.map sourceType) body compiled epilogue ∧
      SourceMachine.ModuleBindings (Store.decodeStore view code store) (Store.decodeInstance store inst)
        (Compiler.moduleFunctionContext inst.module (signature.params.val.map sourceType++declared) (signature.results.val.map sourceType)) ∧
      (Store.decodeStore view code store).FUNCS[address.index.val]? =
        some ⟨Store.decodeFuncType signature,Store.decodeInstance store inst,
          .FUNC (.mk_uN compiled.type_index.val) (declared.map local.LOCAL) body⟩ := by
  obtain ⟨inst,compiled,signature,declared,body,epilogue,hi,hc,hs,source,table,types,certificate⟩ :=
    compiledFunctions function (List.mem_of_getElem? lookup) instanceIndex functionIndex defined
  have sourceTyped := typed function (List.mem_of_getElem? lookup)
  simp only [CoreFunctionTyped,defined] at sourceTyped
  obtain ⟨actual,index,locals,instructions,found,bodyEq,bindings,functionTyped⟩ := sourceTyped
  have same : actual = inst := Option.some.inj (found.symm.trans hi)
  subst actual
  have contextBindings := bindings.scope (signature.params.val.map sourceType++declared) [] (some (.mk_list (signature.results.val.map sourceType)))
  exact ⟨inst,compiled,signature,declared,body,epilogue,hi,hc,hs,table,certificate,contextBindings,
    defined_function_lookup view code store address function signature instanceIndex functionIndex inst _ lookup hs defined hi source⟩
end Itasca.Runtime.Interp.Machine

end

/-! ## CallStack -/

section

/-!
The caller's post-fetch continuation and live prefix form the saved frame needed for entry. The argument words remain available to the new callee.

Main declarations: `prepare_saved_caller` and `FrameStackRel.call_enter`. A direct consumer is `Interp.Machine.Calls.CallStackEntry`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

/-- The caller's post-fetch continuation and live prefix form the saved frame
needed for entry. The argument words remain available to the new callee. -/
theorem prepare_saved_caller {M : Type} {store : runtime.store.Store M} {s : _root_.store}
    {exec : runtime.interp.Execution} {raw : runtime.interp.Frame} {source : SourceMachine.AFrame}
    (binding : FrameBinding store exec raw source)
    (slots : FrameSlots exec raw source)
    {compiled C targets next output}
    (program : FrameProgram store raw compiled (source.locals.map Compiler.valueType) source.resultTypes C.FUNCS)
    (point : FramePoint s raw source compiled C targets next output)
    (index : Usize) (pc : U32) (lookup : exec.frames.val[index.val]? = some raw)
    (front args : List val) (after : List instr) (returns : List valtype) (base : Nat)
    (split : source.vals = front ++ args)
    (destination : base = raw.base.val + Compiler.slots ((source.locals ++ front).map Compiler.valueType))
    (heights : ∀ label ∈ source.labels, label.height ≤ front.length)
    (continuation : Compiler.StructuredCode (emission compiled C) C.TYPES C.FUNCS source.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
      (front.map Compiler.valueType ++ returns) after pc.val next output) :
    SavedFrame store s { exec with frames := exec.frames.set index { raw with pc := pc } }
      { raw with pc := pc } { source with vals := front, code := after } returns base := by
  refine ⟨binding.advance index pc lookup, ?_, destination,
    compiled, C, targets, next, output, ⟨program.lookup, program.checked, program.fetchBound, program.localSlots, program.epilogue⟩,
    point.suspend front args after pc returns split heights continuation⟩
  apply WordsAt.append_left (right := Compiler.encodeValues args)
  simpa only [FrameSlots, ValuesAt, split, Compiler.encode_values_append, List.append_assoc] using slots

/-- After successful entry, the initialized callee and prepared caller chain
constitute the complete frame-stack relation. -/
theorem FrameStackRel.call_enter {M : Type} {store : runtime.store.Store M} {s : _root_.store}
    {before after : runtime.interp.Execution} {raws : List runtime.interp.Frame} {sources : List SourceMachine.AFrame}
    {instanceIndex functionIndex base : Usize} {compiled : runtime.bytecode.CompiledFunction}
    (effect : CallEntryEffect before after instanceIndex functionIndex base compiled)
    (source : SourceMachine.AFrame)
    (frames : before.frames.val = raws.reverse)
    (saved : SavedFrames store s before raws sources source.resultTypes base.val)
    (active : ActiveFrame store s after ⟨instanceIndex, functionIndex, 0#u32, base⟩ source)
    (params : compiled.param_slots.val ≤ compiled.local_slots.val)
    (capacity : compiled.local_slots.val ≤ compiled.slot_count.val) :
    FrameStackRel store s after (source :: sources) := by
  exact .active (by rw [effect.1, frames]) active
    (saved.call_preserved effect (Nat.le_refl _) params capacity)

end Itasca.Runtime.Interp.Machine

end

/-! ## CallStackEntry -/

section

/-!
Defined-function callee certification and stack entry. The body point and call certificate assemble the frame-stack relation for the newly entered Wasm callee.
-/

/-! ## Call Certificate -/

section

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

/-- The compiler's complete function certificate supplies the initial callee
point, including implicit body-label branch and normal continuations. -/
theorem function_callee_point
    (s : _root_.store) (moduleInst : moduleinst) (C : context)
    (bindings : SourceMachine.ModuleBindings s moduleInst C)
    (params declared results : List valtype) (body : List instr)
    (compiled : runtime.bytecode.CompiledFunction) (epilogue : U32)
    (certificate : FunctionCode C params declared results body compiled epilogue)
    (address : Nat) (instanceIndex functionIndex base : Usize)
    (args defaults : List val)
    (argumentTypes : args.map Compiler.valueType = params)
    (default : SourceMachine.defaultLocals (declared.map local.LOCAL) = some defaults) :
    FramePoint s ⟨instanceIndex, functionIndex, 0#u32, base⟩
      (callCallee address moduleInst results args defaults body) compiled C
      [Compiler.functionRootLabel results compiled epilogue] epilogue.val results := by
  refine ⟨bindings,?_,?_,?_⟩
  · simpa only [callCallee,List.map_append,argumentTypes,default_locals_types declared defaults default] using certificate.1
  · constructor
    · rfl
    · intro depth label lookup
      cases depth with
      | zero =>
        have same : label = ⟨results, results, [], 0, []⟩ := by simpa [callCallee] using lookup.symm
        subst label
        refine ⟨Compiler.functionRootLabel results compiled epilogue, rfl, ?_⟩
        constructor <;> rfl
      | succ depth => simp [callCallee] at lookup
  · have localTypes : (args ++ defaults).map Compiler.valueType = params ++ declared := by
      rw [List.map_append, argumentTypes, default_locals_types declared defaults default]
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
    (function : runtime.store.FuncInst) (signature : Itasca.wasm_types.FuncType)
    (instanceIndex functionIndex : Usize) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (epilogue : U32)
    (s : _root_.store) (C : context) (bindings : SourceMachine.ModuleBindings s (Store.decodeInstance store inst) C)
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
    (argumentTypes : args.map Compiler.valueType = signature.params.val.map sourceType)
    (default : SourceMachine.defaultLocals (declared.map local.LOCAL) = some defaults) :
    runtime.interp.call memory hooks floats allocator exec store platform address base ⦃ out =>
      out.2.2.1 = store ∧ (out.1 = .Ok () →
        let raw : runtime.interp.Frame := ⟨instanceIndex, functionIndex, 0#u32, base⟩
        let source := callCallee address.index.val (Store.decodeInstance store inst)
          (signature.results.val.map sourceType) args defaults body
        CallEntryEffect exec out.2.1 instanceIndex functionIndex base compiled ∧
        FrameBinding store out.2.1 raw source ∧ FrameSlots out.2.1 raw source ∧
        FramePoint s raw source compiled C
          [Compiler.functionRootLabel (signature.results.val.map sourceType) compiled epilogue]
          epilogue.val (signature.results.val.map sourceType)) ⦄ := by
  have localSlots : compiled.local_slots.val = compiled.param_slots.val + Compiler.slots declared := by
    rw [certificate.2.localSlots, Compiler.slots_append, certificate.2.parameterSlots]
  have params : compiled.param_slots.val ≤ compiled.local_slots.val := by omega
  have tags : (args ++ defaults).map Compiler.valueType = compiled.locals.val.map sourceType := by
    have translation : Itasca.Translate.valueType = sourceType := by funext ty; cases ty <;> rfl
    rw [List.map_append, argumentTypes, default_locals_types declared defaults default]
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

end Itasca.Runtime.Interp.Machine

end

/-! ## Call Stack Entry -/

section

namespace Itasca.Runtime.Interp.Machine
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
    (function : runtime.store.FuncInst) (signature : Itasca.wasm_types.FuncType)
    (instanceIndex functionIndex : Usize) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (epilogue : U32)
    (s : _root_.store) (C : context) (bindings : SourceMachine.ModuleBindings s (Store.decodeInstance store inst) C)
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
    (argumentTypes : args.map Compiler.valueType = signature.params.val.map sourceType)
    (default : SourceMachine.defaultLocals (declared.map local.LOCAL) = some defaults)
    (raws : List runtime.interp.Frame) (sources : List SourceMachine.AFrame)
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
  have localSlots : compiled.local_slots.val = compiled.param_slots.val + Compiler.slots declared := by
    rw [certificate.2.localSlots, Compiler.slots_append, certificate.2.parameterSlots]
  have program : FrameProgram store ⟨instanceIndex, functionIndex, 0#u32, base⟩ compiled
      ((callCallee address.index.val (Store.decodeInstance store inst)
        (signature.results.val.map sourceType) args defaults body).locals.map Compiler.valueType)
      (signature.results.val.map sourceType) C.FUNCS := by
    refine ⟨⟨inst, hi, hc, functionTable⟩, certificate.2.checked, certificate.2.fetchBound, ?_, ?_⟩
    · simpa only [callCallee, List.map_append, argumentTypes,
        default_locals_types declared defaults default] using certificate.2.localSlots
    · obtain ⟨count, fetched⟩ := certificate.2.returnCode
      exact ⟨epilogue, count, certificate.2.endPosition, fetched⟩
  have top : out.2.1.frames.val.getLast? = some ⟨instanceIndex, functionIndex, 0#u32, base⟩ := by
    rw [effect.1]; simp
  refine ⟨?_, top, _, compiled, C,
    [Compiler.functionRootLabel (signature.results.val.map sourceType) compiled epilogue], epilogue.val,
    signature.results.val.map sourceType, top, program, point⟩
  apply FrameStackRel.call_enter effect _ frames saved _ (by omega) certificate.2.capacity
  exact ⟨binding, slots, compiled, C,
    [Compiler.functionRootLabel (signature.results.val.map sourceType) compiled epilogue], epilogue.val,
    signature.results.val.map sourceType, false, program, .ready point⟩

end Itasca.Runtime.Interp.Machine

end

end
