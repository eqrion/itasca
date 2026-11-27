import Itasca.Runtime.Interp.Machine.SuspendedPoint
import Itasca.Runtime.Compiler.Local.Relations.Calls.BranchAndCallSafety
import Itasca.Runtime.Interp.Machine.CompiledFunctions
import Itasca.Runtime.SourceMachine.Preservation
import Itasca.Runtime.Interp.Machine.Frames.FrameAndReturnStacks
import Itasca.Runtime.Interp.Calls.OutcomesAndResolution
import Itasca.Runtime.Interp.Recording
import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.SourceMachine.Numeric.Decode
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.Interp.Control.BrTableSource
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.EntryAndBranchTables
import Itasca.Runtime.Interp.Machine.Coverage.SyntaxClosure
import Itasca.Runtime.SourceMachine.Bound
import Itasca.Runtime.Interp.Machine.Progress.SupportedAdvance
import Itasca.Runtime.Spec.TypingAndNumericOperations
import Itasca.Runtime.Interp.Relations.SourceCallCause
import Itasca.Runtime.Interp.Relations.TypedOperands
import Itasca.Runtime.Interp.Machine.Coverage.Heads
import Itasca.Runtime.SourceMachine.TransitionAndHostPreparation
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulLowered
import Itasca.Runtime.SourceMachine.Indirect.HostSimulation

/-!
Proofs for Runtime / Interp / Machine / Calls.

This module collects CallStackEntry, IndirectOperands.
Each section documents its contracts and consumers.
-/

/-! ## CallStackEntry -/

section

open Itasca.Representation

/-! ## IndirectPoint -/

section

/-!
The indirect call head is independent of the following instruction family. The projection is purely syntactic and is discharged by each cumulative emission.

Main declarations: `indirect_point_head`.
-/

namespace Itasca.Interp.Machine
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
      base.val = Representation.slots C.LOCALS + Representation.slots front ∧ index.val = base.val + Representation.slots params ∧
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
end Itasca.Interp.Machine

end

/-! ## CallLookup -/

section

/-!
Lookup of a defined function from its compilation certificate.

Main declarations: `CompiledFunctions.defined`.
-/

namespace Itasca.Interp.Machine
open Aeneas Aeneas.Std

theorem CompiledFunctions.defined {M : Type} {code : Representation.CodeInterpretation}
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
      FunctionTable store inst (inst.module.module.env.func_types.val.map Itasca.Translation.Environment.funcType) ∧
      FunctionCode (Compiler.moduleFunctionContext inst.module
        (signature.params.val.map Itasca.Translation.valueType++declared) (signature.results.val.map Itasca.Translation.valueType))
        (signature.params.val.map Itasca.Translation.valueType) declared (signature.results.val.map Itasca.Translation.valueType) body compiled epilogue ∧
      SourceMachine.ModuleBindings (Representation.decodeStore view code store) (Representation.decodeInstance store inst)
        (Compiler.moduleFunctionContext inst.module (signature.params.val.map Itasca.Translation.valueType++declared) (signature.results.val.map Itasca.Translation.valueType)) ∧
      (Representation.decodeStore view code store).FUNCS[address.index.val]? =
        some ⟨Itasca.Translation.Environment.funcType signature,Representation.decodeInstance store inst,
          .FUNC (.mk_uN compiled.type_index.val) (declared.map local.LOCAL) body⟩ := by
  obtain ⟨inst,compiled,signature,declared,body,epilogue,hi,hc,hs,source,table,types,certificate⟩ :=
    compiledFunctions function (List.mem_of_getElem? lookup) instanceIndex functionIndex defined
  have sourceTyped := typed function (List.mem_of_getElem? lookup)
  simp only [CoreFunctionTyped,defined] at sourceTyped
  obtain ⟨actual,index,locals,instructions,found,bodyEq,bindings,functionTyped⟩ := sourceTyped
  have same : actual = inst := Option.some.inj (found.symm.trans hi)
  subst actual
  have contextBindings := bindings.scope (signature.params.val.map Itasca.Translation.valueType++declared) [] (some (.mk_list (signature.results.val.map Itasca.Translation.valueType)))
  exact ⟨inst,compiled,signature,declared,body,epilogue,hi,hc,hs,table,certificate,contextBindings,
    defined_function_lookup view code store address function signature instanceIndex functionIndex inst _ lookup hs defined hi source⟩
end Itasca.Interp.Machine

end

/-! ## CallStack -/

section

/-!
The caller's post-fetch continuation and live prefix form the saved frame needed for entry. The argument words remain available to the new callee.

Main declarations: `prepare_saved_caller` and `FrameStackRel.call_enter`.
-/

namespace Itasca.Interp.Machine
open Aeneas Aeneas.Std

/-- The caller's post-fetch continuation and live prefix form the saved frame
needed for entry. The argument words remain available to the new callee. -/
theorem prepare_saved_caller {M : Type} {store : runtime.store.Store M} {s : _root_.store}
    {exec : runtime.interp.Execution} {raw : runtime.interp.Frame} {source : SourceMachine.AFrame}
    (binding : FrameBinding store exec raw source)
    (slots : FrameSlots exec raw source)
    {compiled C targets next output}
    (program : FrameProgram store raw compiled (source.locals.map Representation.valueType) source.resultTypes C.FUNCS)
    (point : FramePoint s raw source compiled C targets next output)
    (index : Usize) (pc : U32) (lookup : exec.frames.val[index.val]? = some raw)
    (front args : List val) (after : List instr) (returns : List valtype) (base : Nat)
    (split : source.vals = front ++ args)
    (destination : base = raw.base.val + Representation.slots ((source.locals ++ front).map Representation.valueType))
    (heights : ∀ label ∈ source.labels, label.height ≤ front.length)
    (continuation : Compiler.StructuredCode (emission compiled C) C.TYPES C.FUNCS source.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
      (front.map Representation.valueType ++ returns) after pc.val next output) :
    SavedFrame store s { exec with frames := exec.frames.set index { raw with pc := pc } }
      { raw with pc := pc } { source with vals := front, code := after } returns base := by
  refine ⟨binding.advance index pc lookup, ?_, destination,
    compiled, C, targets, next, output, ⟨program.lookup, program.checked, program.fetchBound, program.localSlots, program.epilogue⟩,
    point.suspend front args after pc returns split heights continuation⟩
  apply WordsAt.append_left (right := Representation.encodeValues args)
  simpa only [FrameSlots, ValuesAt, split, Representation.encode_values_append, List.append_assoc] using slots

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

end Itasca.Interp.Machine

end

/-! ## CallStackEntry -/

section

/-!
Defined-function callee certification and stack entry. The body point and call certificate assemble the frame-stack relation for the newly entered Wasm callee.
-/

/-! ## Call Certificate -/

section

namespace Itasca.Interp.Machine
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
    (argumentTypes : args.map Representation.valueType = params)
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
  · have localTypes : (args ++ defaults).map Representation.valueType = params ++ declared := by
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
    (s : _root_.store) (C : context) (bindings : SourceMachine.ModuleBindings s (Representation.decodeInstance store inst) C)
    (declared : List valtype) (body : List instr)
    (args defaults : List val)
    (certificate : FunctionCode C
      (signature.params.val.map Itasca.Translation.valueType) declared (signature.results.val.map Itasca.Translation.valueType) body compiled epilogue)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (hi : store.instances.val[instanceIndex.val]? = some inst)
    (hc : inst.module.functions.val[functionIndex.val]? = some compiled)
    (identity : exec.store = store.id)
    (arguments : ValuesAt exec.slots.val base.val args)
    (argumentTypes : args.map Representation.valueType = signature.params.val.map Itasca.Translation.valueType)
    (default : SourceMachine.defaultLocals (declared.map local.LOCAL) = some defaults) :
    runtime.interp.call memory hooks floats allocator exec store platform address base ⦃ out =>
      out.2.2.1 = store ∧ (out.1 = .Ok () →
        let raw : runtime.interp.Frame := ⟨instanceIndex, functionIndex, 0#u32, base⟩
        let source := callCallee address.index.val (Representation.decodeInstance store inst)
          (signature.results.val.map Itasca.Translation.valueType) args defaults body
        CallEntryEffect exec out.2.1 instanceIndex functionIndex base compiled ∧
        FrameBinding store out.2.1 raw source ∧ FrameSlots out.2.1 raw source ∧
        FramePoint s raw source compiled C
          [Compiler.functionRootLabel (signature.results.val.map Itasca.Translation.valueType) compiled epilogue]
          epilogue.val (signature.results.val.map Itasca.Translation.valueType)) ⦄ := by
  have localSlots : compiled.local_slots.val = compiled.param_slots.val + Representation.slots declared := by
    rw [certificate.2.localSlots, Representation.slots_append, certificate.2.parameterSlots]
  have params : compiled.param_slots.val ≤ compiled.local_slots.val := by omega
  have tags : (args ++ defaults).map Representation.valueType = compiled.locals.val.map Itasca.Translation.valueType := by
    have translation : Itasca.Translation.valueType = Itasca.Translation.valueType := by funext ty; cases ty <;> rfl
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
  · exact function_callee_point s (Representation.decodeInstance store inst) C bindings _ declared _ body compiled epilogue
      certificate address.index.val instanceIndex functionIndex base args defaults argumentTypes default

end Itasca.Interp.Machine

end

/-! ## Call Stack Entry -/

section

namespace Itasca.Interp.Machine
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
    (s : _root_.store) (C : context) (bindings : SourceMachine.ModuleBindings s (Representation.decodeInstance store inst) C)
    (declared : List valtype) (body : List instr)
    (args defaults : List val)
    (certificate : FunctionCode C
      (signature.params.val.map Itasca.Translation.valueType) declared (signature.results.val.map Itasca.Translation.valueType) body compiled epilogue)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (hi : store.instances.val[instanceIndex.val]? = some inst)
    (hc : inst.module.functions.val[functionIndex.val]? = some compiled)
    (functionTable : FunctionTable store inst C.FUNCS)
    (identity : exec.store = store.id)
    (arguments : ValuesAt exec.slots.val base.val args)
    (argumentTypes : args.map Representation.valueType = signature.params.val.map Itasca.Translation.valueType)
    (default : SourceMachine.defaultLocals (declared.map local.LOCAL) = some defaults)
    (raws : List runtime.interp.Frame) (sources : List SourceMachine.AFrame)
    (frames : exec.frames.val = raws.reverse)
    (saved : SavedFrames store s exec raws sources (signature.results.val.map Itasca.Translation.valueType) base.val) :
    runtime.interp.call memory hooks floats allocator exec store platform address base ⦃ out =>
      out.2.2.1 = store ∧ (out.1 = .Ok () →
        FrameStackRel store s out.2.1
          (callCallee address.index.val (Representation.decodeInstance store inst)
            (signature.results.val.map Itasca.Translation.valueType) args defaults body :: sources) ∧
        out.2.1.frames.val.getLast? = some ⟨instanceIndex, functionIndex, 0#u32, base⟩ ∧
        ReadyTop store s out.2.1 (callCallee address.index.val (Representation.decodeInstance store inst)
          (signature.results.val.map Itasca.Translation.valueType) args defaults body)) ⦄ := by
  apply WP.spec_mono (call_wasm_certified memory hooks floats allocator allocation interrupts
    exec store platform address base function signature instanceIndex functionIndex inst compiled epilogue
    s C bindings declared body args defaults certificate hf hs hw hi hc identity arguments argumentTypes default)
  intro out result
  refine ⟨result.1, ?_⟩
  intro success
  obtain ⟨effect, binding, slots, point⟩ := result.2 success
  have localSlots : compiled.local_slots.val = compiled.param_slots.val + Representation.slots declared := by
    rw [certificate.2.localSlots, Representation.slots_append, certificate.2.parameterSlots]
  have program : FrameProgram store ⟨instanceIndex, functionIndex, 0#u32, base⟩ compiled
      ((callCallee address.index.val (Representation.decodeInstance store inst)
        (signature.results.val.map Itasca.Translation.valueType) args defaults body).locals.map Representation.valueType)
      (signature.results.val.map Itasca.Translation.valueType) C.FUNCS := by
    refine ⟨⟨inst, hi, hc, functionTable⟩, certificate.2.checked, certificate.2.fetchBound, ?_, ?_⟩
    · simpa only [callCallee, List.map_append, argumentTypes,
        default_locals_types declared defaults default] using certificate.2.localSlots
    · obtain ⟨count, fetched⟩ := certificate.2.returnCode
      exact ⟨epilogue, count, certificate.2.endPosition, fetched⟩
  have top : out.2.1.frames.val.getLast? = some ⟨instanceIndex, functionIndex, 0#u32, base⟩ := by
    rw [effect.1]; simp
  refine ⟨?_, top, _, compiled, C,
    [Compiler.functionRootLabel (signature.results.val.map Itasca.Translation.valueType) compiled epilogue], epilogue.val,
    signature.results.val.map Itasca.Translation.valueType, top, program, point⟩
  apply FrameStackRel.call_enter effect _ frames saved _ (by omega) certificate.2.capacity
  exact ⟨binding, slots, compiled, C,
    [Compiler.functionRootLabel (signature.results.val.map Itasca.Translation.valueType) compiled epilogue], epilogue.val,
    signature.results.val.map Itasca.Translation.valueType, false, program, .ready point⟩

end Itasca.Interp.Machine

end

end

end

/-! ## IndirectOperands -/

section

open Itasca.Representation

/-! ## CallPoint -/

section

/-!
Inversion of a direct-call code point and its source values.

Main declarations: `code_rel_call_inv` and `code_rel_call_values`.
-/

namespace Itasca.Interp.Machine
open Aeneas.Std
variable {jumpTables : List Aeneas.Std.U32}
variable {emission : ContextEmission} [OrdinaryHeads emission]
theorem code_rel_call_inv {C returns locals code labels stack pc next output after}
    (index : U32)
    (relation : Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns locals code jumpTables labels stack
      (.CALL (.mk_uN index.val) :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns locals code jumpTables labels stack (.CALL (.mk_uN index.val) :: after) target.val next output) ∨
    (∃ front params results base,
      stack = front ++ params ∧ C.FUNCS[index.val]? = some ⟨.mk_list params, .mk_list results⟩ ∧
      base.val = Representation.slots locals + Representation.slots front ∧ code[pc]? = some (.Call index base) ∧
      Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns locals code jumpTables labels (front ++ results) after (pc + 1) next output) := by
  generalize hindex : index.val = sourceIndex at relation
  cases relation with
  | linear head ordinary fragment rest => exact False.elim (emission_not_call head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | call signature arguments instruction rest =>
    rename_i actualIndex base
    have same : actualIndex = index := by scalar_tac
    subst actualIndex
    exact Or.inr ⟨_, _, _, _, rfl, signature, arguments, instruction, rest⟩

/-- Static CALL argument types identify the actual operand suffix and the
callee base. The continuation records the future returned values. -/
theorem code_rel_call_values {C returns code labels pc next output after}
    (index : U32) (locals values : List val)
    (relation : Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns (locals.map Representation.valueType) code jumpTables labels
      (values.map Representation.valueType) (.CALL (.mk_uN index.val) :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns (locals.map Representation.valueType) code jumpTables labels
        (values.map Representation.valueType) (.CALL (.mk_uN index.val) :: after) target.val next output) ∨
    (∃ front args params results base,
      values = front ++ args ∧ args.map Representation.valueType = params ∧
      C.FUNCS[index.val]? = some ⟨.mk_list params, .mk_list results⟩ ∧
      base.val = Representation.slots ((locals ++ front).map Representation.valueType) ∧
      code[pc]? = some (.Call index base) ∧
      Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns (locals.map Representation.valueType) code jumpTables labels
        (front.map Representation.valueType ++ results) after (pc + 1) next output) := by
  rcases code_rel_call_inv index relation with skip | actual
  · exact Or.inl skip
  · obtain ⟨frontTypes, params, results, base, stack, signature, arguments, instruction, rest⟩ := actual
    obtain ⟨front, args, split, frontTypesEq, argumentTypes⟩ := List.map_eq_append_iff.mp stack
    refine Or.inr ⟨front, args, params, results, base, split, argumentTypes, signature, ?_, instruction, ?_⟩
    · simpa only [List.map_append, Representation.slots_append, frontTypesEq] using arguments
    · simpa only [frontTypesEq] using rest

end Itasca.Interp.Machine

end

/-! ## PrepareCallStack -/

section

/-!
Fetch advances the caller PC and removes argument values from its saved live prefix, preparing the complete suspended chain for a defined call.

Main declarations: `FrameStackRel.prepare_call`.
-/

namespace Itasca.Interp.Machine
open Aeneas Aeneas.Std

/-- Fetch advances the caller PC and removes argument values from its saved
live prefix, preparing the complete suspended chain for a defined call. -/
theorem FrameStackRel.prepare_call {M : Type} {store : runtime.store.Store M} {s : _root_.store}
    {exec : runtime.interp.Execution} {source : SourceMachine.AFrame} {rest : List SourceMachine.AFrame}
    (relation : FrameStackRel store s exec (source :: rest))
    (raw : runtime.interp.Frame) (index : Usize) (pc : U32)
    (last : index.val + 1 = exec.frames.length)
    (lookup : exec.frames.val[index.val]? = some raw)
    (binding : FrameBinding store exec raw source)
    (slots : FrameSlots exec raw source)
    {compiled C targets next output}
    (program : FrameProgram store raw compiled (source.locals.map Representation.valueType) source.resultTypes C.FUNCS)
    (point : FramePoint s raw source compiled C targets next output)
    (front args : List val) (after : List instr) (returns : List valtype) (base : Nat)
    (split : source.vals = front ++ args)
    (destination : base = raw.base.val + Representation.slots ((source.locals ++ front).map Representation.valueType))
    (heights : ∀ label ∈ source.labels, label.height ≤ front.length)
    (continuation : Compiler.StructuredCode (emission compiled C) C.TYPES C.FUNCS source.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
      (front.map Representation.valueType ++ returns) after pc.val next output) :
    ∃ raws,
      (exec.frames.set index { raw with pc := pc }).val = raws.reverse ∧
      SavedFrames store s { exec with frames := exec.frames.set index { raw with pc := pc } }
        raws ({ source with vals := front, code := after } :: rest) returns base := by
  have top : exec.frames.val.getLast? = some raw := by
    rw [List.getLast?_eq_getElem?]
    have position : exec.frames.val.length - 1 = index.val := by change exec.frames.length - 1 = index.val; omega
    rw [position]
    exact lookup
  cases relation with
  | @active actual _ raws _ frames active saved =>
    have same : actual = raw := by simpa only [frames, List.getLast?_concat, Option.some.injEq] using top
    subst actual
    have remaining : exec.frames.val.dropLast = raws.reverse := by rw [frames, List.dropLast_concat]
    refine ⟨{ raw with pc := pc } :: raws, ?_, ?_⟩
    · rw [frames_set_last exec index _ last, remaining, List.reverse_cons]
    · apply SavedFrames.cons
      · exact prepare_saved_caller binding slots program point index pc lookup front args after returns base
          split destination heights continuation
      · apply saved.transport
        · intro frame source binding member
          exact binding.advance_older index { raw with pc := pc } last (by rw [remaining]; exact List.mem_reverse.mpr member)
        · intro position bits represented _
          exact represented

end Itasca.Interp.Machine

end

/-! ## StructuredCall -/

section

/-!
Source-base retention and structured execution of a direct call.

Main declarations: `saved_source_base` and `step_call_structured`.
-/

namespace Itasca.Interp.Machine
open Aeneas Aeneas.Std

theorem saved_source_base {M : Type} {store : runtime.store.Store M} {s : _root_.store}
    {exec raws sources waiting base} (saved : SavedFrames store s exec raws sources waiting base) :
    base = suspendedSourceWords sources := by
  induction saved with
  | nil => rfl
  | cons head tail ih => simp only [suspendedSourceWords,head.destination,ih,Nat.add_comm]

/-- A direct call derives its callee, signature, argument layout, defaults, and
retained caller continuation from structural compilation/store certificates.
The actual interpreter returns normally under allocation/interrupt laws; a
successful result preserves the whole typed source slice and frame stack. -/
theorem step_call_structured {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame)
    (caller : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (index : U32) (after : List instr)
    (decoded : s = Representation.decodeStore view code store)
    (compiledFunctions : CompiledFunctions code store)
    (functionTyping : CoreFunctionsTyped view code store)
    (last : frameIndex.val + 1 = exec.frames.length)
    (hf : exec.frames.val[frameIndex.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some caller)
    (hc : caller.module.functions.val[raw.function.val]? = some compiled)
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := .CALL (.mk_uN index.val) :: after } :: rest, []⟩)
    (covered : SourceMachine.SupportedState ⟨s, ambient, { f with code := .CALL (.mk_uN index.val) :: after } :: rest, []⟩)
    (binding : FrameBinding store exec raw f)
    (slots : FrameSlots exec raw f)
    (program : FrameProgram store raw compiled (f.locals.map Representation.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint s raw { f with code := .CALL (.mk_uN index.val) :: after }
      compiled C targets next output)
    (relation : FrameStackRel store s exec ({ f with code := .CALL (.mk_uN index.val) :: after } :: rest)) :
    (∃ address function host offset, compiled.code.val[raw.pc.val]? = some (.Call index offset) ∧
      caller.funcs.val[index.val]? = some address ∧
      store.funcs.val[address.index.val]? = some function ∧ function.code = .Host host) ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ (out.1 = .Ok () →
        ∃ pc frames, (out.2.1.frames.val.getLast?).map (fun frame => frame.pc) = some pc ∧
          FrameStackRel store s out.2.1 frames ∧
          SourceMachine.ATyped ⟨s, ambient, frames, []⟩ ∧
          SourceMachine.SupportedState ⟨s, ambient, frames, []⟩ ∧
          ConcreteSim compiled.code.length raw.pc.val pc.val false false
            ⟨s, ambient, { f with code := .CALL (.mk_uN index.val) :: after } :: rest, []⟩
            ⟨s, ambient, frames, []⟩ ∧
          ReadyState store out.2.1 ⟨s, ambient, frames, []⟩ ∧
          (∀ expected, SourceMachine.InvocationResult expected
              ⟨s, ambient, { f with code := .CALL (.mk_uN index.val) :: after } :: rest, []⟩ →
            SourceMachine.InvocationResult expected ⟨s, ambient, frames, []⟩) ∧
          (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds ⟨s,ambient,{f with code := .CALL (.mk_uN index.val)::after}::rest,[]⟩ →
            SourceMachine.Ownership.StatefulOwned bounds ⟨s,ambient,frames,[]⟩) ∧
          (∀ bound, SourceMachine.CodeBound bound ⟨s,ambient,{f with code := .CALL (.mk_uN index.val)::after}::rest,[]⟩ →
            SourceMachine.CodeBound bound ⟨s,ambient,frames,[]⟩)) ∧
      (∀ error, out.1 = .Err error →
        SourceDirectCallCause allocator hooks exec store platform frameIndex raw caller compiled
          ⟨s, ambient, { f with code := .CALL (.mk_uN index.val) :: after } :: rest, []⟩ error) ⦄ := by
  have current := point.code.current
  rw [point.locals] at current
  rcases code_rel_call_values index f.locals f.vals current with skip | actual
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    have targetPoint : FramePoint s { raw with pc := target }
        { f with code := .CALL (.mk_uN index.val) :: after } compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels, by simpa only [point.locals] using continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩
    apply Or.inr
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      frameIndex raw caller compiled target last hf hi hc (program.fetched_bound _ fetched) fetched)
    intro out result
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := result
    refine ⟨sameStore, (fun _ => ⟨target, { f with code := .CALL (.mk_uN index.val) :: after } :: rest,
      ?_, ?_, typed, covered, ?_, ?_, (fun _ invariant => invariant), (fun _ invariant => invariant), (fun _ invariant => invariant)⟩), ?_⟩
    · rw [exactState, frames_set_last exec frameIndex _ last]
      simp
    · rw [exactState]
      exact FrameStackRel.ordinary relation (.refl store) (Itasca.Spec.extend_store_refl _ typed.store)
        raw frameIndex target last hf binding program (.ready targetPoint) slots ⟨rfl,rfl,rfl,rfl⟩ rfl (.refl _ _)
    · exact Or.inl ⟨rfl, dispatch_measure_forward _ _ _ _ forward continuation.entry_bound⟩
    · refine ⟨{ raw with pc := target }, compiled, C, targets, next, output, ?_,
        ⟨program.lookup, program.checked, program.fetchBound, program.localSlots, program.epilogue⟩, targetPoint⟩
      rw [exactState, frames_set_last exec frameIndex _ last]
      simp
    · intro error rejected
      rw [success] at rejected
      cases rejected
  · obtain ⟨front, args, params, results, offset, split, argumentTypes, signatureAt,
      argumentOffset, fetched, continuation⟩ := actual
    obtain ⟨address, function, signature, addressAt, ownedHere, functionAt, signatureAtStore, signatureEq⟩ :=
      program.resolve_call caller hi index.val ⟨.mk_list params, .mk_list results⟩ signatureAt
    cases defined : function.code with
    | Host host => exact Or.inl ⟨address,function,host,offset,fetched,addressAt,functionAt,defined⟩
    | Wasm instanceIndex functionIndex =>
      apply Or.inr
      obtain ⟨inst, calleeCode, actualSignature, declared, body, epilogue,
        instanceAt, calleeAt, actualSignatureAt, table, certificate, calleeBindings, sourceAt⟩ :=
        compiledFunctions.defined view functionTyping address function instanceIndex functionIndex functionAt defined
      have sameSignature : actualSignature = signature := Option.some.inj (actualSignatureAt.symm.trans signatureAtStore)
      subst actualSignature
      have signatureTypes : signature.params.val.map Itasca.Translation.valueType = params ∧ signature.results.val.map Itasca.Translation.valueType = results := by
        simpa only [Itasca.Translation.Environment.funcType, functype.mk_functype.injEq, list.mk_list.injEq] using signatureEq
      have argumentTypes' : args.map Representation.valueType = signature.params.val.map Itasca.Translation.valueType := argumentTypes.trans signatureTypes.1.symm
      obtain ⟨defaults, default, defaultTyped⟩ := SourceMachine.default_locals_typed typed.store declared (declared_types_not_bottom certificate)
      have resolve := binding.resolve_call caller hi index.val address addressAt
      have sourceAt' : s.FUNCS[address.index.val]? = some
          ⟨Itasca.Translation.Environment.funcType signature, Representation.decodeInstance store inst,
            .FUNC (.mk_uN calleeCode.type_index.val) (declared.map local.LOCAL) body⟩ := by rw [decoded]; exact sourceAt
      have nextStep := call_next s ambient f rest after index.val address.index.val (Representation.decodeInstance store inst)
        (signature.params.val.map Itasca.Translation.valueType) (signature.results.val.map Itasca.Translation.valueType) declared
        (.mk_uN calleeCode.type_index.val) body front args defaults resolve sourceAt' argumentTypes' default
      have actualStep : SourceMachine.astep ⟨s, ambient, { f with code := .CALL (.mk_uN index.val) :: after } :: rest, []⟩ =
          .next ⟨s, ambient,
            callCallee address.index.val (Representation.decodeInstance store inst) (signature.results.val.map Itasca.Translation.valueType)
              args defaults body :: { f with code := after, vals := front } :: rest, []⟩ := by
        simpa only [← split] using nextStep
      have nextTyped := SourceMachine.instruction_preservation s ambient f rest (.CALL (.mk_uN index.val)) after _ (.call _) typed actualStep
      have nextCovered := Machine.call_supported s ambient f rest index.val after _ covered actualStep
      have simulation := SourceMachine.instruction_simulation s ambient f rest (.CALL (.mk_uN index.val)) after _ (.call _) typed actualStep
      have heights : ∀ label ∈ f.labels, label.height ≤ front.length := by
        exact nextTyped.heights { f with code := after, vals := front } (by simp)
      have capacity := slots.capacity binding
      have baseFits : raw.base.val + offset.val ≤ Usize.max := by
        have prefixBound : Representation.slots ((f.locals ++ front).map Representation.valueType) ≤
            Representation.slots ((f.locals ++ f.vals).map Representation.valueType) := by
          simp only [split, List.map_append, Representation.slots_append]
          omega
        scalar_tac
      have encodedBound : raw.base.val + offset.val < 2 ^ UScalarTy.Usize.numBits := by scalar_tac
      let calleeBase : Usize := UScalar.ofNatCore (raw.base.val + offset.val) encodedBound
      have baseOffset : calleeBase.val = raw.base.val + offset.val := UScalar.ofNatCore_val_eq encodedBound
      have arguments : ValuesAt exec.slots.val calleeBase.val args := by
        have words : WordsAt exec.slots.val raw.base.val
            (Representation.encodeValues (f.locals ++ front) ++ Representation.encodeValues args) := by
          simpa only [FrameSlots, ValuesAt, split, Representation.encode_values_append, List.append_assoc] using slots
        simpa only [ValuesAt, Representation.encode_values_length, baseOffset, argumentOffset] using words.append_right
      have identity : exec.store = store.id := by
        obtain ⟨_, _, _, _, identity, _⟩ := binding
        exact identity
      refine (step_direct_call memory hooks floats allocator exec store platform frameIndex raw caller compiled
        index offset address calleeBase last hf hi hc fetched (program.fetched_bound _ fetched) addressAt baseOffset False _ ?_).spec
      intro pc hpc
      have tail : Compiler.StructuredCode (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
          (front.map Representation.valueType ++ signature.results.val.map Itasca.Translation.valueType) after pc.val next output := by
        simpa only [hpc, signatureTypes.2,point.locals] using continuation
      obtain ⟨raws, frames, saved⟩ := relation.prepare_call raw frameIndex pc last hf binding slots program point
        front args after (signature.results.val.map Itasca.Translation.valueType) calleeBase.val split
        (by rw [baseOffset, argumentOffset]) heights tail
      obtain ⟨out, returned, result⟩ := WP.spec_imp_exists (call_wasm_stack memory hooks floats allocator allocation interrupts
        { exec with frames := exec.frames.set frameIndex { raw with pc := pc } } store platform address calleeBase
        function signature instanceIndex functionIndex inst calleeCode epilogue s (Compiler.moduleFunctionContext inst.module (signature.params.val.map Itasca.Translation.valueType++declared) (signature.results.val.map Itasca.Translation.valueType))
        (by simpa only [decoded] using calleeBindings) declared body args defaults
        certificate functionAt signatureAtStore defined instanceAt calleeAt table identity arguments argumentTypes' default raws
        ({ f with code := after, vals := front } :: rest) frames saved)
      have causes := call_wasm_causes memory hooks floats allocator allocation interrupts
        { exec with frames := exec.frames.set frameIndex { raw with pc := pc } } store platform address calleeBase
        function instanceIndex functionIndex inst calleeCode functionAt defined instanceAt calleeAt
        (by rw [certificate.2.parameterSlots, certificate.2.localSlots, Representation.slots_append]; omega)
        certificate.2.capacity
      rw [returned] at causes
      simp only [WP.spec_ok] at causes
      rw [returned]
      apply Computation.DivSpec.ret
      refine ⟨result.1, ?_, ?_⟩
      · intro success
        obtain ⟨stack, top, ready⟩ := result.2 success
        refine ⟨0#u32, _, ?_, stack, nextTyped, nextCovered, ?_, ready, ?_, ?_, ?_⟩
        · simp only [top, Option.map_some]
        · exact ConcreteSim.of_source compiled.code.length raw.pc.val (0#u32).val false false simulation
        · intro expected invariant
          exact SourceMachine.instruction_result _ _ _ _ _ _ _ expected (.call _) typed invariant actualStep
        · exact Machine.call_owned s ambient f rest index.val after _ actualStep
        · intro bound bounded
          exact SourceMachine.instruction_bound bound s ambient f rest (.CALL (.mk_uN index.val)) after _ (.call _) bounded actualStep
      · intro error rejected
        refine ⟨index, offset, pc, address, calleeBase, function, instanceIndex, functionIndex,
          inst, calleeCode, fetched, addressAt, functionAt, defined, instanceAt, calleeAt,
          baseOffset, hpc, causes error rejected, ?_⟩
        refine ⟨f, rest, index.val, after, front, args, _,
          signature.params.val.map Itasca.Translation.valueType, signature.results.val.map Itasca.Translation.valueType, 0, ?_,
          resolve, sourceAt', rfl, argumentTypes', ?_⟩
        · simpa only [← split] using (Spec.StepsHN.refl typed.decode_wf)
        · simpa only [suspendedSourceWords, Nat.add_comm] using saved_source_base saved

end Itasca.Interp.Machine

end

/-! ## IndirectOperands -/

section

/-!
Source operand values at an indirect-call instruction.

Main declarations: `indirect_values_head`.
-/

namespace Itasca.Interp.Machine
open Aeneas Aeneas.Std WebAssembly Itasca.Spec

theorem indirect_values_head {s : _root_.store} {raw : runtime.interp.Frame} {f : SourceMachine.AFrame} {compiled : runtime.bytecode.CompiledFunction} {C targets next output}
    [IndirectProjection (emission compiled) compiled.indirect.val]
    (table type : Nat) (after : List instr)
    (point : FramePoint s raw {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after} compiled C targets next output)
    (typed : SourceMachine.FrameTyped s {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after} []) :
    (∃ target : U32, raw.pc.val<target.val ∧ compiled.code.val[raw.pc.val]?=some (.Jump target) ∧
      FramePoint s {raw with pc:=target} {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after} compiled C targets next output) ∨
    (∃ (front args : List val) (params results : List valtype) (position : Nat)
        (typeIndex tableIndex entry index base : U32) (bounds : limits),
      typeIndex.val=type ∧ tableIndex.val=table ∧
      f.vals=(front++args)++[SourceMachine.integerVal .I32 position] ∧ position<2^32 ∧
      ResultsTyped s params args ∧ args.map Representation.valueType=params ∧
      (∀ label∈f.labels,label.height≤front.length) ∧ SourceMachine.FrameTyped s {f with code:=after,vals:=front} results ∧
      C.TYPES[type]?=some ⟨.mk_list params,.mk_list results⟩ ∧
      C.TABLES[table]?=some (.mk_tabletype bounds .FUNCREF) ∧
      compiled.indirect.val[entry.val]?=some (tableIndex,typeIndex) ∧
      base.val=Representation.slots ((f.locals++front).map Representation.valueType) ∧ index.val=base.val+Representation.slots params ∧
      compiled.code.val[raw.pc.val]?=some (.CallIndirect entry index base) ∧
      Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
        (front.map Representation.valueType++results) after (raw.pc.val+1) next output) := by
  rcases indirect_point_head table type after (fun _ _ _ head => IndirectProjection.project (pairs:=compiled.indirect.val) head) point.code with jump | actual
  · obtain ⟨target,forward,fetched,tail⟩ := jump
    exact Or.inl ⟨target,forward,fetched,⟨point.bindings,point.locals,point.labels,tail⟩⟩
  · obtain ⟨stack,params,results,typeIndex,tableIndex,entry,index,base,bounds,typeEq,tableEq,input,signature,tableType,pair,basePosition,indexPosition,fetch,tail⟩ := actual
    obtain ⟨actualContext,front,args,actualParams,actualResults,position,bindings,actualTable,actualSignature,values,bounded,arguments,frontWf,heights,caller,tableBound,typeBound⟩ := SourceMachine.Indirect.operands typed
    have contexts : actualContext.TYPES=C.TYPES := bindings.types.trans point.bindings.types.symm
    rw [contexts,signature] at actualSignature
    have equal := Option.some.inj actualSignature
    obtain ⟨paramsEq,resultsEq⟩ := functype.mk_functype.inj equal
    have paramsEq := list.mk_list.inj paramsEq
    have resultsEq := list.mk_list.inj resultsEq
    subst actualParams
    subst actualResults
    have argumentTypes : args.map Representation.valueType=params := by
      simpa only [show Representation.valueType = SourceMachine.valueType from funext value_type_eq_abs] using SourceMachine.results_type_of_typed arguments
    have valueType : Representation.valueType (SourceMachine.integerVal .I32 position)=.I32 := rfl
    simp only [values,List.map_append,List.map_cons,List.map_nil,argumentTypes,valueType] at input
    have frontTypes : front.map Representation.valueType=stack := List.append_cancel_right (List.append_cancel_right input)
    refine Or.inr ⟨front,args,params,results,position,typeIndex,tableIndex,entry,index,base,bounds,typeEq,tableEq,
      values,bounded,arguments,argumentTypes,heights,caller,signature,tableType,pair,?_,indexPosition,fetch,?_⟩
    · simpa only [List.map_append,Representation.slots_append,frontTypes,point.locals] using basePosition
    · simpa only [frontTypes] using tail
end Itasca.Interp.Machine

end

end
