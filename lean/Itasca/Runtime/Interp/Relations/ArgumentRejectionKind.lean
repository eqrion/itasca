import Itasca.Runtime.Representation.StoreCapacity
import Itasca.Runtime.Interp.Relations.SourceCallCause
import Itasca.Runtime.SourceMachine.DecodeDepth
import Itasca.Runtime.Interp.Machine.Resources.CallErrors
import Itasca.Runtime.Interp.Machine.Functions.CompiledFunctions
import Itasca.Runtime.Interp.Relations.StepActive
import Itasca.Runtime.Compiler.Body.Relations.Executable.RecordingEmission
import Itasca.Runtime.Interp.Relations.TypedOperands

/-!
Sections, each formerly its own module: SourceValueCauses, SourceAllocationCauses, SourceCanonicalCapacity, SourceIndirectResources, StepRecordingLookup, StepRecordingInversion, ArgumentRejectionKind.
-/

/-! ## SourceValueCauses -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- The type and function tables used by the integer/control trace match the
source module and its issued function signatures. The selected signature also
matches the source function itself; no compiled slot counter appears here. -/
structure SourceCapacityEnvironment (store : _root_.store) (function : funcinst)
    (env : Itasca.metadata.Env) (typeIndex : U32) : Prop where
  types : function.MODULE.TYPES = env.types.val.map Store.decodeFuncType
  functions : Interp.FunctionsMatch store function.MODULE (env.func_types.val.map Store.decodeFuncType)
  signature : ∃ signature, env.types.val[typeIndex.val]? = some signature ∧
    function.TYPE = Store.decodeFuncType signature

end Itasca.Runtime.Interp

end

/-! ## SourceAllocationCauses -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Actual allocator refusals at entry retain source-bounded request sizes. -/
theorem CallCause.source_allocation {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {base : Usize}
    {compiled : runtime.bytecode.CompiledFunction} {words : Nat}
    (bound : compiled.slot_count.val ≤ words)
    (cause : CallCause allocator hooks exec store platform base compiled (.Exhausted .Allocation)) :
    (∃ n : Usize, n.val ≤ base.val + words ∧ allocator.reserve exec.slots n = .ok (false, exec.slots)) ∨
      allocator.reserve exec.frames 1#usize = .ok (false, exec.frames) := by
  rcases cause with ⟨needed, n, amount, refused⟩ | refused
  · exact Or.inl ⟨n, by omega, refused⟩
  · exact Or.inr refused

end Itasca.Runtime.Interp

end

/-! ## SourceCanonicalCapacity -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- The complete source module namespace. The data namespace is completed
from the parsed module tail, as in the canonical function-typing certificate. -/
def sourceCapacityContext (env : Itasca.metadata.Env) (dataCount : Nat) : context :=
  { Compiler.sourceFunctionContext env [] [] with
    DATAS := List.replicate dataCount datatype.OK, RETURN := none }

/-- A source frame requirement whose complete validation environment is tied
by semantic bindings to the actual source instance. The function is typed in
that same context. No compiled slot counter appears in this definition. -/
def SourceCanonicalFunctionCapacity (store : _root_.store) (address : funcaddr) (words : Nat) : Prop :=
  ∃ (function : funcinst) (env : Itasca.metadata.Env)
      (typeIndex : U32) (dataCount : Nat),
    store.FUNCS[address]? = some function ∧
    SourceCapacityEnvironment store function env typeIndex ∧
    SourceMachine.ModuleBindings store function.MODULE (sourceCapacityContext env dataCount) ∧
    (∃ index locals body, function.CODE = .FUNC index locals body ∧
      Func_ok (sourceCapacityContext env dataCount) (.FUNC index locals body) function.TYPE) ∧
    Compiler.SourceFrameCapacity env typeIndex function.CODE words

/-- Canonical module typing supplies every namespace required by full-profile
capacity traces, including mutable globals, tables, memories and segments. -/
theorem function_canonical_capacity_decoded {M : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M)
    (capacities : Store.FunctionCapacities code store)
    (typed : CoreFunctionsTyped view code store)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (instanceIndex functionIndex : Usize) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction)
    (found : store.funcs.val[address.index.val]? = some function)
    (defined : function.code = .Wasm instanceIndex functionIndex)
    (instanceFound : store.instances.val[instanceIndex.val]? = some inst)
    (codeFound : inst.module.functions.val[functionIndex.val]? = some compiled) :
    ∃ words, SourceCanonicalFunctionCapacity (Store.decodeStore view code store) address.index.val words ∧
      compiled.slot_count.val ≤ words := by
  obtain ⟨actualInst,actualCode,typeIndex,actualFound,actualCodeFound,
      ⟨words,sourceCapacity,bound⟩,entries,table,signature,typeFound,signatureFound⟩ :=
    capacities function (List.mem_of_getElem? found) instanceIndex functionIndex defined
  have sameInst : actualInst = inst := Option.some.inj (actualFound.symm.trans instanceFound)
  subst actualInst
  have sameCode : actualCode = compiled := Option.some.inj (actualCodeFound.symm.trans codeFound)
  subst actualCode
  have functionTyped := typed function (List.mem_of_getElem? found)
  simp only [CoreFunctionTyped,defined] at functionTyped
  obtain ⟨typedInst,sourceIndex,locals,body,typedFound,sourceEq,bindings,sourceTyped⟩ := functionTyped
  have sameInst : typedInst = inst := Option.some.inj (typedFound.symm.trans instanceFound)
  subst typedInst
  have contextEq : Compiler.moduleSourceContext inst.module =
      sourceCapacityContext inst.module.module.env inst.module.module.tail.data.length := by rfl
  refine ⟨words,⟨Store.decodeFunction code store function,
    inst.module.module.env,typeIndex,inst.module.module.tail.data.length,?_,?_,?_,?_,?_⟩,bound⟩
  · simp only [Store.decodeStore,List.getElem?_map,found,Option.map_some]
  · constructor
    · simpa only [Store.decodeFunction,defined,instanceFound,Store.decodeInstance] using entries.capacity_decode
    · simpa only [Store.decodeFunction,defined,instanceFound] using table.source view code
    · refine ⟨signature,typeFound,?_⟩
      simp only [Store.decodeFunction,defined,instanceFound,List.getD_eq_getElem?_getD,
        List.getElem?_map,signatureFound,Option.map_some,Option.getD_some]
  · simpa only [Store.decodeFunction,defined,instanceFound,contextEq] using bindings
  · refine ⟨sourceIndex,locals,body,?_,?_⟩
    · simpa only [Store.decodeFunction,defined,instanceFound] using sourceEq
    · simpa only [contextEq] using sourceTyped
  · simpa only [Store.decodeFunction,defined,instanceFound] using sourceCapacity
end Itasca.Runtime.Interp

end

/-! ## SourceIndirectResources -/

section

/-!
Source invocation sites and their resource demand. Indirect-call site transport supports canonical value-capacity and allocation causes for direct and indirect calls.
-/

/-! ## Source Indirect Site -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- An indirect source call retains the selected callee and the shared
argument position, including storage suspended in all source callers. -/
def SourceIndirectCallSite (initial : SourceMachine.AState) (address : funcaddr) (base : Nat) : Prop :=
  ∃ (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (table type position : Nat) (after : List instr)
    (front args : List val) (callee : funcinst) (params results : List valtype) (count : Nat),
    Spec.StepsHN count (SourceMachine.decode initial) [] (SourceMachine.decode ⟨initial.store,initial.ambient,
      {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩) ∧
    f.vals=(front++args)++[SourceMachine.integerVal .I32 position] ∧ position<2^32 ∧
    SourceMachine.Indirect.resolve initial.store f table type position=some address ∧
    initial.store.FUNCS[address]?=some callee ∧
    callee.TYPE=⟨.mk_list params,.mk_list results⟩ ∧ args.map Compiler.valueType=params ∧
    base=suspendedSourceWords rest+Compiler.slots ((f.locals++front).map Compiler.valueType)

theorem SourceIndirectCallSite.prepend {before middle : SourceMachine.AState} {address base count}
    (steps : Spec.StepsHN count (SourceMachine.decode before) [] (SourceMachine.decode middle))
    (sameStore : middle.store=before.store) (sameAmbient : middle.ambient=before.ambient)
    (site : SourceIndirectCallSite middle address base) : SourceIndirectCallSite before address base := by
  obtain ⟨f,rest,table,type,position,after,front,args,callee,params,results,tailCount,
    tail,values,bounded,resolved,found,signature,arguments,storage⟩ := site
  refine ⟨f,rest,table,type,position,after,front,args,callee,params,results,count+tailCount,
    ?_,values,bounded,?_,?_,signature,arguments,storage⟩
  · simpa only [sameStore,sameAmbient,List.nil_append] using steps.trans tail
  · simpa only [sameStore] using resolved
  · simpa only [sameStore] using found

/-- The actual refusal witness exposes a purely source-level call site. -/
theorem SourceIndirectCallCause.source_site {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {interpretation : Store.CodeInterpretation}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P}
    {index : Usize} {raw : runtime.interp.Frame} {compiled : runtime.bytecode.CompiledFunction}
    {source : SourceMachine.AState} {error : runtime.ExecError}
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (decoded : source.store=Store.decodeStore view code store)
    (cause : SourceIndirectCallCause allocator hooks interpretation exec store platform index raw compiled source error) :
    ∃ (pc : U32) (address base : Usize) (function : runtime.store.FuncInst)
      (instanceIndex functionIndex : Usize) (inst : runtime.store.ModuleInst) (callee : runtime.bytecode.CompiledFunction),
      store.funcs.val[address.val]?=some function ∧ function.code=.Wasm instanceIndex functionIndex ∧
      store.instances.val[instanceIndex.val]?=some inst ∧ inst.module.functions.val[functionIndex.val]?=some callee ∧
      CallCause allocator hooks {exec with frames:=exec.frames.set index {raw with pc:=pc}}
        store platform base callee error ∧ SourceIndirectCallSite source address.val base.val := by
  obtain ⟨entry,selector,offset,table,type,pc,address,base,function,instanceIndex,functionIndex,inst,callee,
    fetch,pair,functionAt,defined,instanceAt,calleeAt,baseEq,pcEq,rejected,
    f,rest,after,front,args,position,params,results,count,steps,values,bounded,resolved,signature,arguments,coordinates,sourceBase⟩ := cause
  refine ⟨pc,address,base,function,instanceIndex,functionIndex,inst,callee,functionAt,defined,instanceAt,calleeAt,rejected,
    f,rest,table.val,type.val,position,after,front,args,Store.decodeFunction code store function,params,results,count,
    steps,values,bounded,resolved,?_,?_,arguments,?_⟩
  · simp only [decoded,Store.decodeStore,List.getElem?_map,functionAt,Option.map_some]
  · simpa only [Store.decodeFunction,defined,instanceAt] using signature
  · omega
end Itasca.Runtime.Interp

end

/-! ## Source Indirect Resources -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- A selected call may be direct or table-resolved; either witness is purely
source-level and fixes the shared argument base. -/
def SourceInvocationSite (source : SourceMachine.AState) (address : funcaddr) (base : Nat) : Prop :=
  SourceCallSite source address base ∨ SourceIndirectCallSite source address base

def SourceInvocationAllocation {A : Type} (allocator : runtime.platform.Alloc A)
    (source : SourceMachine.AState) : Prop :=
  ∃ address base words, SourceInvocationSite source address base ∧
    SourceCanonicalFunctionCapacity source.store address words ∧
    ((∃ (slots : alloc.vec.Vec U64) (n : Usize), n.val ≤ base+words ∧
      allocator.reserve slots n=.ok (false,slots)) ∨
      ∃ frames : alloc.vec.Vec runtime.interp.Frame, allocator.reserve frames 1#usize=.ok (false,frames))

theorem SourceIndirectCallCause.source_values {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {interpretation : Store.CodeInterpretation}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P}
    {index : Usize} {raw : runtime.interp.Frame} {compiled : runtime.bytecode.CompiledFunction} {source : SourceMachine.AState}
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (decoded : source.store=Store.decodeStore view code store)
    (capacities : Store.FunctionCapacities code store)
    (typed : CoreFunctionsTyped view code store)
    (cause : SourceIndirectCallCause allocator hooks interpretation exec store platform index raw compiled source (.Exhausted .Values)) :
    ∃ address base words, SourceIndirectCallSite source address base ∧
      SourceCanonicalFunctionCapacity source.store address words ∧ store.limits.max_values.val<base+words := by
  obtain ⟨pc,address,base,function,ii,fi,inst,callee,found,defined,hi,hc,rejected,site⟩ := cause.source_site view code decoded
  obtain ⟨words,capacity,bound⟩ := function_canonical_capacity_decoded view code store capacities typed {store:=store.id,index:=address}
    function ii fi inst callee found defined hi hc
  refine ⟨address.val,base.val,words,site,by simpa only [decoded] using capacity,?_⟩
  change store.limits.max_values.val<base.val+callee.slot_count.val at rejected
  omega

theorem SourceIndirectCallCause.source_allocation {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {interpretation : Store.CodeInterpretation}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P}
    {index : Usize} {raw : runtime.interp.Frame} {compiled : runtime.bytecode.CompiledFunction} {source : SourceMachine.AState}
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (decoded : source.store=Store.decodeStore view code store)
    (capacities : Store.FunctionCapacities code store)
    (typed : CoreFunctionsTyped view code store)
    (cause : SourceIndirectCallCause allocator hooks interpretation exec store platform index raw compiled source (.Exhausted .Allocation)) :
    SourceInvocationAllocation allocator source := by
  obtain ⟨pc,address,base,function,ii,fi,inst,callee,found,defined,hi,hc,rejected,site⟩ := cause.source_site view code decoded
  obtain ⟨words,capacity,bound⟩ := function_canonical_capacity_decoded view code store capacities typed {store:=store.id,index:=address}
    function ii fi inst callee found defined hi hc
  refine ⟨address.val,base.val,words,Or.inr site,by simpa only [decoded] using capacity,?_⟩
  rcases CallCause.source_allocation bound rejected with ⟨n,amount,refused⟩ | refused
  · exact Or.inl ⟨exec.slots,n,amount,refused⟩
  · exact Or.inr ⟨exec.frames.set index {raw with pc:=pc},refused⟩
theorem SourceDirectCallCause.source_values_canonical {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {index : Usize}
    {raw : runtime.interp.Frame} {inst : runtime.store.ModuleInst}
    {compiled : runtime.bytecode.CompiledFunction} {source : SourceMachine.AState}
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (decoded : source.store = Store.decodeStore view code store)
    (capacities : Store.FunctionCapacities code store)
    (typed : CoreFunctionsTyped view code store)
    (cause : SourceDirectCallCause allocator hooks exec store platform index raw inst compiled source (.Exhausted .Values)) :
    ∃ address base words, SourceCallSite source address base ∧
      SourceCanonicalFunctionCapacity source.store address words ∧ store.limits.max_values.val < base + words := by
  obtain ⟨target, offset, pc, address, base, function, instanceIndex, functionIndex,
    callee, codeObject, fetch, resolved, lookup, wasm, instanceLookup, codeLookup, baseEq, pcEq, rejection, site⟩ := cause
  obtain ⟨words, capacity, bound⟩ := function_canonical_capacity_decoded view code store capacities typed address function
    instanceIndex functionIndex callee codeObject lookup wasm instanceLookup codeLookup
  refine ⟨address.index.val, base.val, words, site, by simpa only [decoded] using capacity, ?_⟩
  change store.limits.max_values.val < base.val + codeObject.slot_count.val at rejection
  omega

theorem SourceDirectCallCause.source_allocation_canonical {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {index : Usize}
    {raw : runtime.interp.Frame} {inst : runtime.store.ModuleInst}
    {compiled : runtime.bytecode.CompiledFunction} {source : SourceMachine.AState}
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (decoded : source.store = Store.decodeStore view code store)
    (capacities : Store.FunctionCapacities code store)
    (typed : CoreFunctionsTyped view code store)
    (cause : SourceDirectCallCause allocator hooks exec store platform index raw inst compiled source (.Exhausted .Allocation)) :
    SourceInvocationAllocation allocator source := by
  obtain ⟨target, offset, pc, address, base, function, instanceIndex, functionIndex,
    callee, codeObject, fetch, resolved, lookup, wasm, instanceLookup, codeLookup, baseEq, pcEq, rejection, site⟩ := cause
  obtain ⟨words, capacity, bound⟩ := function_canonical_capacity_decoded view code store capacities typed address function
    instanceIndex functionIndex callee codeObject lookup wasm instanceLookup codeLookup
  refine ⟨address.index.val, base.val, words, Or.inl site, by simpa only [decoded] using capacity, ?_⟩
  rcases rejection with ⟨needed, n, amount, refused⟩ | refused
  · exact Or.inl ⟨exec.slots, n, by omega, refused⟩
  · exact Or.inr ⟨exec.frames.set index {raw with pc := pc}, refused⟩

end Itasca.Runtime.Interp

end

end

/-! ## StepRecordingLookup -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt

theorem host_step_address_at {M : Type} (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) (instruction : runtime.bytecode.Instr)
    (last : index.val+1=exec.frames.length) (frameAt : exec.frames.val[index.val]?=some raw)
    (instanceAt : store.instances.val[raw.instance.val]?=some inst)
    (compiledAt : inst.module.functions.val[raw.function.val]?=some compiled)
    (fetched : compiled.code.val[raw.pc.val]?=some instruction) :
    hostStepAddress exec store = hostInstructionAddress exec store raw inst compiled instruction := by
  have indexEq : exec.frames.length-1=index.val := by omega
  simp [hostStepAddress,indexEq,frameAt,instanceAt,compiledAt,fetched,Bind.bind,Option.bind]

theorem host_instruction_address_direct {M : Type} (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (index offset : U32)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (host : U64)
    (addressAt : inst.funcs.val[index.val]?=some address)
    (functionAt : store.funcs.val[address.index.val]?=some function) (hostCode : function.code=.Host host) :
    hostInstructionAddress exec store raw inst compiled (.Call index offset)=some address := by
  simp [hostInstructionAddress,addressAt,Bind.bind,Option.bind,functionAt,hostCode]

theorem host_instruction_address_indirect {M : Type} (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (entry selector offset table type : U32)
    (tableAddress : runtime.TableAddr) (object : runtime.store.TableInst) (word reference : U64)
    (address : Usize) (function : runtime.store.FuncInst) (signature : Usize) (host : U64)
    (pairAt : compiled.indirect.val[entry.val]?=some (table,type))
    (tableAt : inst.tables.val[table.val]?=some tableAddress)
    (objectAt : store.tables.val[tableAddress.index.val]?=some object)
    (wordAt : exec.slots.val[raw.base.val+selector.val]?=some word)
    (referenceAt : object.elements.val[(UScalar.cast .U32 word).val]?=some reference)
    (nonzero : reference≠0#u64) (indexEq : (UScalar.cast .Usize reference).val=address.val+1)
    (functionAt : store.funcs.val[address.val]?=some function)
    (signatureAt : inst.types.val[type.val]?=some signature) (same : function.signature=signature)
    (hostCode : function.code=.Host host) :
    hostInstructionAddress exec store raw inst compiled (.CallIndirect entry selector offset)=some ⟨store.id,address⟩ := by
  have nz : ¬(UScalar.cast .Usize reference).val=0 := by omega
  simp only [hostInstructionAddress,pairAt,Bind.bind,Option.bind,tableAt,objectAt,wordAt,referenceAt,nonzero,ite_false,nz]
  have sub : (UScalar.cast .Usize reference).val-1=address.val := by omega
  have equal (bound : (UScalar.cast .Usize reference).val-1<2^UScalarTy.Usize.numBits) :
      UScalar.ofNatCore ((UScalar.cast .Usize reference).val-1) bound=address := by
    apply UScalar.eq_of_val_eq
    simpa only [UScalar.ofNatCore_val_eq] using sub
  simp only [equal,functionAt,Bind.bind,Option.bind,signatureAt,same,ite_true,hostCode]
end Itasca.Runtime.Interp

end

/-! ## StepRecordingInversion -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem host_instruction_address_call_tag {M : Type} (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (instruction : runtime.bytecode.Instr)
    (address : runtime.FuncAddr) (selected : hostInstructionAddress exec store raw inst compiled instruction=some address) :
    Compiler.callTag instruction≠0 := by
  cases instruction <;> first | (simp [Compiler.callTag]; done) | (simp only [hostInstructionAddress,Bind.bind,Option.bind] at selected; cases selected)

theorem host_instruction_address_direct_inv {M : Type} (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (index offset : U32)
    (address : runtime.FuncAddr) (selected : hostInstructionAddress exec store raw inst compiled (.Call index offset)=some address) :
    ∃function host, inst.funcs.val[index.val]?=some address ∧
      store.funcs.val[address.index.val]?=some function ∧ function.code=.Host host := by
  cases addressAt : inst.funcs.val[index.val]? with
  | none => simp [hostInstructionAddress,addressAt,Bind.bind,Option.bind] at selected
  | some actual =>
    cases functionAt : store.funcs.val[actual.index.val]? with
    | none => simp [hostInstructionAddress,addressAt,functionAt,Bind.bind,Option.bind] at selected
    | some function =>
      cases hostCode : function.code with
      | Wasm => simp [hostInstructionAddress,addressAt,functionAt,hostCode,Bind.bind,Option.bind] at selected
      | Host host =>
        have same : actual=address := by simpa [hostInstructionAddress,addressAt,functionAt,hostCode,Bind.bind,Option.bind] using selected
        subst actual
        exact ⟨function,host,rfl,functionAt,hostCode⟩

theorem host_instruction_address_indirect_inv {M : Type} (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (entry selector offset table type : U32)
    (tableAddress : runtime.TableAddr) (object : runtime.store.TableInst) (word : U64) (signature : Usize)
    (pairAt : compiled.indirect.val[entry.val]?=some (table,type))
    (tableAt : inst.tables.val[table.val]?=some tableAddress)
    (objectAt : store.tables.val[tableAddress.index.val]?=some object)
    (wordAt : exec.slots.val[raw.base.val+selector.val]?=some word)
    (signatureAt : inst.types.val[type.val]?=some signature)
    (address : runtime.FuncAddr) (selected : hostInstructionAddress exec store raw inst compiled (.CallIndirect entry selector offset)=some address) :
    ∃ reference function host,
      object.elements.val[(UScalar.cast .U32 word).val]?=some reference ∧ reference≠0#u64 ∧
      (UScalar.cast .Usize reference).val=address.index.val+1 ∧ address.store=store.id ∧
      store.funcs.val[address.index.val]?=some function ∧ function.signature=signature ∧ function.code=.Host host := by
  simp only [hostInstructionAddress,pairAt,Bind.bind,Option.bind,tableAt,objectAt,wordAt] at selected
  cases referenceAt : object.elements.val[(UScalar.cast .U32 word).val]? with
  | none => simp only [referenceAt,Option.bind] at selected; cases selected
  | some reference =>
    simp only [referenceAt] at selected
    split at selected
    · simp at selected
    · rename_i nonzero
      split at selected
      · simp at selected
      · rename_i positive
        let target : Usize := UScalar.ofNatCore ((UScalar.cast .Usize reference).val-1) (by have := (UScalar.cast .Usize reference).hBounds;omega)
        change (Option.bind (store.funcs.val[target.val]?) (fun (function : runtime.store.FuncInst) =>
          Option.bind (inst.types.val[type.val]?) (fun wanted => if function.signature=wanted then
            Option.bind (store.funcs.val[target.val]?) (fun (function : runtime.store.FuncInst) =>
              match function.code with | .Host _ => some (⟨store.id,target⟩ : runtime.FuncAddr) | .Wasm .. => none)
            else none)))=some address at selected
        cases functionAt : store.funcs.val[target.val]? with
        | none => simp [functionAt] at selected
        | some function =>
          simp only [functionAt,Option.bind,signatureAt] at selected
          split at selected
          · rename_i same
            cases hostCode : function.code with
            | Wasm => simp [hostCode] at selected
            | Host host =>
              have equal : (⟨store.id,target⟩ : runtime.FuncAddr)=address := by simpa [hostCode] using selected
              subst address
              refine ⟨reference,function,host,rfl,nonzero,?_,rfl,functionAt,same,hostCode⟩
              change (UScalar.cast .Usize reference).val=(UScalar.cast .Usize reference).val-1+1
              omega
          · simp at selected
theorem host_step_address_instruction {M : Type} (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (last : index.val+1=exec.frames.length) (frameAt : exec.frames.val[index.val]?=some raw)
    (instanceAt : store.instances.val[raw.instance.val]?=some inst)
    (compiledAt : inst.module.functions.val[raw.function.val]?=some compiled)
    (address : runtime.FuncAddr) (selected : hostStepAddress exec store=some address) :
    ∃instruction, compiled.code.val[raw.pc.val]?=some instruction ∧
      hostInstructionAddress exec store raw inst compiled instruction=some address := by
  have indexEq : exec.frames.length-1=index.val := by omega
  simp only [hostStepAddress,indexEq,frameAt,instanceAt,compiledAt,Bind.bind,Option.bind] at selected
  cases found : compiled.code.val[raw.pc.val]? with
  | none => simp [found] at selected
  | some instruction => exact ⟨instruction,rfl,by simpa only [found,Option.bind] using selected⟩
end Itasca.Runtime.Interp

end

/-! ## ArgumentRejectionKind -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem check_argument_error_kind {id value ty error}
    (rejected : checkArgument id value ty = .Err error) :
    error = .BadArguments ∨ error = .WrongStore := by
  unfold checkArgument at rejected
  split at rejected
  · split at rejected <;> simp_all
  · simp_all

theorem check_arguments_error_kind {id values types error}
    (rejected : checkArguments id values types = .Err error) :
    error = .BadArguments ∨ error = .WrongStore := by
  induction values generalizing types with
  | nil => cases types <;> simp_all [checkArguments]
  | cons value values ih =>
    cases types with
    | nil => simp_all [checkArguments]
    | cons ty types =>
      cases checked : checkArgument id value ty with
      | Ok unitValue => exact ih (by simpa only [checkArguments,checked] using rejected)
      | Err failed =>
        have same : failed = error := by simpa only [checkArguments,checked,core.result.Result.Err.injEq] using rejected
        subst failed
        exact check_argument_error_kind checked

theorem check_values_error_kind {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (args : Slice runtime.Value) (types : Slice Itasca.wasm_types.ValueType)
    (error : runtime.ExecError)
    (rejected : runtime.interp.check_values memory store args types = .ok (.Err error)) :
    error = .BadArguments ∨ error = .WrongStore := by
  have decision := check_values_effect memory store args types
  rw [rejected,WP.spec_ok] at decision
  split at decision
  · exact check_arguments_error_kind decision.symm
  · simpa only [core.result.Result.Err.injEq] using Or.inl decision
end Itasca.Runtime.Interp

end
