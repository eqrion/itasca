import Itasca.Runtime.Interp.Relations.SourceIndirectCallCause
import Itasca.Runtime.Interp.Relations.SourceValueCauses
import Itasca.Runtime.Interp.Relations.SourceCanonicalCapacity
import Itasca.Runtime.Interp.Relations.SourceAllocationCauses

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
