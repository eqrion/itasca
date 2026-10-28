import Itasca.Runtime.Interp.Relations.SourceIndirectCallCause
import Itasca.Runtime.Interp.Relations.SourceValueCauses
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- An indirect source call retains the selected callee and the shared
argument position, including storage suspended in all source callers. -/
def SourceIndirectCallSite (initial : Abs.AState) (address : funcaddr) (base : Nat) : Prop :=
  ∃ (f : Abs.AFrame) (rest : List Abs.AFrame) (table type position : Nat) (after : List instr)
    (front args : List val) (callee : funcinst) (params results : List valtype) (count : Nat),
    Spec.StepsHN count (Abs.decode initial) [] (Abs.decode ⟨initial.store,initial.ambient,
      {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩) ∧
    f.vals=(front++args)++[Abs.integerVal .I32 position] ∧ position<2^32 ∧
    Abs.Indirect.resolve initial.store f table type position=some address ∧
    initial.store.FUNCS[address]?=some callee ∧
    callee.TYPE=⟨.mk_list params,.mk_list results⟩ ∧ args.map Code.valueType=params ∧
    base=suspendedSourceWords rest+Code.slots ((f.locals++front).map Code.valueType)

theorem SourceIndirectCallSite.prepend {before middle : Abs.AState} {address base count}
    (steps : Spec.StepsHN count (Abs.decode before) [] (Abs.decode middle))
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
    {source : Abs.AState} {error : runtime.ExecError}
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
