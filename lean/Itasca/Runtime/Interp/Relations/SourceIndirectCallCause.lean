import Itasca.Runtime.Interp.Relations.SourceCallCause
import Itasca.Runtime.Abs.Indirect.Definition
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- A rejected indirect call retains both the actual selected callee and the
source argument region. The table selector is consumed before callee entry. -/
def SourceIndirectCallCause {A M P : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (code : Store.CodeInterpretation) (before : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (frameIndex : Usize)
    (raw : runtime.interp.Frame) (callerCode : runtime.bytecode.CompiledFunction)
    (source : Abs.AState) (error : runtime.ExecError) : Prop :=
  ∃ (entry selector offset table type pc : U32) (address base : Usize)
    (function : runtime.store.FuncInst) (instanceIndex functionIndex : Usize)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction),
    callerCode.code.val[raw.pc.val]?=some (.CallIndirect entry selector offset) ∧
    callerCode.indirect.val[entry.val]?=some (table,type) ∧
    store.funcs.val[address.val]?=some function ∧ function.code=.Wasm instanceIndex functionIndex ∧
    store.instances.val[instanceIndex.val]?=some inst ∧ inst.module.functions.val[functionIndex.val]?=some compiled ∧
    base.val=raw.base.val+offset.val ∧ pc.val=raw.pc.val+1 ∧
    CallCause allocator hooks {before with frames:=before.frames.set frameIndex {raw with pc:=pc}}
      store platform base compiled error ∧
    ∃ (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (front args : List val)
      (position : Nat) (params results : List valtype) (count : Nat),
      Spec.StepsHN count (Abs.decode source) [] (Abs.decode ⟨source.store,source.ambient,
        {f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩) ∧
      f.vals=(front++args)++[Abs.integerVal .I32 position] ∧ position<2^32 ∧
      Abs.Indirect.resolve source.store f table.val type.val position=some address.val ∧
      (Store.decodeFunction code store function).TYPE=⟨.mk_list params,.mk_list results⟩ ∧
      args.map Code.valueType=params ∧
      offset.val=Code.slots ((f.locals++front).map Code.valueType) ∧
      raw.base.val=suspendedSourceWords rest
theorem SourceIndirectCallCause.prepend {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {code : Store.CodeInterpretation} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {frameIndex : Usize} {raw : runtime.interp.Frame}
    {compiled : runtime.bytecode.CompiledFunction} {before after : Abs.AState} {error : runtime.ExecError} {count}
    (steps : Spec.StepsHN count (Abs.decode before) [] (Abs.decode after))
    (sameStore : after.store=before.store) (sameAmbient : after.ambient=before.ambient)
    (cause : SourceIndirectCallCause allocator hooks code exec store platform frameIndex raw compiled after error) :
    SourceIndirectCallCause allocator hooks code exec store platform frameIndex raw compiled before error := by
  obtain ⟨entry,selector,offset,table,type,pc,address,base,function,instanceIndex,functionIndex,inst,callee,
    fetch,pair,functionAt,defined,instanceAt,calleeAt,baseEq,pcEq,rejected,
    f,rest,source,front,args,position,params,results,tailCount,tail,values,bounded,resolved,signature,arguments,coordinates,sourceBase⟩ := cause
  refine ⟨entry,selector,offset,table,type,pc,address,base,function,instanceIndex,functionIndex,inst,callee,
    fetch,pair,functionAt,defined,instanceAt,calleeAt,baseEq,pcEq,rejected,
    f,rest,source,front,args,position,params,results,count+tailCount,?_,values,bounded,?_,signature,arguments,coordinates,sourceBase⟩
  · simpa only [sameStore,sameAmbient,List.nil_append] using steps.trans tail
  · simpa only [sameStore] using resolved
end Itasca.Runtime.Interp
