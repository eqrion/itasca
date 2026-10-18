import Exec.Interp.StructuredMachine.UniformAdvance
import Exec.Interp.Machines.Uniform.UniformSourceControl
import Exec.Interp.StructuredMachine.SupportedAdvance
import Exec.Interp.StructuredMachine.CallLookup
import Exec.Interp.StructuredMachine.StructuredCall
import Exec.Interp.Calls.IndirectCallNext
import Exec.Abs.Indirect.Results
import Exec.Abs.Indirect.Correct
import Exec.Abs.Indirect.Transport
namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std

/-- A resolved defined indirect call reuses the actual call installer while
saving the caller after consuming both its arguments and table selector. -/
theorem call_indirect_selected_uniform {emission : FunctionEmission} {allowed : instr → Prop}
    (language : Abs.Supported.Language allowed) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (table type position : Nat) (after : List instr)
    (front args : List val) (params results : List valtype) (pc : U32) (base : Usize)
    (address : runtime.FuncAddr) (function : runtime.store.Function) (instanceIndex functionIndex : Usize)
    (compiledFunctions : StructuredMachine.CompiledFunctions emission code store)
    (functionTyping : CoreFunctionsTyped view code store)
    (functionAt : store.funcs.val[address.index.val]? = some function)
    (defined : function.code = .Wasm instanceIndex functionIndex)
    (selected : Abs.Indirect.resolve (Store.decodeStore view code store) f table type position = some address.index.val)
    (signature : (Store.decodeFunction code store function).TYPE = ⟨.mk_list params,.mk_list results⟩)
    (last : frameIndex.val+1=exec.frames.length) (hf : exec.frames.val[frameIndex.val]?=some raw)
    (pcNext : pc.val=raw.pc.val+1)
    (split : f.vals=(front++args)++[Abs.integerVal .I32 position]) (bounded : position<2^32)
    (argumentTypes : args.map Code.valueType=params)
    (basePosition : base.val=raw.base.val+Code.slots ((f.locals++front).map Code.valueType))
    (heights : ∀ label∈f.labels,label.height≤front.length)
    (slots : FrameSlots exec raw f)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint emission (Store.decodeStore view code store) raw {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after} compiled C targets next output)
    (tail : Code.StructuredCodeWithTables (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
      (front.map Code.valueType++results) after pc.val next output)
    (expected : List valtype)
    (machine : Execution emission (Abs.SupportedState allowed) view code store exec ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ expected raw.pc.val false) :
    runtime.interp.call memory hooks floats allocator
      {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} store platform address base ⦃ out =>
      out.2.2.1=store ∧
      (out.1=.Ok () → UniformAdvance emission (Abs.SupportedState allowed) Abs.Ownership.StatefulOwned view code store out.2.1 expected compiled.code.length raw.pc.val false
        ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩) ∧
      (∀ error,out.1=.Err error → ∃ inst callee,
        store.instances.val[instanceIndex.val]?=some inst ∧ inst.module.functions.val[functionIndex.val]?=some callee ∧
        CallCause allocator hooks {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} store platform base callee error) ⦄ := by
  have top : exec.frames.val.getLast?=some raw := by
    rw [List.getLast?_eq_getElem?]
    have position : exec.frames.val.length-1=frameIndex.val := by change exec.frames.length-1=frameIndex.val;omega
    rw [position];exact hf
  have binding := (machine.stack.top raw top).binding
  obtain ⟨inst,calleeCode,actualSignature,declared,body,epilogue,instanceAt,calleeAt,signatureAt,
    tableFunctions,certificate,calleeBindings,sourceAt⟩ :=
    compiledFunctions.defined view functionTyping address function instanceIndex functionIndex functionAt defined
  have decodedType : (Store.decodeFunction code store function).TYPE=Store.decodeFuncType actualSignature := by
    simp only [Store.decodeFunction]
    rw [List.getD_eq_getElem?_getD,List.getElem?_map,signatureAt]
    simp only [defined,instanceAt,Option.map_some,Option.getD_some]
  have signatureTypes : actualSignature.params.val.map sourceType=params ∧ actualSignature.results.val.map sourceType=results := by
    simpa only [Store.decodeFuncType,functype.mk_functype.injEq,list.mk_list.injEq] using decodedType.symm.trans signature
  have argumentTypes' : args.map Code.valueType=actualSignature.params.val.map sourceType := argumentTypes.trans signatureTypes.1.symm
  obtain ⟨defaults,default,defaultTyped⟩ := Abs.defaultLocals_typed machine.typed.typed.store declared (StructuredMachine.declared_types_not_bottom certificate)
  have exactStep := indirect_call_next (Store.decodeStore view code store) ambient f rest after table type position address.index.val
    (Store.decodeInstance store inst) (actualSignature.params.val.map sourceType) (actualSignature.results.val.map sourceType)
    declared (.mk_uN calleeCode.type_index.val) body front args defaults selected bounded sourceAt argumentTypes' default
  have sourceStep : Abs.Indirect.step
      ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ f rest table type after =
      .next ⟨Store.decodeStore view code store,ambient,callCallee address.index.val (Store.decodeInstance store inst)
        (actualSignature.results.val.map sourceType) args defaults body::{f with code:=after,vals:=front}::rest,[]⟩ := by
    simpa only [← split] using exactStep
  have transition : Abs.Cumulative.Step _ _ := .indirect sourceStep (by intro impossible;cases impossible)
  have nextTyped := transition.next_typed_supported language machine.typed machine.core
  have nextCovered := transition.next_covered_supported language machine.typed machine.core
  have arguments : ValuesAt exec.slots.val base.val args := by
    have words : WordsAt exec.slots.val raw.base.val
        (Code.encodeValues (f.locals++front) ++ (Code.encodeValues args ++ Code.encodeValues [Abs.integerVal .I32 position])) := by
      simpa only [FrameSlots,ValuesAt,split,Code.encodeValues_append,List.append_assoc] using slots
    have taken := words.append_right.append_left
    simpa only [ValuesAt,Code.encodeValues_length,basePosition] using taken
  have identity : exec.store=store.id := by
    obtain ⟨_,_,_,_,identity,_⟩ := binding
    exact identity
  have tail' : Code.StructuredCodeWithTables (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
      (front.map Code.valueType++actualSignature.results.val.map sourceType) after pc.val next output := by
    simpa only [signatureTypes.2] using tail
  obtain ⟨raws,frames,saved⟩ := machine.stack.prepare_call raw frameIndex pc last hf binding slots program point
    front (args++[Abs.integerVal .I32 position]) after (actualSignature.results.val.map sourceType) base.val
    (by simpa only [List.append_assoc] using split) basePosition heights tail'
  obtain ⟨out,returned,result⟩ := WP.spec_imp_exists (StructuredMachine.call_wasm_stack memory hooks floats allocator allocation interrupts
    {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} store platform address base function actualSignature instanceIndex functionIndex
    inst calleeCode epilogue (Store.decodeStore view code store)
    (Code.moduleFunctionContext inst.module (actualSignature.params.val.map sourceType++declared) (actualSignature.results.val.map sourceType))
    calleeBindings declared body args defaults certificate functionAt signatureAt defined instanceAt calleeAt tableFunctions identity
    arguments argumentTypes' default raws ({f with code:=after,vals:=front}::rest) frames saved)
  have causes := call_wasm_causes memory hooks floats allocator allocation interrupts
    {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} store platform address base function instanceIndex functionIndex inst calleeCode
    functionAt defined instanceAt calleeAt
    (by rw [certificate.2.parameterSlots,certificate.2.localSlots,Code.slots_append];omega) certificate.2.capacity
  rw [returned] at causes
  simp only [WP.spec_ok] at causes
  rw [returned]
  apply WP.spec.ret
  refine ⟨result.1,?_,fun error rejected => ⟨inst,calleeCode,instanceAt,calleeAt,causes error rejected⟩⟩
  intro success
  obtain ⟨stack,top,ready⟩ := result.2 success
  refine ⟨0,false,_,?_,ConcreteSim.of_source _ _ _ _ _ (transition.next_simulation_supported language machine.typed machine.core),
    UniformConcreteSim.of_steps (by omega : 0 < 2) (Abs.Indirect.next_simulation _ _ _ _ _ _ _ _ machine.typed sourceStep),
    fun _ h => transition.next_owned_supported language machine.typed machine.core h,rfl,fun _ h => transition.next_bound_supported language machine.typed machine.core h⟩
  refine ⟨rfl,nextTyped,nextCovered,Abs.Indirect.step_result machine.result sourceStep,stack,?_⟩
  obtain ⟨head,code,C,targets,next,output,found,program,point⟩ := ready
  have same : head.pc.val=0 := by rw [top] at found;cases found;rfl
  exact ⟨head,code,C,targets,next,output,found,same,program,.ready point⟩
end Exec.Interp.StructuredMachine
