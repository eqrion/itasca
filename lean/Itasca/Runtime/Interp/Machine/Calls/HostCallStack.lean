import Itasca.Runtime.Interp.Machine.Progress.SupportedAdvance
import Itasca.Runtime.Interp.Machine.Calls.CallStackEntry
import Itasca.Runtime.Interp.Machine.Calls.IndirectOperands
import Itasca.Runtime.Interp.Calls.IndirectResolve
import Itasca.Runtime.SourceMachine.Indirect.HostSimulation
import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.Interp.Host.HostReturnFrames
import Itasca.Runtime.Interp.Machine.Frames.FrameDepth

/-!
Sections, each formerly its own module: IndirectSelected, CallExecution, HostReturnFrames, HostCallStack.
-/

/-! ## IndirectSelected -/

section

/-!
A resolved defined indirect call reuses the actual call installer while saving the caller after consuming both its arguments and table selector.

Main declarations: `call_indirect_selected`. A direct consumer is `Integration.Execution.Dispatch.IndirectExecution`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

/-- A resolved defined indirect call reuses the actual call installer while
saving the caller after consuming both its arguments and table selector. -/
theorem call_indirect_selected
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (table type position : Nat) (after : List instr)
    (front args : List val) (params results : List valtype) (pc : U32) (base : Usize)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (instanceIndex functionIndex : Usize)
    (compiledFunctions : Machine.CompiledFunctions code store)
    (functionTyping : CoreFunctionsTyped view code store)
    (functionAt : store.funcs.val[address.index.val]? = some function)
    (defined : function.code = .Wasm instanceIndex functionIndex)
    (selected : SourceMachine.Indirect.resolve (Store.decodeStore view code store) f table type position = some address.index.val)
    (signature : (Store.decodeFunction code store function).TYPE = ⟨.mk_list params,.mk_list results⟩)
    (last : frameIndex.val+1=exec.frames.length) (hf : exec.frames.val[frameIndex.val]?=some raw)
    (pcNext : pc.val=raw.pc.val+1)
    (split : f.vals=(front++args)++[SourceMachine.integerVal .I32 position]) (bounded : position<2^32)
    (argumentTypes : args.map Compiler.valueType=params)
    (basePosition : base.val=raw.base.val+Compiler.slots ((f.locals++front).map Compiler.valueType))
    (heights : ∀ label∈f.labels,label.height≤front.length)
    (slots : FrameSlots exec raw f)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after} compiled C targets next output)
    (tail : Compiler.StructuredCode (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
      (front.map Compiler.valueType++results) after pc.val next output)
    (expected : List valtype)
    (machine : Execution view code store exec ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ expected raw.pc.val false) :
    runtime.interp.call memory hooks floats allocator
      {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} store platform address base ⦃ out =>
      out.2.2.1=store ∧
      (out.1=.Ok () → Advance view code store out.2.1 expected compiled.code.length raw.pc.val false
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
  have argumentTypes' : args.map Compiler.valueType=actualSignature.params.val.map sourceType := argumentTypes.trans signatureTypes.1.symm
  obtain ⟨defaults,default,defaultTyped⟩ := SourceMachine.default_locals_typed machine.typed.typed.store declared (Machine.declared_types_not_bottom certificate)
  have exactStep := indirect_call_next (Store.decodeStore view code store) ambient f rest after table type position address.index.val
    (Store.decodeInstance store inst) (actualSignature.params.val.map sourceType) (actualSignature.results.val.map sourceType)
    declared (.mk_uN calleeCode.type_index.val) body front args defaults selected bounded sourceAt argumentTypes' default
  have sourceStep : SourceMachine.Indirect.step
      ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ f rest table type after =
      .next ⟨Store.decodeStore view code store,ambient,callCallee address.index.val (Store.decodeInstance store inst)
        (actualSignature.results.val.map sourceType) args defaults body::{f with code:=after,vals:=front}::rest,[]⟩ := by
    simpa only [← split] using exactStep
  have transition : SourceMachine.Cumulative.Step _ _ := .indirect sourceStep (by intro impossible;cases impossible)
  have nextTyped := transition.next_typed_supported machine.typed machine.core
  have nextCovered := transition.next_covered_supported machine.typed machine.core
  have arguments : ValuesAt exec.slots.val base.val args := by
    have words : WordsAt exec.slots.val raw.base.val
        (Compiler.encodeValues (f.locals++front) ++ (Compiler.encodeValues args ++ Compiler.encodeValues [SourceMachine.integerVal .I32 position])) := by
      simpa only [FrameSlots,ValuesAt,split,Compiler.encode_values_append,List.append_assoc] using slots
    have taken := words.append_right.append_left
    simpa only [ValuesAt,Compiler.encode_values_length,basePosition] using taken
  have identity : exec.store=store.id := by
    obtain ⟨_,_,_,_,identity,_⟩ := binding
    exact identity
  have tail' : Compiler.StructuredCode (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
      (front.map Compiler.valueType++actualSignature.results.val.map sourceType) after pc.val next output := by
    simpa only [signatureTypes.2] using tail
  obtain ⟨raws,frames,saved⟩ := machine.stack.prepare_call raw frameIndex pc last hf binding slots program point
    front (args++[SourceMachine.integerVal .I32 position]) after (actualSignature.results.val.map sourceType) base.val
    (by simpa only [List.append_assoc] using split) basePosition heights tail'
  obtain ⟨out,returned,result⟩ := WP.spec_imp_exists (Machine.call_wasm_stack memory hooks floats allocator allocation interrupts
    {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} store platform address base function actualSignature instanceIndex functionIndex
    inst calleeCode epilogue (Store.decodeStore view code store)
    (Compiler.moduleFunctionContext inst.module (actualSignature.params.val.map sourceType++declared) (actualSignature.results.val.map sourceType))
    calleeBindings declared body args defaults certificate functionAt signatureAt defined instanceAt calleeAt tableFunctions identity
    arguments argumentTypes' default raws ({f with code:=after,vals:=front}::rest) frames saved)
  have causes := call_wasm_causes memory hooks floats allocator allocation interrupts
    {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} store platform address base function instanceIndex functionIndex inst calleeCode
    functionAt defined instanceAt calleeAt
    (by rw [certificate.2.parameterSlots,certificate.2.localSlots,Compiler.slots_append];omega) certificate.2.capacity
  rw [returned] at causes
  simp only [WP.spec_ok] at causes
  rw [returned]
  apply WP.spec.ret
  refine ⟨result.1,?_,fun error rejected => ⟨inst,calleeCode,instanceAt,calleeAt,causes error rejected⟩⟩
  intro success
  obtain ⟨stack,top,ready⟩ := result.2 success
  refine ⟨0,false,_,?_,ConcreteSim.of_source _ _ _ _ _ (transition.next_simulation_supported machine.typed machine.core),
    fun _ h => transition.next_owned_supported machine.typed machine.core h,rfl,fun _ h => transition.next_bound_supported machine.typed machine.core h⟩
  refine ⟨rfl,nextTyped,nextCovered,SourceMachine.Indirect.step_result machine.result sourceStep,stack,?_⟩
  obtain ⟨head,code,C,targets,next,output,found,program,point⟩ := ready
  have same : head.pc.val=0 := by rw [top] at found;cases found;rfl
  exact ⟨head,code,C,targets,next,output,found,same,program,.ready point⟩
end Itasca.Runtime.Interp.Machine

end

/-! ## CallExecution -/

section

/-!
Direct-call execution in the structured machine.

Main declarations: `step_call_execution`. A direct consumer is `Integration.Execution.Dispatch.Host`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

theorem step_call_execution {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (caller : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)] (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (index : U32) (after : List instr)
    (compiledFunctions : CompiledFunctions code store) (functionTyping : CoreFunctionsTyped view code store)
    (last : frameIndex.val+1 = exec.frames.length) (hf : exec.frames.val[frameIndex.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some caller)
    (hc : caller.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .CALL (.mk_uN index.val)::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .CALL (.mk_uN index.val)::after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .CALL (.mk_uN index.val)::after}::rest,[]⟩
    (∃ address function host offset, compiled.code.val[raw.pc.val]? = some (.Call index offset) ∧
      caller.funcs.val[index.val]? = some address ∧ store.funcs.val[address.index.val]? = some function ∧ function.code = .Host host) ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧
      (out.1 = .Ok () → ∃ pc source,
        Execution view code store out.2.1 source expected pc false ∧
        ConcreteSim compiled.code.length raw.pc.val pc false false initial source ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds source) ∧ source.ambient = ambient ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound source)) ∧
      (∀ error, out.1 = .Err error → SourceDirectCallCause allocator hooks exec store platform frameIndex raw caller compiled initial error) ⦄ := by
  dsimp only
  have top : exec.frames.val.getLast? = some raw := by
    rw [List.getLast?_eq_getElem?]
    have position : exec.frames.val.length-1 = frameIndex.val := by change exec.frames.length-1 = frameIndex.val; omega
    rw [position]; exact hf
  have binding := (machine.stack.top raw top).binding
  rcases step_call_structured memory hooks floats allocator allocation interrupts view code exec store platform frameIndex raw caller compiled
    C targets next output (Store.decodeStore view code store) ambient f rest index after rfl compiledFunctions functionTyping last hf hi hc
    machine.typed.typed machine.core binding slots program point machine.stack with host | operation
  · exact Or.inl host
  · apply Or.inr
    apply WP.spec_mono operation
    intro out effect
    refine ⟨effect.1,?_,effect.2.2⟩
    intro success
    obtain ⟨pc,frames,top,stack,typed,covered,simulation,ready,result,ownedHere,bounded⟩ := effect.2.1 success
    obtain ⟨current,cursor⟩ := ready.cursor
    have same : current = pc.val := by
      cases frames with
      | nil =>
        cases stack with
        | empty empty => simp [empty] at top
      | cons frame rest =>
        have actual := cursor.pc
        have eq := congrArg (Option.map (fun value : U32 => value.val)) top
        simp only [Option.map_map,Option.map_some,Function.comp_def] at eq
        rw [actual] at eq
        exact Option.some.inj eq
    subst current
    exact ⟨pc.val,_,⟨rfl,⟨typed,machine.typed.contents⟩,covered,result expected machine.result,stack,cursor⟩,simulation,ownedHere,rfl,bounded⟩
end Itasca.Runtime.Interp.Machine

end

/-! ## HostReturnFrames -/

section

/-!
Resuming saved frames after a host call returns.

Main declarations: `SavedFrame.resume_host` and `host_return_stack`. A direct consumer is `Interp.Machine.Calls.HostCallStack`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

theorem SavedFrame.resume_host {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {before after : runtime.interp.Execution} {base : Nat} {raw : runtime.interp.Frame}
    {source : SourceMachine.AFrame} {waiting : List valtype} {results : List val}
    (saved : SavedFrame store sourceStore before raw source waiting base)
    (effect : HostReturnEffect before after base results)
    (types : results.map Compiler.valueType = waiting) (heights : SourceMachine.FrameHeights source) :
    ActiveFrame store sourceStore after raw {source with vals := source.vals ++ results} := by
  refine ⟨effect.preserve_binding saved.binding,effect.resume saved.slots saved.destination,?_⟩
  obtain ⟨compiled,functions,targets,next,output,program,point⟩ := saved.continuation
  exact ⟨compiled,functions,targets,next,output,false,program,.ready (point.resume results types heights)⟩

theorem SavedFrames.host_preserved {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {before after : runtime.interp.Execution} {base : Nat} {results : List val}
    {raws sources waiting boundary}
    (saved : SavedFrames store sourceStore before raws sources waiting boundary)
    (effect : HostReturnEffect before after base results) (below : boundary ≤ base) :
    SavedFrames store sourceStore after raws sources waiting boundary := by
  apply saved.transport
  · intro raw source binding member
    exact effect.preserve_binding binding
  · intro position bits represented bound
    exact effect.preserve_prefix represented (bound.trans below)

/-- A synchronous host call does not push a concrete Wasm frame. Its waiting
caller becomes active again after the checked result write, while every older
caller keeps its own saved continuation. -/
theorem host_return_stack {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {before after : runtime.interp.Execution} {base : Nat} {results : List val}
    {raw : runtime.interp.Frame} {raws : List runtime.interp.Frame}
    {caller : SourceMachine.AFrame} {rest : List SourceMachine.AFrame} {waiting : List valtype}
    (frames : before.frames.val = raws.reverse ++ [raw])
    (saved : SavedFrame store sourceStore before raw caller waiting base)
    (older : SavedFrames store sourceStore before raws rest caller.resultTypes raw.base.val)
    (effect : HostReturnEffect before after base results)
    (types : results.map Compiler.valueType = waiting) (heights : SourceMachine.FrameHeights caller) :
    FrameStackRel store sourceStore after ({caller with vals := caller.vals ++ results} :: rest) ∧
      ReadyTop store sourceStore after {caller with vals := caller.vals ++ results} := by
  refine ⟨.active (by simpa only [effect.frames] using frames)
    (saved.resume_host effect types heights) (older.host_preserved effect saved.base_le),?_⟩
  obtain ⟨compiled,functions,targets,next,output,program,point⟩ := saved.continuation
  refine ⟨raw,compiled,functions,targets,next,output,?_,program,point.resume results types heights⟩
  simp only [effect.frames,frames,List.getLast?_concat]

end Itasca.Runtime.Interp.Machine

end

/-! ## HostCallStack -/

section

/-!
Resuming saved frames after a host call. Saved-frame transport and extended code/store facts reconstruct the suspended frame-stack relation.
-/

/-! ## Host Saved Frames Resume -/

section

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

/-- Consume exactly the suspended stack produced by prepare_call. A host
callee contributes no concrete frame, so the saved head resumes directly. -/
theorem SavedFrames.resume_host {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {before after : runtime.interp.Execution} {base : Nat} {results : List val}
    {raws : List runtime.interp.Frame} {caller : SourceMachine.AFrame} {rest : List SourceMachine.AFrame}
    {waiting : List valtype}
    (saved : SavedFrames store sourceStore before raws (caller :: rest) waiting base)
    (frames : before.frames.val = raws.reverse)
    (effect : HostReturnEffect before after base results)
    (types : results.map Compiler.valueType = waiting) (heights : SourceMachine.FrameHeights caller) :
    FrameStackRel store sourceStore after ({caller with vals := caller.vals ++ results} :: rest) ∧
      ReadyTop store sourceStore after {caller with vals := caller.vals ++ results} := by
  cases saved with
  | cons head tail =>
    exact host_return_stack (by simpa only [List.reverse_cons] using frames) head tail effect types heights

theorem SavedFrames.resume_host_extended {M : Type} {beforeStore afterStore : runtime.store.Store M}
    {oldSource newSource : _root_.store}
    (retained : FrameStorePrefix beforeStore afterStore) (bounds : FrameTypeBounds beforeStore)
    (extension : Extend_store oldSource newSource)
    {before after : runtime.interp.Execution} {base : Nat} {results : List val}
    {raws : List runtime.interp.Frame} {caller : SourceMachine.AFrame} {rest : List SourceMachine.AFrame}
    {waiting : List valtype}
    (saved : SavedFrames beforeStore oldSource before raws (caller :: rest) waiting base)
    (frames : before.frames.val = raws.reverse)
    (effect : HostReturnEffect before after base results)
    (types : results.map Compiler.valueType = waiting) (heights : SourceMachine.FrameHeights caller) :
    FrameStackRel afterStore newSource after ({caller with vals := caller.vals ++ results} :: rest) ∧
      ReadyTop afterStore newSource after {caller with vals := caller.vals ++ results} :=
  (saved.store_prefix_extension retained bounds extension).resume_host frames effect types heights
end Itasca.Runtime.Interp.Machine

end

/-! ## Host Call Stack -/

section

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

/-- Actual caller PC advancement and checked host result writes compose into
the full resumed concrete stack under retained raw metadata and source extension. -/
theorem FrameStackRel.host_call_return {M : Type} {store : runtime.store.Store M} {s : _root_.store}
    {exec : runtime.interp.Execution} {source : SourceMachine.AFrame} {rest : List SourceMachine.AFrame}
    (relation : FrameStackRel store s exec (source :: rest))
    (raw : runtime.interp.Frame) (index : Usize) (pc : U32)
    (last : index.val + 1 = exec.frames.length)
    (lookup : exec.frames.val[index.val]? = some raw)
    (binding : FrameBinding store exec raw source)
    (slots : FrameSlots exec raw source)
    {compiled C targets next output}
    (program : FrameProgram store raw compiled (source.locals.map Compiler.valueType) source.resultTypes C.FUNCS)
    (point : FramePoint s raw source compiled C targets next output)
    (front args : List val) (after : List instr) (returns : List valtype) (base : Nat)
    (split : source.vals = front ++ args)
    (destination : base = raw.base.val + Compiler.slots ((source.locals ++ front).map Compiler.valueType))
    (heights : ∀ label ∈ source.labels, label.height ≤ front.length)
    (continuation : Compiler.StructuredCode (emission compiled C) C.TYPES C.FUNCS source.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
      (front.map Compiler.valueType ++ returns) after pc.val next output)
    (afterStore : runtime.store.Store M) (sourceAfter : _root_.store)
    (retained : FrameStorePrefix store afterStore) (bounds : FrameTypeBounds store)
    (extension : Extend_store s sourceAfter)
    (finished : runtime.interp.Execution) (values : List val)
    (effect : HostReturnEffect {exec with frames := exec.frames.set index {raw with pc := pc}} finished base values)
    (typed : values.map Compiler.valueType = returns) :
    FrameStackRel afterStore sourceAfter finished
      ({source with code := after,vals := front ++ values} :: rest) ∧
      ReadyTop afterStore sourceAfter finished {source with code := after,vals := front ++ values} := by
  obtain ⟨raws,frames,saved⟩ := relation.prepare_call raw index pc last lookup binding slots program point
    front args after returns base split destination heights continuation
  exact saved.resume_host_extended retained bounds extension frames effect typed heights

end Itasca.Runtime.Interp.Machine

end

end
