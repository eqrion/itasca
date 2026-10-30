import Itasca.Runtime.Integration.Host.HostIndirectSelected
import Itasca.Runtime.Integration.Host.HostCallRetainedWorld
import Itasca.Runtime.Integration.Execution.World.ExecutionCode
import Itasca.Runtime.Integration.Host.HostDispatchCauses
namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp
open Itasca.Runtime.Interp.Machine

theorem call_indirect_host_structured_world {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (certify : ∀ c s, Inv c s → CertifiedSupportedStore view c s)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv code store)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (table type position : Nat) (after : List instr)
    (front args : List val) (params results : List valtype) (pc : U32) (base : Usize)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (host : U64) (signature : Itasca.wasm_types.FuncType)
    (functionAt : store.funcs.val[address.index.val]?=some function) (hostCode : function.code=.Host host)
    (signatureAt : store.types.val[function.signature.val]?=some signature)
    (signatureTypes : signature.params.val.map sourceType=params ∧ signature.results.val.map sourceType=results)
    (selected : SourceMachine.Indirect.resolve (Store.decodeStore view code store) f table type position=some address.index.val)
    (last : frameIndex.val+1=exec.frames.length) (hf : exec.frames.val[frameIndex.val]?=some raw)
    (split : f.vals=(front++args)++[SourceMachine.integerVal .I32 position]) (bounded : position<2^32)
    (argumentTypes : args.map Compiler.valueType=params)
    (basePosition : base.val=raw.base.val+Compiler.slots ((f.locals++front).map Compiler.valueType))
    (heights : ∀label∈f.labels,label.height≤front.length)
    (binding : FrameBinding store exec raw f) (slots : FrameSlots exec raw f)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint (Store.decodeStore view code store) raw
      {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after} compiled C targets next output)
    (tail : Compiler.StructuredCode (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (front.map Compiler.valueType++results) after pc.val next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ expected raw.pc.val false)
    (owned : SourceMachine.Ownership.StateOwned (Store.ownershipBounds store)
      ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩)
    (callback : ∀ p args results,
      hooks.call_host p store host args results ⦃ answer => ∃ afterCode,
        Store.CodeAgreesOn store code afterCode ∧ Inv afterCode answer.2.2.1 ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode answer.2.2.1) ∧
        Store_ok (Store.decodeStore view afterCode answer.2.2.1) ⦄div)
    (retains : HostRetention hooks store host) :
    DivSpec (HostDiverges hooks store) (runtime.interp.call memory hooks floats allocator {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} store platform address base) fun out =>
      ∃afterCode,Store.CodeAgreesOn store code afterCode ∧ Inv afterCode out.2.2.1 ∧ CertifiedSupportedStore view afterCode out.2.2.1 ∧ FrameStorePrefix store out.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode out.2.2.1) ∧
      store.externs.length≤out.2.2.1.externs.length ∧
      HostSignatureSite ⟨Store.decodeStore view code store,ambient,
        {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ address.index.val host.val signature base.val ∧
      HostCallCauses allocator hooks {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} store platform signature base host out ∧
      ((∃error,out.1=.Err error ∧ HostPreparationCause allocator hooks
          {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} store platform signature base error ∧ out.2.2.1=store ∧ hostCallEvents address out=[]) ∨
       ((out.1=.Ok () ∨ out.1=.Err (.Trap .Host) ∨ out.1=.Err (.Exhausted .CallStack)) ∧
        (∃n,2≤n ∧ Spec.StepsHN n
          (SourceMachine.decode ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩)
          (hostCallEvents address out) (hostCallFrameResult view afterCode ambient f rest after front out)) ∧
        (out.1=.Ok () → ∃finalPC,Execution view afterCode out.2.2.1 out.2.1
          ⟨Store.decodeStore view afterCode out.2.2.1,ambient,{f with code:=after,vals:=front++out.2.1.host_results.val.map sourceValue}::rest,[]⟩ expected finalPC false ∧
          SourceMachine.Ownership.ValuesOwned (Store.ownershipBounds out.2.2.1) (out.2.1.host_results.val.map sourceValue)))) := by
  have certified := certify code store valid
  have argumentTypes' := argumentTypes.trans signatureTypes.1.symm
  have hostSource := Store.decode_host_function view code store address function host signature functionAt hostCode signatureAt
  have exactStep := structured_indirect_host_next (Store.decodeStore view code store) ambient f rest after table type position address.index.val host.val
    (signature.params.val.map sourceType) (signature.results.val.map sourceType) front args selected bounded hostSource argumentTypes'
  rw [←split] at exactStep
  obtain ⟨pending,identity,sourceParams,sourceFront,sourcePosition,sourceHost,argumentTyped,sourceSplit,resumeEq,
      target,tableBound,typeBound,positionBound,frameWf,labels,frontWf,sourceTail,callers,sourceHeights⟩ :=
    SourceMachine.Indirect.host_preparation _ ambient f rest table type after address.index.val args _ _ machine.typed.typed exactStep
  have sameTypes : sourceParams=signature.params.val.map sourceType := by
    have tags := SourceMachine.results_type_of_typed argumentTyped
    have equal : SourceMachine.valueType=Compiler.valueType := (funext value_type_eq_abs).symm
    rw [equal,argumentTypes'] at tags
    exact tags.symm
  rw [sameTypes] at argumentTyped
  have frontEq : sourceFront=front := by
    have valsEq := congrArg (fun st : SourceMachine.AState => (st.frames.head!).vals) resumeEq
    simpa using valsEq.symm
  subst sourceFront
  have positionEq : sourcePosition=position := by
    have valsEq := sourceSplit.symm.trans split
    have valueEq := List.append_cancel_left valsEq
    simpa only [List.cons.injEq,SourceMachine.integerVal,val.CONST.injEq,num_.mk_num__0.injEq,uN.mk_uN.injEq,true_and,and_true] using valueEq
  subst sourcePosition
  have arguments : ValuesAt exec.slots.val base.val args := by
    have words : WordsAt exec.slots.val raw.base.val
        (Compiler.encodeValues (f.locals++front)++(Compiler.encodeValues args++Compiler.encodeValues [SourceMachine.integerVal .I32 position])) := by
      simpa only [FrameSlots,ValuesAt,split,Compiler.encode_values_append,List.append_assoc] using slots
    simpa only [ValuesAt,Compiler.encode_values_length,basePosition] using words.append_right.append_left
  have fits : ∀value∈args,ResultIndexFits value := by
    intro value member
    apply Store.owned_result_fits store
    exact (owned.2 _ (List.mem_cons_self ..)).2 value (by rw [split]; exact List.mem_append_left _ (List.mem_append_right _ member))
  apply DivSpec.mono (call_host_source_retained_world memory hooks floats allocator allocation interrupts view code
    Inv (fun c s h => (certify c s h).shape)
    {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} store platform valid
    address base f.toFrame frameWf function host signature functionAt hostCode signatureAt args argumentTypes'.symm
    argumentTyped (Itasca.Runtime.Spec.results_typed_wf argumentTyped) fits arguments machine.typed.typed.store callback retains)
  intro out result
  obtain ⟨afterCode,agrees,freshInv,retained,extension,retainedExterns,outcome,causes⟩ := result
  have same := Store.decode_store_code_agrees view agrees
  have newMachine : Execution view afterCode store exec
      ⟨Store.decodeStore view afterCode store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ expected raw.pc.val false := by
    simpa only [same] using machine.change_code agrees
  have newPoint : FramePoint (Store.decodeStore view afterCode store) raw
      {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after} compiled C targets next output := by
    simpa only [same] using point
  have newPending : SourceMachine.HostPending
      ⟨Store.decodeStore view afterCode store,ambient,{f with code:=after,vals:=front}::rest,[]⟩
      (signature.results.val.map sourceType) := by simpa only [same] using pending
  have newExtension : Extend_store (Store.decodeStore view afterCode store)
      (Store.decodeStore view afterCode out.2.2.1) := by simpa only [same] using extension
  have fresh := certify afterCode _ freshInv
  have sourceSite : HostSignatureSite ⟨Store.decodeStore view code store,ambient,
      {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ address.index.val host.val signature base.val := by
    refine ⟨Or.inr ?_,hostSource⟩
    obtain ⟨hostModule,sourceAt⟩ := hostSource
    refine ⟨f,rest,table,type,position,after,front,args,_,signature.params.val.map sourceType,signature.results.val.map sourceType,
      0,Spec.StepsHN.refl machine.typed.typed.decode_wf,split,bounded,selected,sourceAt,rfl,argumentTypes',?_⟩
    rw [basePosition,machine.stack.source_base last hf]
  refine ⟨afterCode,agrees,freshInv,fresh,retained,extension,retainedExterns,sourceSite,causes,?_⟩
  rcases outcome with early | observed
  · obtain ⟨error,status,cause,sameStore⟩ := early
    apply Or.inl
    refine ⟨error,status,cause,sameStore,?_⟩
    have kind := cause.error
    simp only [hostCallEvents,status]
    cases error <;> simp only [HostPreparationError] at kind ⊢ <;> try contradiction <;> try rfl
    rename_i limit
    cases limit <;> simp only [HostPreparationError] at kind ⊢ <;> try contradiction <;> rfl
  · apply Or.inr
    refine ⟨?_,?_,?_⟩
    · rcases observed.1.2.2.2.2 with success | failure
      · exact Or.inl success.1
      · exact Or.inr failure.1
    · have events := observed.1.indirect_frame_events view afterCode store ambient f rest after table type position address front args base _ out
        newMachine.typed.typed.store (Store.decode_store_wf view afterCode _ fresh.shape fresh.storeSyntax)
        machine.typed.typed.ambient frameWf labels frontWf sourceTail callers sourceHeights (by simpa only [same] using target) tableBound typeBound positionBound
        (Itasca.Runtime.Spec.results_typed_wf argumentTyped)
      simpa only [←split,same] using events
    · intro success
      have tail' : Compiler.StructuredCode (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
          compiled.code.val compiled.jump_tables.val targets (front.map Compiler.valueType++signature.results.val.map sourceType) after pc.val next output := by
        simpa only [signatureTypes.2] using tail
      obtain ⟨finalPC,resumed⟩ := host_structured_resume newMachine last hf binding slots program newPoint (by simpa only [List.append_assoc] using split)
        basePosition heights tail' newPending observed.1 success retained (frame_type_bounds_of_shape certified.shape) newExtension fresh (observed.2 success).1
      exact ⟨finalPC,resumed,(observed.2 success).2⟩
end Itasca.Runtime.Integration
