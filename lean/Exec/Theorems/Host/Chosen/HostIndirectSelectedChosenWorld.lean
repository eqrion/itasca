import Exec.Theorems.Host.HostIndirectSelected
import Exec.Theorems.Host.Chosen.HostCallChosenWorld
import Exec.Theorems.Host.Chosen.HostIndirectChosenContext
import Exec.Theorems.Host.Chosen.HostCallChosenErasure
import Exec.Theorems.Composition.ExecutionCode
import Exec.Theorems.Host.HostDispatchCauses
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
open Exec.Interp.StructuredMachine

theorem call_indirect_host_structured_chosen_world {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=Spec.firstVectorChoice) (occurrence : Nat) {M P F A : Type} {emission : FunctionEmission} {allowed : instr → Prop}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (certify : ∀ c s, Inv c s → CertifiedSupportedStore emission allowed view c s)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv code store)
    (entryTyped : Store_ok (Store.decodeStore view code store))
    (frameIndex : Usize) (raw : runtime.interp.Frame) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (table type position : Nat) (after : List instr)
    (front args : List val) (params results : List valtype) (pc : U32) (base : Usize)
    (address : runtime.FuncAddr) (function : runtime.store.Function) (host : U64) (signature : Itasca.types.FuncType)
    (functionAt : store.funcs.val[address.index.val]?=some function) (hostCode : function.code=.Host host)
    (signatureAt : store.types.val[function.signature.val]?=some signature)
    (signatureTypes : signature.params.val.map sourceType=params ∧ signature.results.val.map sourceType=results)
    (selected : Abs.Indirect.resolve (Store.decodeStore view code store) f table type position=some address.index.val)
    (last : frameIndex.val+1=exec.frames.length) (hf : exec.frames.val[frameIndex.val]?=some raw)
    (split : f.vals=(front++args)++[Abs.integerVal .I32 position]) (bounded : position<2^32)
    (argumentTypes : args.map Code.valueType=params)
    (basePosition : base.val=raw.base.val+Code.slots ((f.locals++front).map Code.valueType))
    (heights : ∀label∈f.labels,label.height≤front.length)
    (binding : FrameBinding store exec raw f) (slots : FrameSlots exec raw f)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint emission (Store.decodeStore view code store) raw
      {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after} compiled C targets next output)
    (tail : Code.StructuredCodeWithTables (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (front.map Code.valueType++results) after pc.val next output)
    (expected : List valtype)
    (machine : Execution emission (Abs.SupportedState allowed) view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ expected raw.pc.val false)
    (owned : Abs.Ownership.StateOwned (Store.ownershipBounds store)
      ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩)
    (callback : ∀ p args results,
      hooks.call_host p store host args results ⦃ answer => ∃ afterCode,
        Store.CodeAgreesOn store code afterCode ∧ Inv afterCode answer.2.2.1 ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode answer.2.2.1) ∧
        Store_ok (Store.decodeStore view afterCode answer.2.2.1) ∧
        choices.host (occurrence+1) (Store.decodeStore view code store) address.index.val host.val
          (signature.params.val.map sourceType) (signature.results.val.map sourceType) (args.val.map sourceValue)=
          checkedHostReply memory view afterCode answer.2.2.1 signature ⟨answer.2.2.2⟩ answer.1 ⦄)
    (preserve : ∀p args results answer,hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀p args results answer,hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issued : ∀p args results answer,hooks.call_host p store host args results=.ok answer →
      ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value) :
    runtime.interp.call memory hooks floats allocator {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} store platform address base ⦃ out =>
      ∃afterCode,Store.CodeAgreesOn store code afterCode ∧ Inv afterCode out.2.2.1 ∧ CertifiedSupportedStore emission allowed view afterCode out.2.2.1 ∧ FrameStorePrefix store out.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode out.2.2.1) ∧
      store.externs.length≤out.2.2.1.externs.length ∧
      HostSignatureSite ⟨Store.decodeStore view code store,ambient,
        {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ address.index.val host.val signature base.val ∧
      HostCallCauses allocator hooks {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} store platform signature base host out ∧
      ((∃error,out.1=.Err error ∧ HostPreparationCause allocator hooks
          {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} store platform signature base error ∧ out.2.2.1=store ∧ hostCallEvents address out=[]) ∨
       ((out.1=.Ok () ∨ out.1=.Err (.Trap .Host) ∨ out.1=.Err (.Exhausted .CallStack)) ∧
        (∃n,2≤n ∧ Spec.ChosenStepsN choices occurrence n
          (Abs.decode ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩)
          (hostCallEvents address out) (hostCallFrameResult view afterCode ambient f rest after front out)) ∧
        (out.1=.Ok () → ∃finalPC,Execution emission (Abs.SupportedState allowed) view afterCode out.2.2.1 out.2.1
          ⟨Store.decodeStore view afterCode out.2.2.1,ambient,{f with code:=after,vals:=front++out.2.1.host_results.val.map sourceValue}::rest,[]⟩ expected finalPC false ∧
          Abs.Ownership.ValuesOwned (Store.ownershipBounds out.2.2.1) (out.2.1.host_results.val.map sourceValue)))) ⦄ := by
  have certified := certify code store valid
  have argumentTypes' := argumentTypes.trans signatureTypes.1.symm
  have hostSource := Store.decode_host_function view code store address function host signature functionAt hostCode signatureAt
  have exactStep := structured_indirect_host_next (Store.decodeStore view code store) ambient f rest after table type position address.index.val host.val
    (signature.params.val.map sourceType) (signature.results.val.map sourceType) front args selected bounded hostSource argumentTypes'
  rw [←split] at exactStep
  obtain ⟨pending,identity,sourceParams,sourceFront,sourcePosition,sourceHost,argumentTyped,sourceSplit,resumeEq,
      target,tableBound,typeBound,positionBound,frameWf,labels,frontWf,sourceTail,callers,sourceHeights⟩ :=
    Abs.Indirect.host_preparation _ ambient f rest table type after address.index.val args _ _ machine.typed.typed exactStep
  have sameTypes : sourceParams=signature.params.val.map sourceType := by
    have tags := Abs.results_type_of_typed argumentTyped
    have equal : Abs.valueType=Code.valueType := (funext valueType_eq_abs).symm
    rw [equal,argumentTypes'] at tags
    exact tags.symm
  rw [sameTypes] at argumentTyped
  have frontEq : sourceFront=front := by
    have valsEq := congrArg (fun st : Abs.AState => (st.frames.head!).vals) resumeEq
    simpa using valsEq.symm
  subst sourceFront
  have positionEq : sourcePosition=position := by
    have valsEq := sourceSplit.symm.trans split
    have valueEq := List.append_cancel_left valsEq
    simpa only [List.cons.injEq,Abs.integerVal,val.CONST.injEq,num_.mk_num__0.injEq,uN.mk_uN.injEq,true_and,and_true] using valueEq
  subst sourcePosition
  have arguments : ValuesAt exec.slots.val base.val args := by
    have words : WordsAt exec.slots.val raw.base.val
        (Code.encodeValues (f.locals++front)++(Code.encodeValues args++Code.encodeValues [Abs.integerVal .I32 position])) := by
      simpa only [FrameSlots,ValuesAt,split,Code.encodeValues_append,List.append_assoc] using slots
    simpa only [ValuesAt,Code.encodeValues_length,basePosition] using words.append_right.append_left
  have fits : ∀value∈args,ResultIndexFits value := by
    intro value member
    apply Store.owned_result_fits store
    exact (owned.2 _ (List.mem_cons_self ..)).2 value (by rw [split]; exact List.mem_append_left _ (List.mem_append_right _ member))
  apply WP.spec_mono (call_host_chosen_retained_world (choices:=choices) (occurrence+1) memory hooks floats allocator allocation interrupts view code
    Inv (fun c s h => (certify c s h).shape)
    {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} store platform valid
    address base f.toFrame frameWf function host signature functionAt hostCode signatureAt args argumentTypes'.symm
    argumentTyped (Exec.Spec.resultsTyped_wf argumentTyped) fits arguments machine.typed.typed.store entryTyped callback preserve externs issued)
  intro out result
  obtain ⟨afterCode,agrees,freshInv,retained,extension,retainedExterns,outcome,causes⟩ := result
  have same := Store.decodeStore_code_agrees view agrees
  have newMachine : Execution emission (Abs.SupportedState allowed) view afterCode store exec
      ⟨Store.decodeStore view afterCode store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ expected raw.pc.val false := by
    simpa only [same] using machine.change_code agrees
  have newPoint : FramePoint emission (Store.decodeStore view afterCode store) raw
      {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after} compiled C targets next output := by
    simpa only [same] using point
  have newPending : Abs.HostPending
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
    · have events := observed.1.indirect_frame_events admissible vector occurrence view afterCode store ambient f rest after table type position address front args base _ out
        newMachine.typed.typed.store (Store.decodeStore_wf view afterCode _ fresh.shape fresh.storeSyntax)
        machine.typed.typed.ambient frameWf labels frontWf sourceTail callers sourceHeights (by simpa only [same] using target) tableBound typeBound positionBound
        (Exec.Spec.resultsTyped_wf argumentTyped)
      simpa only [←split,same] using events
    · intro success
      have tail' : Code.StructuredCodeWithTables (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
          compiled.code.val compiled.jump_tables.val targets (front.map Code.valueType++signature.results.val.map sourceType) after pc.val next output := by
        simpa only [signatureTypes.2] using tail
      obtain ⟨finalPC,resumed⟩ := host_structured_resume newMachine last hf binding slots program newPoint (by simpa only [List.append_assoc] using split)
        basePosition heights tail' newPending (observed.1.erases admissible) success retained (frame_type_bounds_of_shape certified.shape) newExtension fresh (observed.2 success).1
      exact ⟨finalPC,resumed,(observed.2 success).2⟩
end Exec.Theorems
