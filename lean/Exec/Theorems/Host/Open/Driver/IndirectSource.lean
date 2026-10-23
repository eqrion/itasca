import Exec.Theorems.Host.Open.Driver.DirectSource
import Exec.Interp.Relations.StepRecordingLookup
import Exec.Theorems.Host.Open.Driver.IndirectFetch
import Exec.Interp.Host.OpenJump
import Exec.Theorems.Host.HostIndirectStructuredWorld
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall Exec.Interp.StructuredMachine
private theorem host_identity_equal {s : _root_.store} {address left right : Nat} {p q r t : List valtype}
    (first : HostFunction s address left p q) (second : HostFunction s address right r t) : left=right := by
  obtain ⟨firstModule,firstAt⟩ := first
  obtain ⟨secondModule,secondAt⟩ := second
  exact funccode.HOST.inj (congrArg funcinst.CODE (Option.some.inj (firstAt.symm.trans secondAt)))

theorem prepare_selected_indirect_host_source {M P F A : Type} {emission : FunctionEmission} {allowed : instr → Prop}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (table type position : Nat) (after : List instr)
    (front args : List val) (params results : List valtype) (pc : U32) (base : Usize)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (host : U64) (signature : Itasca.types.FuncType)
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
    (configurationTyped : Config_ok
      (Abs.decode ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩)
      (.mk_list expected)) :
    prepareCall memory hooks floats allocator {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} store platform address base
      ⦃phase=>PreparedSourceHost emission allowed memory view code store exec
        (Abs.decode ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩)
        (.mk_list expected) phase⦄ := by
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
  obtain ⟨sourcePending,beforeEq,addressEq,argsEq,resultsEq,sourcePrefix,pendingTyped,completion⟩ :=
    Abs.OpenContext.indirect_host_pending_completion _ ambient f rest table type after address.index.val args _ _ machine.typed.typed exactStep
      (.mk_list expected) configurationTyped
  have identityEq : sourcePending.identity=host.val := by
    apply host_identity_equal
    · simpa only [beforeEq,addressEq] using sourcePending.host
    · exact hostSource
  apply WP.spec_mono (prepare_host_call_effects memory hooks floats allocator allocation interrupts
    {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} store platform address base function host signature
    functionAt hostCode signatureAt args argumentTypes'.symm (Spec.resultsTyped_wf argumentTyped) fits arguments)
  intro phase post
  rcases post with rejected|prepared
  · obtain ⟨out,rfl,error,status,cause,unchanged⟩ := rejected
    exact Or.inr ⟨error,status,cause.error,unchanged⟩
  · obtain ⟨ready,nextPlatform,copied,defaults,rfl,padding,frames,capacity,copiedEq,defaultsEq,lengthBound,copiedOwned⟩ := prepared
    refine ⟨rfl,copiedOwned,sourcePending,beforeEq,addressEq,identityEq,argsEq.trans copiedEq.symm,
      .cons sourcePrefix (.refl (Spec.stepH_wf sourcePrefix).2),pendingTyped,⟨_,completion⟩,?_,?_⟩
    · intro choices admissible vector occurrence
      have first:=Abs.chosen_neutral_simulation admissible vector occurrence sourcePrefix (by simp only [List.map_cons,admininstr_instr,Spec.neutralActive])
      exact ⟨1,by simpa only [List.append_nil] using Spec.ChosenStepsN.cons first (.refl _ (first.wf admissible).2)⟩
    · apply source_continuation_of_prepared machine last hf binding slots program point
        (by simpa only [List.append_assoc] using split) basePosition heights tail
        (by simpa only [resumeEq,signatureTypes.2] using pending) memory ready function signature host.val
        (signature.params.val.map sourceType) copied hostSource argumentTyped signatureTypes.2 frameWf
        functionAt signatureAt padding frames capacity copiedEq owned sourcePending
      intro fresh returned
      rw [completion,resumeEq]
      rfl

theorem prepare_indirect_host_source {M P F A : Type} {emission : FunctionEmission} {allowed : instr → Prop}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (shaped : Store.Shape view store)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    [IndirectProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (table type : U32) (after : List instr)
    (position : Nat) (sourceOperands : List val) (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (host : U64)
    (positionSplit : f.vals=sourceOperands++[Abs.integerVal .I32 position])
    (selectedSource : Abs.Indirect.resolve (Store.decodeStore view code store) f table.val type.val position=some address.index.val)
    (functionAt : store.funcs.val[address.index.val]?=some function) (hostCode : function.code=.Host host)
    (owner : address.store=store.id)
    (last : frameIndex.val+1=exec.frames.length) (hf : exec.frames.val[frameIndex.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some inst) (hc : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module=Store.decodeInstance store inst)
    (binding : FrameBinding store exec raw f) (slots : FrameSlots exec raw f)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint emission (Store.decodeStore view code store) raw
      {f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution emission (Abs.SupportedState allowed) view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩ expected raw.pc.val false)
    (owned : Abs.Ownership.StateOwned (Store.ownershipBounds store)
      ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩)
    (configurationTyped : Config_ok
      (Abs.decode ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩)
      (.mk_list expected)) :
    prepareStep memory hooks floats allocator exec store platform
      ⦃phase=>PreparedSourceHost emission allowed memory view code store exec
        (Abs.decode ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩)
        (.mk_list expected) phase⦄ := by
  have frameTyped : Abs.FrameTyped (Store.decodeStore view code store)
      {f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after} [] := by
    cases machine.typed.typed.frames with | cons head _ => exact head
  rcases indirect_values_head table.val type.val after point frameTyped with skip | actual
  · obtain ⟨target,forward,fetch,tail⟩ := skip
    rw [prepare_jump_exact memory hooks floats allocator exec store platform frameIndex raw inst compiled target
      last hf hi hc (program.fetched_bound _ fetch) fetch]
    apply WP.spec.ret
    apply Or.inl
    rw [hostStepAddress_at exec store frameIndex raw inst compiled (.Jump target) last hf hi hc fetch]
    simp [hostInstructionAddress,Bind.bind,Option.bind]
  · obtain ⟨front,args,params,results,actualPosition,typeIndex,tableIndex,entry,selector,offset,bounds,typeEq,tableEq,values,bounded,arguments,argumentTypes,heights,caller,
      signature,tableType,pair,basePosition,indexPosition,fetch,tail⟩ := actual
    have typeSame : typeIndex=type := UScalar.eq_of_val_eq typeEq
    have tableSame : tableIndex=table := UScalar.eq_of_val_eq tableEq
    subst typeIndex
    subst tableIndex
    have positionSame : actualPosition=position := by
      have parts := congrArg Abs.pop (values.symm.trans positionSplit)
      simp only [Abs.pop_append,Option.some.injEq,Prod.mk.injEq] at parts
      simpa only [Abs.integerVal,val.CONST.injEq,num_.mk_num__0.injEq,uN.mk_uN.injEq,true_and] using parts.2
    subst actualPosition
    have bindings : Abs.ModuleBindings (Store.decodeStore view code store) (Store.decodeInstance store inst) C := by
      simpa only [moduleEq] using point.bindings
    obtain ⟨signatureIndex,rawSignature,tableAddress,object,signatureMapped,signatureFound,signatureEq,tableMapped,tableFound,funcref,typeLookup,tableLookup⟩ :=
      indirect_bindings_raw view code store inst f.toFrame C shaped (List.mem_of_getElem? hi) bindings moduleEq type table _ bounds signature tableType
    obtain ⟨positionWord,positionEq,selectorBound,input⟩ := indirect_call_slots slots values argumentTypes basePosition indexPosition bounded
    have baseFits : raw.base.val+offset.val<2^UScalarTy.Usize.numBits := by
      have capacity := exec.slots.property
      scalar_tac
    let base : Usize := UScalar.ofNatCore (raw.base.val+offset.val) baseFits
    have baseOffset : base.val=raw.base.val+offset.val := rfl
    apply prepare_step_indirect_shaped memory hooks floats allocator view code exec store platform frameIndex raw entry selector offset
      inst compiled table type tableAddress object positionWord signatureIndex base rawSignature shaped funcref last hf fetch
      (program.fetched_bound _ fetch) hi hc pair tableMapped tableFound input selectorBound signatureMapped baseOffset signatureFound
    · intro pc pcEq outside
      have missing := indirect_resolve_outside view code store f table.val type.val position object tableLookup (by omega)
      rw [selectedSource] at missing
      cases missing
    · intro pc pcEq null
      have missing := indirect_resolve_null view code store f table.val type.val position object tableLookup (by simpa only [positionEq] using null)
      rw [selectedSource] at missing
      cases missing
    · intro pc pcEq reference target fn selected nonzero word found mismatch
      have resolved := indirect_resolve_reference view code store f table.val type.val position object reference target fn tableLookup funcref
        (by simpa only [positionEq] using selected) word found
      have different : ¬fun_type ⟨Store.decodeStore view code store,f.toFrame⟩ (.mk_uN type.val)=(Store.decodeFunction code store fn).TYPE := by
        rw [typeLookup,←signatureEq]; exact fun same=>mismatch same.symm
      rw [if_neg different,selectedSource] at resolved
      cases resolved
    · intro pc pcEq reference target fn selected nonzero word found sameType
      have resolved := indirect_resolve_reference view code store f table.val type.val position object reference target fn tableLookup funcref
        (by simpa only [positionEq] using selected) word found
      have same : fun_type ⟨Store.decodeStore view code store,f.toFrame⟩ (.mk_uN type.val)=(Store.decodeFunction code store fn).TYPE := by
        rw [typeLookup,←signatureEq];exact sameType.symm
      rw [if_pos same,selectedSource] at resolved
      have targetEq : target=address.index := UScalar.eq_of_val_eq (Option.some.inj resolved).symm
      subst target
      have functionEq : fn=function := Option.some.inj (found.symm.trans functionAt)
      subst fn
      have addressEq : (⟨store.id,address.index⟩ : runtime.FuncAddr)=address := by
        cases address with | mk identity index => simp_all only
      rw [addressEq]
      have actualSignatureBound := (shaped.functions function (List.mem_of_getElem? functionAt)).1
      let actualSignature := store.types.val[function.signature.val]
      have actualSignatureAt : store.types.val[function.signature.val]?=some actualSignature := List.getElem?_eq_getElem actualSignatureBound
      have decodedSignature : (Store.decodeFunction code store function).TYPE=Store.decodeFuncType actualSignature := by
        rw [Store.decodeFunction_type code store function actualSignatureBound]
      have signatureTypes : actualSignature.params.val.map sourceType=params ∧ actualSignature.results.val.map sourceType=results := by
        have sameSignature := decodedSignature.symm.trans (sameType.trans signatureEq)
        simpa only [Store.decodeFuncType,functype.mk_functype.injEq,list.mk_list.injEq] using sameSignature
      have continuation : Code.StructuredCodeWithTables (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
          compiled.code.val compiled.jump_tables.val targets (front.map Code.valueType++results) after pc.val next output := by
        simpa only [pcEq] using tail.current
      exact prepare_selected_indirect_host_source memory hooks floats allocator allocation interrupts view code exec store platform
        frameIndex raw compiled C targets next output ambient f rest table.val type.val position after front args params results pc base
        address function host actualSignature functionAt hostCode actualSignatureAt signatureTypes selectedSource last hf values bounded argumentTypes
        (by rw [baseOffset,basePosition]) heights binding slots program point continuation expected machine owned configurationTyped
end Exec.Theorems.OpenReentrantControl
