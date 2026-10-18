import Exec.Theorems.Host.HostIndirectSelectedInvariant
import Exec.Interp.Relations.StepRecordingLookup
import Exec.Theorems.Composition.Supported.SupportedIndirectExecution
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
open Exec.Interp.StructuredMachine
theorem step_indirect_host_structured_recording {M P F A : Type} {emission : FunctionEmission} {allowed : instr → Prop}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (Inv : runtime.store.Store M → Prop)
    (certify : ∀ s, Inv s → CertifiedSupportedStore emission allowed view code s)
    (sound : Platform.HostSound hooks Inv (Store.decodeStore view code))
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv store)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    [IndirectProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (table type : U32) (after : List instr)
    (position : Nat) (sourceOperands : List val) (address : runtime.FuncAddr) (function : runtime.store.Function) (host : U64)
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
    (preserve : ∀p args results answer,hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀p args results answer,hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issued : ∀p args results answer,hooks.call_host p store host args results=.ok answer →
      ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      Inv out.2.2.1 ∧ (
      (hostStepAddress exec store=none ∧ (∃ target, compiled.code.val[raw.pc.val]?=some (.Jump target)) ∧ out.1=.Ok () ∧ out.2.2.1=store ∧ out.2.2.2=platform ∧
       ∃ finalPC, Execution emission (Abs.SupportedState allowed) view code store out.2.1
         ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩ expected finalPC false ∧
       ConcreteSim compiled.code.length raw.pc.val finalPC false false
         ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩
         ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩) ∨
      (hostStepAddress exec store=some address ∧ ∃ (signature : Itasca.types.FuncType) (base : Usize) (pc : U32) (front args : List val),
        f.vals=(front++args)++[Abs.integerVal .I32 position] ∧ pc.val=raw.pc.val+1 ∧
        (∃ entry selector offset, compiled.code.val[raw.pc.val]?=some (.CallIndirect entry selector offset)) ∧
        runtime.interp.call memory hooks floats allocator
          {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} store platform address base = .ok out ∧
      CertifiedSupportedStore emission allowed view code out.2.2.1 ∧ FrameStorePrefix store out.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
      store.externs.length≤out.2.2.1.externs.length ∧
      HostCallCauses allocator hooks {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} store platform signature base host out ∧
      ((∃error,out.1=.Err error ∧ HostPreparationCause allocator hooks
          {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} store platform signature base error ∧ out.2.2.1=store ∧ hostCallEvents address out=[]) ∨
       ((out.1=.Ok () ∨ out.1=.Err (.Trap .Host) ∨ out.1=.Err (.Exhausted .CallStack)) ∧
        (∃n,2≤n ∧ Spec.StepsHN n
          (Abs.decode ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩)
          (hostCallEvents address out) (hostCallFrameResult view code ambient f rest after front out)) ∧
        (out.1=.Ok () → ∃finalPC,Execution emission (Abs.SupportedState allowed) view code out.2.2.1 out.2.1
          ⟨Store.decodeStore view code out.2.2.1,ambient,{f with code:=after,vals:=front++out.2.1.host_results.val.map sourceValue}::rest,[]⟩ expected finalPC false ∧
          Abs.Ownership.ValuesOwned (Store.ownershipBounds out.2.2.1) (out.2.1.host_results.val.map sourceValue)))))) ⦄ := by
  have certified := certify store valid
  have frameTyped : Abs.FrameTyped (Store.decodeStore view code store)
      {f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after} [] := by
    cases machine.typed.typed.frames with | cons head _ => exact head
  rcases indirect_values_head table.val type.val after point frameTyped with skip | actual
  · obtain ⟨target,forward,fetch,tail⟩ := skip
    apply WP.spec_mono (step_forward_jump memory hooks floats allocator view code exec store platform frameIndex raw inst compiled ambient
      {f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after} rest expected C targets next output target last hf hi hc forward fetch slots tail machine program)
    intro out effect
    refine ⟨?_, Or.inl ⟨?_,⟨target,fetch⟩,effect.1,effect.2.1,effect.2.2.1,target.val,effect.2.2.2.2.1,effect.2.2.2.2.2⟩⟩
    · simpa only [effect.2.1] using valid
    · rw [hostStepAddress_at exec store frameIndex raw inst compiled (.Jump target) last hf hi hc fetch]
      rfl
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
      indirect_bindings_raw view code store inst f.toFrame C certified.shape (List.mem_of_getElem? hi) bindings moduleEq type table _ bounds signature tableType
    obtain ⟨positionWord,positionEq,selectorBound,input⟩ := indirect_call_slots slots values argumentTypes basePosition indexPosition bounded
    have baseFits : raw.base.val+offset.val<2^UScalarTy.Usize.numBits := by
      have capacity := exec.slots.property
      scalar_tac
    let base : Usize := UScalar.ofNatCore (raw.base.val+offset.val) baseFits
    have baseOffset : base.val=raw.base.val+offset.val := rfl
    apply step_indirect_call_shaped memory hooks floats allocator view code exec store platform frameIndex raw entry selector offset
      inst compiled table type tableAddress object positionWord signatureIndex base rawSignature certified.shape funcref last hf fetch
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
      have actualSignatureBound := (certified.shape.functions function (List.mem_of_getElem? functionAt)).1
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
      obtain ⟨out,callActual,outcome⟩ := WP.spec_imp_exists (call_indirect_host_structured_invariant memory hooks floats allocator allocation interrupts view code Inv certify sound exec store platform valid
        frameIndex raw compiled C targets next output ambient f rest table.val type.val position after front args params results pc base
        address function host actualSignature functionAt hostCode actualSignatureAt signatureTypes selectedSource last hf values bounded argumentTypes
        (by rw [baseOffset,basePosition]) heights binding slots program point continuation expected machine owned preserve externs issued)
      rw [callActual,WP.spec_ok]
      have guard : hostStepAddress exec store=some address := by
        rw [hostStepAddress_at exec store frameIndex raw inst compiled (.CallIndirect entry selector offset) last hf hi hc fetch]
        have castEq := certified.shape.table_function_reference_cast object (List.mem_of_getElem? tableFound) funcref positionWord.val reference selected
        have signatureSame := (certified.shape.function_signature_eq_iff code function (List.mem_of_getElem? functionAt)
          signatureIndex rawSignature signatureFound).mpr sameType
        have wordAt : exec.slots.val[raw.base.val+selector.val]?=some exec.slots.val[raw.base.val+selector.val]! := by
          rw [getElem!_pos exec.slots.val (raw.base.val+selector.val) selectorBound]
          exact List.getElem?_eq_getElem selectorBound
        rw [←addressEq]
        exact hostInstructionAddress_indirect exec store raw inst compiled entry selector offset table type tableAddress object
          (exec.slots.val[raw.base.val+selector.val]!) reference address.index function signatureIndex host
          pair tableMapped tableFound wordAt (by simpa only [input] using selected) nonzero
          (castEq.trans word) functionAt signatureMapped signatureSame hostCode
      exact ⟨outcome.1, Or.inr ⟨guard,actualSignature,base,pc,front,args,values,pcEq,⟨entry,selector,offset,fetch⟩,callActual,outcome.2⟩⟩
end Exec.Theorems
