import Itasca.Runtime.Theorems.Host.HostCallSource
import Itasca.Runtime.Interp.Relations.FrameStorePrefix
import Itasca.Runtime.Theorems.Host.HostResumeOwned
import Itasca.Runtime.Theorems.Host.HostStructuredResume
import Itasca.Runtime.Theorems.Host.HostCallContext
import Itasca.Runtime.Theorems.Composition.FrameStorePrefixStaged
import Itasca.Runtime.Theorems.Composition.Core.CoreOwnership
import Itasca.Runtime.Interp.StructuredMachine.StructuredCall
import Itasca.Runtime.Theorems.Host.HostCallRetainedWorld
import Itasca.Runtime.Theorems.Host.HostDispatchCauses
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp
open Itasca.Runtime.Interp.StructuredMachine

theorem step_host_call_structured_world_provenance {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (certify : ∀ c s, Inv c s → CertifiedSupportedStore view c s)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv code store)
    (frameIndex : Usize) (raw : runtime.interp.Frame)
    (caller : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (index offset : U32) (after : List instr)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (host : U64)
    (expected : List valtype)
    (last : frameIndex.val+1=exec.frames.length)
    (hf : exec.frames.val[frameIndex.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some caller)
    (hc : caller.module.functions.val[raw.function.val]?=some compiled)
    (fetched : compiled.code.val[raw.pc.val]?=some (.Call index offset))
    (addressAt : caller.funcs.val[index.val]?=some address)
    (functionAt : store.funcs.val[address.index.val]?=some function)
    (hostCode : function.code=.Host host)
    (binding : FrameBinding store exec raw f) (slots : FrameSlots exec raw f)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint (Store.decodeStore view code store) raw
      {f with code := .CALL (.mk_uN index.val)::after} compiled C targets next output)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .CALL (.mk_uN index.val)::after}::rest,[]⟩ expected raw.pc.val false)
    (owned : Abs.Ownership.StateOwned (Store.ownershipBounds store)
      ⟨Store.decodeStore view code store,ambient,{f with code := .CALL (.mk_uN index.val)::after}::rest,[]⟩)
    (callback : ∀ p args results,
      hooks.call_host p store host args results ⦃ answer => ∃ afterCode,
        Store.CodeAgreesOn store code afterCode ∧ Inv afterCode answer.2.2.1 ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode answer.2.2.1) ∧
        Store_ok (Store.decodeStore view afterCode answer.2.2.1) ⦄div)
    (retains : HostRetention hooks store host) :
    DivSpec (HostDiverges hooks store) (runtime.interp.step memory hooks floats allocator exec store platform) fun out =>
      ∃ afterCode, Store.CodeAgreesOn store code afterCode ∧ Inv afterCode out.2.2.1 ∧ CertifiedSupportedStore view afterCode out.2.2.1 ∧ FrameStorePrefix store out.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode out.2.2.1) ∧
      store.externs.length≤out.2.2.1.externs.length ∧
      ∃ signature base pc front args,
        f.vals=front++args ∧ pc.val=raw.pc.val+1 ∧
        HostSignatureSite ⟨Store.decodeStore view code store,ambient,{f with code := .CALL (.mk_uN index.val)::after}::rest,[]⟩
          address.index.val host.val signature base.val ∧
        runtime.interp.call memory hooks floats allocator
          {exec with frames := exec.frames.set frameIndex {raw with pc := pc}} store platform address base = .ok out ∧
        HostCallCauses allocator hooks {exec with frames := exec.frames.set frameIndex {raw with pc := pc}}
          store platform signature base host out ∧
        ((∃ error, out.1=.Err error ∧
          HostPreparationCause allocator hooks {exec with frames := exec.frames.set frameIndex {raw with pc := pc}}
            store platform signature base error ∧ out.2.2.1=store ∧ hostCallEvents address out=[]) ∨
         ((out.1=.Ok () ∨ out.1=.Err (.Trap .Host) ∨ out.1=.Err (.Exhausted .CallStack)) ∧
          (∃ n, 2≤n ∧ Spec.StepsHN n
           (Abs.decode ⟨Store.decodeStore view code store,ambient,{f with code := .CALL (.mk_uN index.val)::after}::rest,[]⟩)
           (hostCallEvents address out) (hostCallFrameResult view afterCode ambient f rest after front out)) ∧
          (out.1=.Ok () → ∃ finalPC, Execution view afterCode out.2.2.1 out.2.1
            ⟨Store.decodeStore view afterCode out.2.2.1,ambient,
              {f with code := after,vals := front++out.2.1.host_results.val.map sourceValue}::rest,[]⟩ expected finalPC false ∧
            Abs.Ownership.ValuesOwned (Store.ownershipBounds out.2.2.1) (out.2.1.host_results.val.map sourceValue)))) := by
  have certified := certify code store valid
  have current := point.code.current
  rw [point.locals] at current
  rcases codeRel_call_values index f.locals f.vals current with skip | actual
  · obtain ⟨target,_,fetch,_⟩ := skip
    rw [fetched] at fetch
    cases fetch
  · obtain ⟨front,args,params,results,actualOffset,split,argumentTypes,signatureAt,argumentOffset,fetch,continuation⟩ := actual
    have sameOffset : actualOffset=offset := by simpa only [fetched,Option.some.injEq,runtime.bytecode.Instr.Call.injEq,true_and] using fetch.symm
    subst actualOffset
    obtain ⟨actualAddress,actualFunction,signature,resolveRaw,_,functionRaw,signatureAtStore,signatureEq⟩ :=
      program.resolve_call caller hi index.val ⟨.mk_list params,.mk_list results⟩ signatureAt
    have sameAddress : actualAddress=address := Option.some.inj (resolveRaw.symm.trans addressAt)
    subst actualAddress
    have sameFunction : actualFunction=function := Option.some.inj (functionRaw.symm.trans functionAt)
    subst actualFunction
    have signatureTypes : signature.params.val.map sourceType=params ∧ signature.results.val.map sourceType=results := by
      simpa only [Store.decodeFuncType,functype.mk_functype.injEq,list.mk_list.injEq] using signatureEq
    have argumentTypes' : args.map Code.valueType=signature.params.val.map sourceType := argumentTypes.trans signatureTypes.1.symm
    have resolve := binding.resolve_call caller hi index.val address addressAt
    have hostSource := Store.decode_host_function view code store address function host signature functionAt hostCode signatureAtStore
    have sourceStep := structured_host_next (Store.decodeStore view code store) ambient f rest after index.val address.index.val host.val
      (signature.params.val.map sourceType) (signature.results.val.map sourceType) front args resolve hostSource argumentTypes'
    rw [← split] at sourceStep
    obtain ⟨pending,identity,sourceParams,sourceHost,argumentTyped⟩ := Abs.host_call_preparation _ ambient f rest after index.val
      address.index.val args _ _ machine.typed.typed sourceStep
    have sameTypes : sourceParams=signature.params.val.map sourceType := by
      have tags := Abs.results_type_of_typed argumentTyped
      have equal : Abs.valueType=Code.valueType := by funext v; exact (valueType_eq_abs v).symm
      rw [equal,argumentTypes'] at tags
      exact tags.symm
    rw [sameTypes] at argumentTyped
    obtain ⟨sourceFront,sourceSplit,resumeEq,_,indexBound,frameWf,labels,frontWf,tail,callers,heights⟩ :=
      Abs.host_call_site _ ambient f rest after index.val address.index.val args _ _ machine.typed.typed sourceStep
    have fronts : sourceFront=front := by
      have parts := sourceSplit.symm.trans split
      exact List.append_cancel_right parts
    subst sourceFront
    have capacity := slots.capacity binding
    have baseFits : raw.base.val+offset.val≤Usize.max := by
      have prefixBound : Code.slots ((f.locals++front).map Code.valueType)≤Code.slots ((f.locals++f.vals).map Code.valueType) := by
        simp only [split,List.map_append,Code.slots_append]; omega
      scalar_tac
    have encodedBound : raw.base.val+offset.val<2^UScalarTy.Usize.numBits := by scalar_tac
    let base : Usize := UScalar.ofNatCore (raw.base.val+offset.val) encodedBound
    have baseOffset : base.val=raw.base.val+offset.val := UScalar.ofNatCore_val_eq encodedBound
    have arguments : ValuesAt exec.slots.val base.val args := by
      have words : WordsAt exec.slots.val raw.base.val (Code.encodeValues (f.locals++front)++Code.encodeValues args) := by
        simpa only [FrameSlots,ValuesAt,split,Code.encodeValues_append,List.append_assoc] using slots
      simpa only [ValuesAt,Code.encodeValues_length,baseOffset,argumentOffset] using words.append_right
    have fits : ∀ value∈args, ResultIndexFits value := by
      intro value member
      apply Store.owned_result_fits store
      exact (owned.2 _ (List.mem_cons_self ..)).2 value (by rw [split]; exact List.mem_append_right _ member)
    apply step_direct_call memory hooks floats allocator exec store platform frameIndex raw caller compiled
      index offset address base last hf hi hc fetched (program.fetched_bound _ fetched) addressAt baseOffset
      (HostDiverges hooks store) _
    intro pc hpc
    have tailCode : Code.StructuredCode (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
        compiled.code.val compiled.jump_tables.val targets (front.map Code.valueType++signature.results.val.map sourceType) after pc.val next output := by
      simpa only [hpc,signatureTypes.2,point.locals] using continuation
    rcases (call_host_source_retained_world memory hooks floats allocator allocation interrupts view code
      Inv (fun c s h => (certify c s h).shape)
      {exec with frames := exec.frames.set frameIndex {raw with pc := pc}} store platform valid
      address base f.toFrame frameWf function host signature functionAt hostCode signatureAtStore args argumentTypes'.symm
      argumentTyped (Itasca.Runtime.Spec.resultsTyped_wf argumentTyped) fits arguments machine.typed.typed.store callback
      retains).imp_exists with ⟨out,callActual,result⟩ | ⟨callActual,diverged⟩
    swap
    · rw [callActual]
      exact .div _ diverged
    rw [callActual,DivSpec.ok_iff]
    obtain ⟨afterCode,agrees,freshInv,retained,extension,retainedExterns,outcome,causes⟩ := result
    have same := Store.decodeStore_code_agrees view agrees
    have newMachine : Execution view afterCode store exec
        ⟨Store.decodeStore view afterCode store,ambient,{f with code := .CALL (.mk_uN index.val)::after}::rest,[]⟩ expected raw.pc.val false := by
      simpa only [same] using machine.change_code agrees
    have newPoint : FramePoint (Store.decodeStore view afterCode store) raw
        {f with code := .CALL (.mk_uN index.val)::after} compiled C targets next output := by
      simpa only [same] using point
    have newPending : Abs.HostPending
        ⟨Store.decodeStore view afterCode store,ambient,{f with code := after,vals := front}::rest,[]⟩
        (signature.results.val.map sourceType) := by simpa only [same] using pending
    have newExtension : Extend_store (Store.decodeStore view afterCode store)
        (Store.decodeStore view afterCode out.2.2.1) := by simpa only [same] using extension
    have fresh := certify afterCode _ freshInv
    have sourceSite : HostSignatureSite
        ⟨Store.decodeStore view code store,ambient,{f with code := .CALL (.mk_uN index.val)::after}::rest,[]⟩
        address.index.val host.val signature base.val := by
      refine ⟨Or.inl ?_,hostSource⟩
      obtain ⟨hostModule,sourceAt⟩ := hostSource
      refine ⟨f,rest,index.val,after,front,args,_,signature.params.val.map sourceType,signature.results.val.map sourceType,
        0,?_,resolve,sourceAt,rfl,argumentTypes',?_⟩
      · simpa only [←split] using Spec.StepsHN.refl machine.typed.typed.decode_wf
      · rw [baseOffset,argumentOffset,machine.stack.source_base last hf]
    refine ⟨afterCode,agrees,freshInv,fresh,retained,extension,retainedExterns,signature,base,pc,front,args,split,hpc,sourceSite,callActual,causes,?_⟩
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
      · have events := observed.1.frame_events view afterCode store ambient f rest after index.val address front args base _ out
          newMachine.typed.typed.store (Store.decodeStore_wf view afterCode _ fresh.shape fresh.storeSyntax)
          machine.typed.typed.ambient frameWf labels frontWf tail callers heights resolve indexBound
          (Itasca.Runtime.Spec.resultsTyped_wf argumentTyped)
        simpa only [← split,same] using events
      · intro success
        obtain ⟨finalPC,resumed⟩ := host_structured_resume newMachine last hf binding slots program newPoint split
          (by rw [baseOffset,argumentOffset]) heights tailCode newPending observed.1 success retained
          (frame_type_bounds_of_shape certified.shape) newExtension fresh (observed.2 success).1
        exact ⟨finalPC,resumed,(observed.2 success).2⟩
end Itasca.Runtime.Theorems
