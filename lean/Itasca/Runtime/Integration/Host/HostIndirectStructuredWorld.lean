import Itasca.Runtime.Contracts
import Itasca.Runtime.Integration.Host.HostCallContext
import Itasca.Runtime.Integration.Execution.World.State
import Itasca.Runtime.Interp.Relations.StackPreservation
import Itasca.Runtime.Integration.Host.HostIndirectSelected
import Itasca.Runtime.Integration.Execution.Ownership.ReferenceShape
import Itasca.Runtime.Integration.Execution.Ownership.Publication
import Itasca.Runtime.Interp.Machine.Calls.IndirectOperands
import Itasca.Runtime.Integration.Host.HostDispatchCauses
import Itasca.Runtime.Interp.Relations.ArgumentRejectionKind
import Itasca.Runtime.Integration.Execution.Dispatch.Normalization

/-!
Sections, each formerly its own module: HostCallRetainedWorld, HostCallStructuredWorld, HostIndirectSelectedWorld, HostIndirectStructuredWorld.
-/

/-! ## HostCallRetainedWorld -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

theorem call_host_source_retained_world {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (invariant : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (shape : ∀ c s, invariant c s → Store.Shape view s)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : invariant code store)
    (address : runtime.FuncAddr) (base : Usize) (ambient : frame) (wfAmbient : wf_frame ambient)
    (function : runtime.store.FuncInst) (identity : U64) (signature : Itasca.wasm_types.FuncType)
    (functionAt : store.funcs.val[address.index.val]? = some function)
    (host : function.code = .Host identity)
    (signatureAt : store.types.val[function.signature.val]? = some signature)
    (values : List val)
    (typed : signature.params.val.map sourceType = values.map Compiler.valueType)
    (arguments : ResultsTyped (Store.decodeStore view code store) (signature.params.val.map sourceType) values)
    (wellFormed : ∀ value ∈ values, wf_val value)
    (fits : ∀ value ∈ values, ResultIndexFits value)
    (represented : ValuesAt exec.slots.val base.val values)
    (sourceWf : wf_store (Store.decodeStore view code store))
    (callback : ∀ p args results,
      hooks.call_host p store identity args results ⦃ (result, nextPlatform, after, returned) => ∃ afterCode,
        Store.CodeAgreesOn store code afterCode ∧ invariant afterCode after ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode after) ∧
        Store_ok (Store.decodeStore view afterCode after) ⦄div)
    (retains : HostRetention hooks store identity) :
    DivSpec (HostDiverges hooks store) (runtime.interp.call memory hooks floats allocator exec store platform address base) fun out =>
      ∃ afterCode, Store.CodeAgreesOn store code afterCode ∧ invariant afterCode out.2.2.1 ∧ FrameStorePrefix store out.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode out.2.2.1) ∧
      store.externs.length ≤ out.2.2.1.externs.length ∧
      ((∃ error, out.1 = .Err error ∧ HostPreparationCause allocator hooks exec store platform signature base error ∧ out.2.2.1 = store) ∨
       (HostCallSourceOutcome view afterCode store ambient address values base exec out ∧
        (out.1 = .Ok () → ResultsTyped (Store.decodeStore view afterCode out.2.2.1)
          (signature.results.val.map sourceType) (out.2.1.host_results.val.map sourceValue) ∧
          SourceMachine.Ownership.ValuesOwned (Store.ownershipBounds out.2.2.1) (out.2.1.host_results.val.map sourceValue)))) ∧
      HostCallCauses allocator hooks exec store platform signature base identity out := by
  apply DivSpec.mono (call_host_composition_causes memory hooks floats allocator allocation interrupts
    exec store platform address base function identity signature functionAt host signatureAt values
    typed wellFormed fits represented (HostDiverges hooks store)
    (fun out => ∃ afterCode, Store.CodeAgreesOn store code afterCode ∧ invariant afterCode out.2.2.1 ∧ FrameStorePrefix store out.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode out.2.2.1) ∧
      store.externs.length ≤ out.2.2.1.externs.length ∧
      (HostCallSourceOutcome view afterCode store ambient address values base exec out ∧
       (out.1 = .Ok () → ResultsTyped (Store.decodeStore view afterCode out.2.2.1)
         (signature.results.val.map sourceType) (out.2.1.host_results.val.map sourceValue) ∧
         SourceMachine.Ownership.ValuesOwned (Store.ownershipBounds out.2.2.1) (out.2.1.host_results.val.map sourceValue))) ∧
      HostCallCauses allocator hooks exec store platform signature base identity out) ?_)
  · intro out result
    rcases result with early | observed
    · obtain ⟨error,status,cause,unchanged⟩ := early
      exact ⟨code,(by intro index inst found fn; rfl),unchanged.symm ▸ valid,unchanged.symm ▸ FrameStorePrefix.refl store,
        by rw [unchanged]; exact Spec.extend_store_refl _ sourceWf,
        by rw [unchanged],Or.inl ⟨error,status,cause,unchanged⟩,HostCallCauses.of_preparation status cause⟩
    · obtain ⟨afterCode,agrees,fresh,retained,extension,external,observed,causes⟩ := observed
      exact ⟨afterCode,agrees,fresh,retained,extension,external,Or.inr observed,causes⟩
  · intro ready p args defaults preparation frames capacity argsEq defaultsEq
    rcases (DivSpec.of_dspec (callback p args.slice defaults.slice)
        (fun diverged => (⟨p,identity,args.slice,defaults.slice,diverged⟩ : HostDiverges hooks store))).imp_exists with
      ⟨⟨status,nextPlatform,nextStore,returned⟩,called,afterCode,agrees,fresh,crossExtension,sourceTyped⟩ |
      ⟨called,diverged⟩
    swap
    · rw [called,bind_div]
      exact .div _ diverged
    rw [called,bind_ok]
    have same := Store.decode_store_code_agrees view agrees
    have extension : Extend_store (Store.decodeStore view afterCode store)
        (Store.decodeStore view afterCode nextStore) := by simpa only [same] using crossExtension
    have hostSource := Store.decode_host_function view afterCode store address function identity signature functionAt host signatureAt
    have arguments : ResultsTyped (Store.decodeStore view afterCode store)
        (signature.params.val.map sourceType) values := by simpa only [same] using arguments
    obtain ⟨nextFunction,nextFound,nextSignature⟩ := Store.host_signature_extension view afterCode store nextStore
      address function signature functionAt signatureAt (shape afterCode nextStore fresh) extension
    have returnedIssued : ∀ value ∈ returned.val, Store.IssuedValue nextStore value := retains.issued _ _ _ _ _ _ _ called
    step with host_resume_source_owned memory view afterCode store nextStore ambient {ready with host_args := args}
      address base nextFunction signature identity.val (signature.params.val.map sourceType) values
      ⟨returned⟩ status hostSource arguments extension sourceTyped wfAmbient nextFound nextSignature returnedIssued capacity
      as ⟨result,finished,hostArgs,hostResults,frameEq,executionIdentity,effect⟩
    have causes : HostCallCauses allocator hooks exec store platform signature base identity
        (result,finished,nextStore,nextPlatform) := by
      rcases effect with success | failure
      · simp only [HostCallCauses,success.1]
      · rcases failure.1 with trapped | ⟨exhausted,reply⟩
        · simp only [HostCallCauses,trapped]
        · simp only [HostCallCauses,exhausted]
          exact ⟨p,args.slice,defaults.slice,returned,by simpa only [reply] using called⟩
    refine .ret ⟨afterCode,agrees,fresh,retains.framePrefix _ _ _ _ _ _ _ called,crossExtension,retains.externs _ _ _ _ _ _ _ called,?_,?_,causes⟩
    ·
      obtain ⟨padding,slotsEq,metadata⟩ := preparation
      have readyIdentity : ready.store = exec.store := by
        simpa only [] using congrArg runtime.interp.Execution.store metadata
      have oldLength : exec.slots.length ≤ ready.slots.length := by
        change exec.slots.val.length ≤ ready.slots.val.length
        rw [slotsEq,List.length_append]
        omega
      have oldSlots (j : Nat) (bound : j < exec.slots.length) : ready.slots.val[j]? = exec.slots.val[j]? := by
        rw [slotsEq,List.getElem?_append_left bound]
      refine ⟨?_,frameEq.trans frames,executionIdentity.trans readyIdentity,?_⟩
      · simpa only [hostArgs] using argsEq
      · rcases effect with success | failure
        · obtain ⟨statusEq,source,typedResults,ownedResults,valuesAt,length,preserved⟩ := success
          refine ⟨by simpa only [length] using oldLength,Or.inl ⟨statusEq,
            by simpa only [hostResults] using valuesAt,
            by simpa only [hostResults] using source,?_⟩⟩
          intro j bound outside
          have tags := SourceMachine.results_type_of_typed typedResults
          simp only [List.map_map,Function.comp_def] at tags
          simp only [hostResults,Function.comp_def,value_type_eq_abs] at outside
          rw [tags] at outside
          exact (preserved j outside).trans (oldSlots j bound)
        · obtain ⟨statusEq,same,source⟩ := failure
          refine ⟨by simpa only [same] using oldLength,Or.inr ⟨statusEq.imp_right And.left,source,?_⟩⟩
          intro j bound
          simpa only [same] using oldSlots j bound
    · intro success
      rcases effect with returned | failed
      · exact ⟨by simpa only [hostResults] using returned.2.2.1,by simpa only [hostResults] using returned.2.2.2.1⟩
      · rcases failed.1 with trapped | ⟨exhausted,_⟩
        · simp [trapped] at success
        · simp [exhausted] at success

end Itasca.Runtime.Integration

end

/-! ## HostCallStructuredWorld -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp
open Itasca.Runtime.Interp.Machine

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
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (index offset : U32) (after : List instr)
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
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint (Store.decodeStore view code store) raw
      {f with code := .CALL (.mk_uN index.val)::after} compiled C targets next output)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .CALL (.mk_uN index.val)::after}::rest,[]⟩ expected raw.pc.val false)
    (owned : SourceMachine.Ownership.StateOwned (Store.ownershipBounds store)
      ⟨Store.decodeStore view code store,ambient,{f with code := .CALL (.mk_uN index.val)::after}::rest,[]⟩)
    (callback : ∀ p args results,
      hooks.call_host p store host args results ⦃ (result, nextPlatform, after, returned) => ∃ afterCode,
        Store.CodeAgreesOn store code afterCode ∧ Inv afterCode after ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode after) ∧
        Store_ok (Store.decodeStore view afterCode after) ⦄div)
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
           (SourceMachine.decode ⟨Store.decodeStore view code store,ambient,{f with code := .CALL (.mk_uN index.val)::after}::rest,[]⟩)
           (hostCallEvents address out) (hostCallFrameResult view afterCode ambient f rest after front out)) ∧
          (out.1=.Ok () → ∃ finalPC, Execution view afterCode out.2.2.1 out.2.1
            ⟨Store.decodeStore view afterCode out.2.2.1,ambient,
              {f with code := after,vals := front++out.2.1.host_results.val.map sourceValue}::rest,[]⟩ expected finalPC false ∧
            SourceMachine.Ownership.ValuesOwned (Store.ownershipBounds out.2.2.1) (out.2.1.host_results.val.map sourceValue)))) := by
  have certified := certify code store valid
  have current := point.code.current
  rw [point.locals] at current
  rcases code_rel_call_values index f.locals f.vals current with skip | actual
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
    have argumentTypes' : args.map Compiler.valueType=signature.params.val.map sourceType := argumentTypes.trans signatureTypes.1.symm
    have resolve := binding.resolve_call caller hi index.val address addressAt
    have hostSource := Store.decode_host_function view code store address function host signature functionAt hostCode signatureAtStore
    have sourceStep := structured_host_next (Store.decodeStore view code store) ambient f rest after index.val address.index.val host.val
      (signature.params.val.map sourceType) (signature.results.val.map sourceType) front args resolve hostSource argumentTypes'
    rw [← split] at sourceStep
    obtain ⟨pending,identity,sourceParams,sourceHost,argumentTyped⟩ := SourceMachine.host_call_preparation _ ambient f rest after index.val
      address.index.val args _ _ machine.typed.typed sourceStep
    have sameTypes : sourceParams=signature.params.val.map sourceType := by
      have tags := SourceMachine.results_type_of_typed argumentTyped
      have equal : SourceMachine.valueType=Compiler.valueType := by funext v; exact (value_type_eq_abs v).symm
      rw [equal,argumentTypes'] at tags
      exact tags.symm
    rw [sameTypes] at argumentTyped
    obtain ⟨sourceFront,sourceSplit,resumeEq,_,indexBound,frameWf,labels,frontWf,tail,callers,heights⟩ :=
      SourceMachine.host_call_site _ ambient f rest after index.val address.index.val args _ _ machine.typed.typed sourceStep
    have fronts : sourceFront=front := by
      have parts := sourceSplit.symm.trans split
      exact List.append_cancel_right parts
    subst sourceFront
    have capacity := slots.capacity binding
    have baseFits : raw.base.val+offset.val≤Usize.max := by
      have prefixBound : Compiler.slots ((f.locals++front).map Compiler.valueType)≤Compiler.slots ((f.locals++f.vals).map Compiler.valueType) := by
        simp only [split,List.map_append,Compiler.slots_append]; omega
      scalar_tac
    have encodedBound : raw.base.val+offset.val<2^UScalarTy.Usize.numBits := by scalar_tac
    let base : Usize := UScalar.ofNatCore (raw.base.val+offset.val) encodedBound
    have baseOffset : base.val=raw.base.val+offset.val := UScalar.ofNatCore_val_eq encodedBound
    have arguments : ValuesAt exec.slots.val base.val args := by
      have words : WordsAt exec.slots.val raw.base.val (Compiler.encodeValues (f.locals++front)++Compiler.encodeValues args) := by
        simpa only [FrameSlots,ValuesAt,split,Compiler.encode_values_append,List.append_assoc] using slots
      simpa only [ValuesAt,Compiler.encode_values_length,baseOffset,argumentOffset] using words.append_right
    have fits : ∀ value∈args, ResultIndexFits value := by
      intro value member
      apply Store.owned_result_fits store
      exact (owned.2 _ (List.mem_cons_self ..)).2 value (by rw [split]; exact List.mem_append_right _ member)
    apply step_direct_call memory hooks floats allocator exec store platform frameIndex raw caller compiled
      index offset address base last hf hi hc fetched (program.fetched_bound _ fetched) addressAt baseOffset
      (HostDiverges hooks store) _
    intro pc hpc
    have tailCode : Compiler.StructuredCode (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
        compiled.code.val compiled.jump_tables.val targets (front.map Compiler.valueType++signature.results.val.map sourceType) after pc.val next output := by
      simpa only [hpc,signatureTypes.2,point.locals] using continuation
    rcases (call_host_source_retained_world memory hooks floats allocator allocation interrupts view code
      Inv (fun c s h => (certify c s h).shape)
      {exec with frames := exec.frames.set frameIndex {raw with pc := pc}} store platform valid
      address base f.toFrame frameWf function host signature functionAt hostCode signatureAtStore args argumentTypes'.symm
      argumentTyped (Itasca.Runtime.Spec.results_typed_wf argumentTyped) fits arguments machine.typed.typed.store callback
      retains).imp_exists with ⟨out,callActual,result⟩ | ⟨callActual,diverged⟩
    swap
    · rw [callActual]
      exact .div _ diverged
    rw [callActual,DivSpec.ok_iff]
    obtain ⟨afterCode,agrees,freshInv,retained,extension,retainedExterns,outcome,causes⟩ := result
    have same := Store.decode_store_code_agrees view agrees
    have newMachine : Execution view afterCode store exec
        ⟨Store.decodeStore view afterCode store,ambient,{f with code := .CALL (.mk_uN index.val)::after}::rest,[]⟩ expected raw.pc.val false := by
      simpa only [same] using machine.change_code agrees
    have newPoint : FramePoint (Store.decodeStore view afterCode store) raw
        {f with code := .CALL (.mk_uN index.val)::after} compiled C targets next output := by
      simpa only [same] using point
    have newPending : SourceMachine.HostPending
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
          newMachine.typed.typed.store (Store.decode_store_wf view afterCode _ fresh.shape fresh.storeSyntax)
          machine.typed.typed.ambient frameWf labels frontWf tail callers heights resolve indexBound
          (Itasca.Runtime.Spec.results_typed_wf argumentTyped)
        simpa only [← split,same] using events
      · intro success
        obtain ⟨finalPC,resumed⟩ := host_structured_resume newMachine last hf binding slots program newPoint split
          (by rw [baseOffset,argumentOffset]) heights tailCode newPending observed.1 success retained
          (frame_type_bounds_of_shape certified.shape) newExtension fresh (observed.2 success).1
        exact ⟨finalPC,resumed,(observed.2 success).2⟩
end Itasca.Runtime.Integration

end

/-! ## HostIndirectSelectedWorld -/

section

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
      hooks.call_host p store host args results ⦃ (result, nextPlatform, after, returned) => ∃ afterCode,
        Store.CodeAgreesOn store code afterCode ∧ Inv afterCode after ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode after) ∧
        Store_ok (Store.decodeStore view afterCode after) ⦄div)
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

end

/-! ## HostIndirectStructuredWorld -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp
open Itasca.Runtime.Interp.Machine
theorem step_indirect_host_structured_world {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (certify : ∀ c s, Inv c s → CertifiedSupportedStore view c s)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv code store)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    [IndirectProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (table type : U32) (after : List instr)
    (position : Nat) (sourceOperands : List val) (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (host : U64)
    (positionSplit : f.vals=sourceOperands++[SourceMachine.integerVal .I32 position])
    (selectedSource : SourceMachine.Indirect.resolve (Store.decodeStore view code store) f table.val type.val position=some address.index.val)
    (functionAt : store.funcs.val[address.index.val]?=some function) (hostCode : function.code=.Host host)
    (owner : address.store=store.id)
    (last : frameIndex.val+1=exec.frames.length) (hf : exec.frames.val[frameIndex.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some inst) (hc : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module=Store.decodeInstance store inst)
    (binding : FrameBinding store exec raw f) (slots : FrameSlots exec raw f)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint (Store.decodeStore view code store) raw
      {f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩ expected raw.pc.val false)
    (owned : SourceMachine.Ownership.StateOwned (Store.ownershipBounds store)
      ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩)
    (callback : ∀ p args results,
      hooks.call_host p store host args results ⦃ (result, nextPlatform, after, returned) => ∃ afterCode,
        Store.CodeAgreesOn store code afterCode ∧ Inv afterCode after ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode after) ∧
        Store_ok (Store.decodeStore view afterCode after) ⦄div)
    (retains : HostRetention hooks store host) :
    DivSpec (HostDiverges hooks store) (runtime.interp.step memory hooks floats allocator exec store platform) fun out =>
      (hostStepAddress exec store=none ∧ (∃ target, compiled.code.val[raw.pc.val]?=some (.Jump target)) ∧ out.1=.Ok () ∧ out.2.2.1=store ∧ out.2.2.2=platform ∧
       ∃ finalPC, Execution view code store out.2.1
         ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩ expected finalPC false ∧
       ConcreteSim compiled.code.length raw.pc.val finalPC false false
         ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩
         ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩) ∨
      (∃afterCode,Store.CodeAgreesOn store code afterCode ∧ Inv afterCode out.2.2.1 ∧
       hostStepAddress exec store=some address ∧ ∃ (signature : Itasca.wasm_types.FuncType) (base : Usize) (pc : U32) (front args : List val),
        f.vals=(front++args)++[SourceMachine.integerVal .I32 position] ∧ pc.val=raw.pc.val+1 ∧
        (∃ entry selector offset, compiled.code.val[raw.pc.val]?=some (.CallIndirect entry selector offset)) ∧
        runtime.interp.call memory hooks floats allocator
          {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} store platform address base = .ok out ∧
      CertifiedSupportedStore view afterCode out.2.2.1 ∧ FrameStorePrefix store out.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode out.2.2.1) ∧
      store.externs.length≤out.2.2.1.externs.length ∧
      HostSignatureSite ⟨Store.decodeStore view code store,ambient,
        {f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩ address.index.val host.val signature base.val ∧
      HostCallCauses allocator hooks {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} store platform signature base host out ∧
      ((∃error,out.1=.Err error ∧ HostPreparationCause allocator hooks
          {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} store platform signature base error ∧ out.2.2.1=store ∧ hostCallEvents address out=[]) ∨
       ((out.1=.Ok () ∨ out.1=.Err (.Trap .Host) ∨ out.1=.Err (.Exhausted .CallStack)) ∧
        (∃n,2≤n ∧ Spec.StepsHN n
          (SourceMachine.decode ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩)
          (hostCallEvents address out) (hostCallFrameResult view afterCode ambient f rest after front out)) ∧
        (out.1=.Ok () → ∃finalPC,Execution view afterCode out.2.2.1 out.2.1
          ⟨Store.decodeStore view afterCode out.2.2.1,ambient,{f with code:=after,vals:=front++out.2.1.host_results.val.map sourceValue}::rest,[]⟩ expected finalPC false ∧
          SourceMachine.Ownership.ValuesOwned (Store.ownershipBounds out.2.2.1) (out.2.1.host_results.val.map sourceValue))))) := by
  have certified := certify code store valid
  have frameTyped : SourceMachine.FrameTyped (Store.decodeStore view code store)
      {f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after} [] := by
    cases machine.typed.typed.frames with | cons head _ => exact head
  rcases indirect_values_head table.val type.val after point frameTyped with skip | actual
  · obtain ⟨target,forward,fetch,tail⟩ := skip
    apply DivSpec.mono (.of_spec _ _ _ _ (step_forward_jump memory hooks floats allocator view code exec store platform frameIndex raw inst compiled ambient
      {f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after} rest expected C targets next output target last hf hi hc forward fetch slots tail machine program))
    intro out effect
    refine Or.inl ⟨?_,⟨target,fetch⟩,effect.1,effect.2.1,effect.2.2.1,target.val,effect.2.2.2.2.1,effect.2.2.2.2.2⟩
    rw [host_step_address_at exec store frameIndex raw inst compiled (.Jump target) last hf hi hc fetch]
    rfl
  · obtain ⟨front,args,params,results,actualPosition,typeIndex,tableIndex,entry,selector,offset,bounds,typeEq,tableEq,values,bounded,arguments,argumentTypes,heights,caller,
      signature,tableType,pair,basePosition,indexPosition,fetch,tail⟩ := actual
    have typeSame : typeIndex=type := UScalar.eq_of_val_eq typeEq
    have tableSame : tableIndex=table := UScalar.eq_of_val_eq tableEq
    subst typeIndex
    subst tableIndex
    have positionSame : actualPosition=position := by
      have parts := congrArg SourceMachine.pop (values.symm.trans positionSplit)
      simp only [SourceMachine.pop_append,Option.some.injEq,Prod.mk.injEq] at parts
      simpa only [SourceMachine.integerVal,val.CONST.injEq,num_.mk_num__0.injEq,uN.mk_uN.injEq,true_and] using parts.2
    subst actualPosition
    have bindings : SourceMachine.ModuleBindings (Store.decodeStore view code store) (Store.decodeInstance store inst) C := by
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
      (HostDiverges hooks store) _
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
        rw [Store.decode_function_type code store function actualSignatureBound]
      have signatureTypes : actualSignature.params.val.map sourceType=params ∧ actualSignature.results.val.map sourceType=results := by
        have sameSignature := decodedSignature.symm.trans (sameType.trans signatureEq)
        simpa only [Store.decodeFuncType,functype.mk_functype.injEq,list.mk_list.injEq] using sameSignature
      have continuation : Compiler.StructuredCode (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
          compiled.code.val compiled.jump_tables.val targets (front.map Compiler.valueType++results) after pc.val next output := by
        simpa only [pcEq] using tail.current
      rcases (call_indirect_host_structured_world memory hooks floats allocator allocation interrupts view code Inv certify exec store platform valid
        frameIndex raw compiled C targets next output ambient f rest table.val type.val position after front args params results pc base
        address function host actualSignature functionAt hostCode actualSignatureAt signatureTypes selectedSource last hf values bounded argumentTypes
        (by rw [baseOffset,basePosition]) heights binding slots program point continuation expected machine owned callback
        retains).imp_exists with ⟨out,callActual,outcome⟩ | ⟨callActual,diverged⟩
      swap
      · rw [callActual]
        exact .div _ diverged
      rw [callActual,DivSpec.ok_iff]
      have guard : hostStepAddress exec store=some address := by
        rw [host_step_address_at exec store frameIndex raw inst compiled (.CallIndirect entry selector offset) last hf hi hc fetch]
        have castEq := certified.shape.table_function_reference_cast object (List.mem_of_getElem? tableFound) funcref positionWord.val reference selected
        have signatureSame := (certified.shape.function_signature_eq_iff code function (List.mem_of_getElem? functionAt)
          signatureIndex rawSignature signatureFound).mpr sameType
        have wordAt : exec.slots.val[raw.base.val+selector.val]?=some exec.slots.val[raw.base.val+selector.val]! := by
          rw [getElem!_pos exec.slots.val (raw.base.val+selector.val) selectorBound]
          exact List.getElem?_eq_getElem selectorBound
        rw [←addressEq]
        exact host_instruction_address_indirect exec store raw inst compiled entry selector offset table type tableAddress object
          (exec.slots.val[raw.base.val+selector.val]!) reference address.index function signatureIndex host
          pair tableMapped tableFound wordAt (by simpa only [input] using selected) nonzero
          (castEq.trans word) functionAt signatureMapped signatureSame hostCode
      obtain ⟨afterCode,agrees,freshInv,rest⟩ := outcome
      exact Or.inr ⟨afterCode,agrees,freshInv,guard,actualSignature,base,pc,front,args,values,pcEq,⟨entry,selector,offset,fetch⟩,callActual,rest⟩
end Itasca.Runtime.Integration

end
