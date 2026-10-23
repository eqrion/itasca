import Exec.Spec.Choices.UniversalQuietPrefix
import Exec.Abs.Sim.NeutralDecode
import Exec.Abs.Sim.OpenContextCompletion
import Exec.Interp.Relations.StepRecording
import Exec.Theorems.Host.Open.Source.State.Continuation
import Exec.Interp.Host.OpenDirectFetch
import Exec.Interp.Host.OpenPreparation
import Exec.Theorems.Host.HostCallStructuredWorld
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall Exec.Interp.StructuredMachine

/-- Actual suspension is tied to an independently typed source request and
its saved evaluation context. Early native rejection emits no host entry. -/
def PreparedSourceHost {M P : Type} (emission : FunctionEmission) (allowed : instr → Prop)
    (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (exec : runtime.interp.Execution) (source : config) (expected : resulttype) : CallPhase M P → Prop
  | .done out => hostStepAddress exec store=none ∨ ∃error,out.1=.Err error ∧ HostPreparationError error ∧ out.2.2.1=store
  | .pending ready _ _ address base identity args _ => ready.host_args=args ∧ (∀value∈args.val,OwnedBy store.id value) ∧ ∃pending : Spec.OpenHost.Pending,
      pending.before=Store.decodeStore view code store ∧ pending.address=address.index.val ∧ pending.identity=identity.val ∧
      pending.arguments=args.val.map sourceValue ∧ StepsH source [] pending.initial ∧ Config_ok pending.initial expected ∧
      (∃resume : Abs.AState,∀fresh returned,pending.completed ⟨fresh,some returned⟩=Abs.decode (Abs.finishHost resume fresh returned)) ∧
      Spec.UniversalQuietPrefix source pending.initial ∧
      SourceContinuation emission allowed memory view code store ready address base pending
        (match expected with | .mk_list types=>types)

private theorem host_identity_equal {s : _root_.store} {address left right : Nat} {p q r t : List valtype}
    (first : HostFunction s address left p q) (second : HostFunction s address right r t) : left=right := by
  obtain ⟨firstModule,firstAt⟩ := first
  obtain ⟨secondModule,secondAt⟩ := second
  have equal := Option.some.inj (firstAt.symm.trans secondAt)
  have codes := congrArg funcinst.CODE equal
  exact funccode.HOST.inj codes

theorem prepare_direct_host_source {M P F A : Type} {emission : FunctionEmission} {allowed : instr → Prop}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
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
    (point : FramePoint emission (Store.decodeStore view code store) raw
      {f with code := .CALL (.mk_uN index.val)::after} compiled C targets next output)
    (machine : Execution emission (Abs.SupportedState allowed) view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .CALL (.mk_uN index.val)::after}::rest,[]⟩ expected raw.pc.val false)
    (owned : Abs.Ownership.StateOwned (Store.ownershipBounds store)
      ⟨Store.decodeStore view code store,ambient,{f with code := .CALL (.mk_uN index.val)::after}::rest,[]⟩)
    (configurationTyped : Config_ok
      (Abs.decode ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL (.mk_uN index.val)::after}::rest,[]⟩)
      (.mk_list expected)) :
    prepareStep memory hooks floats allocator exec store platform
      ⦃phase=>PreparedSourceHost emission allowed memory view code store exec
        (Abs.decode ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL (.mk_uN index.val)::after}::rest,[]⟩)
        (.mk_list expected) phase⦄ := by
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
    obtain ⟨sourcePending,beforeEq,addressEq,argsEq,resultsEq,sourcePrefix,pendingTyped,completion⟩ :=
      Abs.OpenContext.host_call_pending_completion _ ambient f rest after index.val address.index.val args _ _ machine.typed.typed sourceStep
        (.mk_list expected) configurationTyped
    have identityEq : sourcePending.identity=host.val := by
      apply host_identity_equal
      · simpa only [beforeEq,addressEq] using sourcePending.host
      · exact hostSource
    apply prepare_step_direct_call memory hooks floats allocator exec store platform frameIndex raw caller compiled
      index offset address base last hf hi hc fetched (program.fetched_bound _ fetched) addressAt baseOffset
    intro pc hpc
    apply WP.spec_mono (prepare_host_call_effects memory hooks floats allocator allocation interrupts
      {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} store platform address base function host signature
      functionAt hostCode signatureAtStore args argumentTypes'.symm (Spec.resultsTyped_wf argumentTyped) fits arguments)
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
      · apply source_continuation_of_prepared machine last hf binding slots program point split
          (by rw [baseOffset,argumentOffset]) heights
          (by simpa only [point.locals,hpc] using continuation)
          (by simpa only [resumeEq,signatureTypes.2] using pending) memory ready function signature host.val
          (signature.params.val.map sourceType) copied hostSource argumentTyped signatureTypes.2 frameWf
          functionAt signatureAtStore padding frames capacity copiedEq owned sourcePending
        intro fresh returned
        rw [completion,resumeEq]
        rfl
end Exec.Theorems.OpenReentrantControl
