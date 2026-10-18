import Exec.Theorems.Host.HostCallRetained
import Exec.Theorems.Host.HostStructuredResume
import Exec.Theorems.Host.HostIndirectContext
import Exec.Theorems.Composition.FrameStorePrefixStaged
import Exec.Theorems.Composition.Core.CoreOwnership
import Exec.Abs.Indirect.HostTyping
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
open Exec.Interp.StructuredMachine

theorem structured_indirect_host_next (s : _root_.store) (ambient : frame) (f : Abs.AFrame)
    (rest : List Abs.AFrame) (after : List instr) (table type position address identity : Nat)
    (params results : List valtype) (front args : List val)
    (resolved : Abs.Indirect.resolve s f table type position=some address)
    (bounded : position<2^32) (host : HostFunction s address identity params results)
    (argumentTypes : args.map Code.valueType=params) :
    Abs.Indirect.step ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after, vals:=(front++args)++[Abs.integerVal .I32 position]}::rest,[]⟩
      {f with vals:=(front++args)++[Abs.integerVal .I32 position]} rest table type after =
      .host address args results ⟨s,ambient,{f with code:=after,vals:=front}::rest,[]⟩ := by
  obtain ⟨moduleInst,lookup⟩ := host
  have types : args.map Abs.valueType=params := by
    simpa only [show Code.valueType=Abs.valueType from funext valueType_eq_abs] using argumentTypes
  have length : params.length=args.length := by rw [←argumentTypes,List.length_map]
  have decoded : Abs.integer numtype.I32 (Abs.integerVal .I32 position)=some position := Abs.integer_accepts .I32 position bounded
  have resolved' : Abs.Indirect.resolve s {f with vals:=(front++args)++[Abs.integerVal .I32 position]} table type position=some address := resolved
  simp only [Abs.Indirect.step,Abs.pop_append,decoded,resolved']
  simp [Abs.Indirect.invoke,lookup,length,types]

/-- The selected host branch of actual indirect dispatch resumes all saved
frames after consuming the selector as well as the argument suffix. -/
theorem call_indirect_host_structured {M P F A : Type} {emission : FunctionEmission} {allowed : instr → Prop}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (sound : Platform.HostSound hooks (CertifiedSupportedStore emission allowed view code) (Store.decodeStore view code))
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedSupportedStore emission allowed view code store)
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
    (preserve : ∀p args results answer,hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀p args results answer,hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issued : ∀p args results answer,hooks.call_host p store host args results=.ok answer →
      ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value) :
    runtime.interp.call memory hooks floats allocator {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} store platform address base ⦃ out =>
      CertifiedSupportedStore emission allowed view code out.2.2.1 ∧ FrameStorePrefix store out.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
      store.externs.length≤out.2.2.1.externs.length ∧
      HostCallCauses allocator hooks {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} store platform signature base host out ∧
      ((∃error,out.1=.Err error ∧ HostPreparationCause allocator hooks
          {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} store platform signature base error ∧ out.2.2.1=store ∧ hostCallEvents address out=[]) ∨
       ((out.1=.Ok () ∨ out.1=.Err (.Trap .Host) ∨ out.1=.Err (.Exhausted .CallStack)) ∧
        (∃n,2≤n ∧ Spec.StepsHN n
          (Abs.decode ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩)
          (hostCallEvents address out) (hostCallFrameResult view code ambient f rest after front out)) ∧
        (out.1=.Ok () → ∃finalPC,Execution emission (Abs.SupportedState allowed) view code out.2.2.1 out.2.1
          ⟨Store.decodeStore view code out.2.2.1,ambient,{f with code:=after,vals:=front++out.2.1.host_results.val.map sourceValue}::rest,[]⟩ expected finalPC false ∧
          Abs.Ownership.ValuesOwned (Store.ownershipBounds out.2.2.1) (out.2.1.host_results.val.map sourceValue)))) ⦄ := by
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
  apply WP.spec_mono (call_host_source_retained memory hooks floats allocator allocation interrupts view code
    (CertifiedSupportedStore emission allowed view code) (fun _ h=>h.shape) sound
    {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} store platform certified
    address base f.toFrame frameWf function host signature functionAt hostCode signatureAt args argumentTypes'.symm
    argumentTyped (Exec.Spec.resultsTyped_wf argumentTyped) fits arguments machine.typed.typed.store preserve externs issued)
  intro out result
  obtain ⟨fresh,retained,extension,retainedExterns,outcome,causes⟩ := result
  refine ⟨fresh,retained,extension,retainedExterns,causes,?_⟩
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
    · have events := observed.1.indirect_frame_events view code store ambient f rest after table type position address front args base _ out
        machine.typed.typed.store (Store.decodeStore_wf view code _ fresh.shape fresh.storeSyntax)
        machine.typed.typed.ambient frameWf labels frontWf sourceTail callers sourceHeights target tableBound typeBound positionBound
        (Exec.Spec.resultsTyped_wf argumentTyped)
      simpa only [←split] using events
    · intro success
      have tail' : Code.StructuredCodeWithTables (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
          compiled.code.val compiled.jump_tables.val targets (front.map Code.valueType++signature.results.val.map sourceType) after pc.val next output := by
        simpa only [signatureTypes.2] using tail
      obtain ⟨finalPC,resumed⟩ := host_structured_resume machine last hf binding slots program point (by simpa only [List.append_assoc] using split)
        basePosition heights tail' pending observed.1 success retained (frame_type_bounds_of_shape certified.shape) extension fresh (observed.2 success).1
      exact ⟨finalPC,resumed,(observed.2 success).2⟩
end Exec.Theorems
