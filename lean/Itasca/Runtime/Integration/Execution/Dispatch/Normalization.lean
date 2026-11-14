import Itasca.Runtime.Integration.Execution.Dispatch.Outcomes
import Itasca.Runtime.Interp.Machine.Control.BranchSource
import Itasca.Runtime.Interp.Machine.Frames.SourceBase
import Itasca.Runtime.Integration.Execution.Dispatch.IndirectBoundary
import Itasca.Runtime.Interp.Machine.Calls.IndirectOperands
import Itasca.Runtime.Interp.Machine.Calls.HostCallStack
import Itasca.Runtime.Interp.Machine.Simulation.CoreErasure
import Itasca.Runtime.Integration.Execution.Resources.InvocationErrors

/-!
Sections, each formerly its own module: BranchTable, IndirectExecution, Measure, Normalization.
-/

/-! ## BranchTable -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std Itasca.Runtime.Interp

theorem step_branch_table_supported
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (depths : List labelidx) (fallback : labelidx) (expected : List valtype)
    (last : index.val+1=exec.frames.length) (hf : exec.frames.val[index.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some inst)
    (hc : inst.module.functions.val[raw.function.val]?=some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (point : Machine.FramePoint (Store.decodeStore view code store) raw
      {f with code:=.BR_TABLE depths fallback::after} compiled C targets next output)
    (machine : Machine.Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code:=.BR_TABLE depths fallback::after}::rest,[]⟩ expected raw.pc.val false)
    (shaped : Store.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SupportedStepOutcome allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨Store.decodeStore view code store,ambient,{f with code:=.BR_TABLE depths fallback::after}::rest,[]⟩ out ⦄ := by
  rcases Machine.branch_table_point_head point.code with jump | operation
  · obtain ⟨target,forward,fetch,tail⟩ := jump
    have retained : Machine.FramePoint (Store.decodeStore view code store) {raw with pc:=target}
        {f with code:=.BR_TABLE depths fallback::after} compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels,tail⟩
    apply WP.spec_mono (Machine.step_forward_jump memory hooks floats allocator view code exec store platform index raw inst compiled
      ambient {f with code:=.BR_TABLE depths fallback::after} rest expected C targets next output target last hf hi hc forward fetch slots retained machine program)
    rintro out ⟨success,sameStore,samePlatform,effect,fresh,simulation⟩
    exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore success
      ⟨target.val,false,_,fresh,simulation,fun _ h => h,rfl,fun _ h => h⟩
  · obtain ⟨stack,selector,start,len,shape,table⟩ := operation
    have typed : SourceMachine.FrameTyped (Store.decodeStore view code store) {f with code:=.BR_TABLE depths fallback::after} [] := by
      cases machine.typed.typed.frames with | cons head _ => exact head
    obtain ⟨front,value,values,bound⟩ := SourceMachine.BrTable.operands typed
    have frontTypes : front.map Compiler.valueType = stack := by
      have equal : front.map Compiler.valueType ++ [.I32] = stack ++ [.I32] := by
        simpa only [values,List.map_append,List.map_cons,List.map_nil,SourceMachine.integerVal,Compiler.valueType,numtype_Inn,valtype_numtype] using shape
      exact List.append_cancel_right equal
    rw [←frontTypes] at table
    apply WP.spec_mono (Machine.step_br_table_execution memory hooks floats allocator view code exec store platform
      index raw inst compiled C targets next output ambient f rest after depths fallback front value selector start len expected
      last hf hi hc program slots point values bound table machine)
    rintro out ⟨success,sameStore,samePlatform,advance⟩
    exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore success advance
end Itasca.Runtime.Integration

end

/-! ## IndirectExecution -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp
theorem step_indirect_supported_execution
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    [Machine.IndirectProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (table type : U32) (after : List instr)
    (last : index.val+1=exec.frames.length) (hf : exec.frames.val[index.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some inst) (hc : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module=Store.decodeInstance store inst)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (point : Machine.FramePoint (Store.decodeStore view code store) raw {f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Machine.Execution view code store exec ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩ expected raw.pc.val false)
    (shaped : Store.Shape view store)
    (compiledFunctions : Machine.CompiledFunctions code store)
    (functionTyping : CoreFunctionsTyped view code store) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩
    SourceIndirectHostBoundary store initial ∨ runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1=store ∧
      (out.1=.Ok () → Machine.Advance view code store out.2.1 expected compiled.code.length raw.pc.val false initial) ∧
      (∀ error,out.1=.Err error →
        ((∃ trap,error=.Trap trap ∧ IndirectTrap trap) ∧ ∃ count,0<count ∧ Spec.StepsHN count (SourceMachine.decode initial) [] ⟨⟨initial.store,ambient⟩,[.TRAP]⟩) ∨
        SourceIndirectCallCause allocator hooks code exec store platform index raw compiled initial error) ⦄ := by
  dsimp only
  have frameTyped : SourceMachine.FrameTyped (Store.decodeStore view code store) {f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after} [] := by
    cases machine.typed.typed.frames with | cons head _ => exact head
  rcases Machine.indirect_values_head table.val type.val after point frameTyped with skip | actual
  · obtain ⟨target,forward,fetch,tail⟩ := skip
    apply Or.inr
    apply WP.spec_mono (Machine.step_forward_jump memory hooks floats allocator view code exec store platform index raw inst compiled ambient
      {f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after} rest expected C targets next output target last hf hi hc forward fetch slots tail machine program)
    intro out effect
    refine ⟨effect.2.1,fun _ => ⟨target.val,false,_,effect.2.2.2.2.1,effect.2.2.2.2.2,fun _ h=>h,rfl,fun _ h=>h⟩,?_⟩
    intro error rejected
    rw [effect.1] at rejected
    cases rejected
  · obtain ⟨front,args,params,results,position,typeIndex,tableIndex,entry,selector,offset,bounds,typeEq,tableEq,values,bounded,arguments,argumentTypes,heights,caller,
      signature,tableType,pair,basePosition,indexPosition,fetch,tail⟩ := actual
    have typesSame : typeIndex=type := UScalar.eq_of_val_eq typeEq
    have tablesSame : tableIndex=table := UScalar.eq_of_val_eq tableEq
    subst typeIndex
    subst tableIndex
    have bindings : SourceMachine.ModuleBindings (Store.decodeStore view code store) (Store.decodeInstance store inst) C := by
      simpa only [moduleEq] using point.bindings
    obtain ⟨signatureIndex,rawSignature,tableAddress,object,signatureMapped,signatureFound,signatureEq,tableMapped,tableFound,funcref,typeLookup,tableLookup⟩ :=
      indirect_bindings_raw view code store inst f.toFrame C shaped (List.mem_of_getElem? hi) bindings moduleEq type table _ bounds signature tableType
    obtain ⟨positionWord,positionEq,selectorBound,input⟩ := indirect_call_slots slots values argumentTypes basePosition indexPosition bounded
    have baseFits : raw.base.val+offset.val<2^UScalarTy.Usize.numBits := by
      have capacity := exec.slots.property
      scalar_tac
    let base : Usize := UScalar.ofNatCore (raw.base.val+offset.val) baseFits
    have baseOffset : base.val=raw.base.val+offset.val := rfl
    have decodedPosition : SourceMachine.integer numtype.I32 (SourceMachine.integerVal .I32 position)=some position := SourceMachine.integer_accepts .I32 position bounded
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩
    have trapped (missing : SourceMachine.Indirect.resolve (Store.decodeStore view code store) f table.val type.val position=none) :
        ∃count,0<count ∧ Spec.StepsHN count (SourceMachine.decode initial) [] ⟨⟨initial.store,ambient⟩,[.TRAP]⟩ := by
      apply SourceMachine.Indirect.trap_simulation _ _ _ _ _ _ _ machine.typed
      simp only [SourceMachine.Indirect.step,values,SourceMachine.pop_append,decodedPosition,missing]
    classical
    by_cases host : SourceIndirectHostBoundary store initial
    · exact Or.inl host
    apply Or.inr
    refine (step_indirect_call_shaped memory hooks floats allocator view code exec store platform index raw entry selector offset
      inst compiled table type tableAddress object positionWord signatureIndex base rawSignature shaped funcref last hf fetch
      (program.fetched_bound _ fetch) hi hc pair tableMapped tableFound input selectorBound signatureMapped baseOffset signatureFound
      False _ ?_ ?_ ?_ ?_).spec
    · intro pc pcEq outside
      refine ⟨rfl,?_,?_⟩
      · intro impossible;cases impossible
      · intro error rejected
        cases rejected
        exact Or.inl ⟨⟨.TableOutOfBounds,rfl,Or.inl rfl⟩,trapped (indirect_resolve_outside view code store f table.val type.val position object tableLookup (by omega))⟩
    · intro pc pcEq null
      refine ⟨rfl,?_,?_⟩
      · intro impossible;cases impossible
      · intro error rejected
        cases rejected
        exact Or.inl ⟨⟨.UninitializedElement,rfl,Or.inr (Or.inl rfl)⟩,trapped (indirect_resolve_null view code store f table.val type.val position object tableLookup (by simpa only [positionEq] using null))⟩
    · intro pc pcEq reference address function selected nonzero word functionAt mismatch
      have resolved := indirect_resolve_reference view code store f table.val type.val position object reference address function tableLookup funcref
        (by simpa only [positionEq] using selected) word functionAt
      have different : ¬fun_type ⟨Store.decodeStore view code store,f.toFrame⟩ (.mk_uN type.val)=(Store.decodeFunction code store function).TYPE := by
        rw [typeLookup,←signatureEq]
        exact fun same=>mismatch same.symm
      rw [if_neg different] at resolved
      refine ⟨rfl,?_,?_⟩
      · intro impossible;cases impossible
      · intro error rejected
        cases rejected
        exact Or.inl ⟨⟨.IndirectCallTypeMismatch,rfl,Or.inr (Or.inr rfl)⟩,trapped resolved⟩
    · intro pc pcEq reference address function selected nonzero word functionAt sameType
      have resolved := indirect_resolve_reference view code store f table.val type.val position object reference address function tableLookup funcref
        (by simpa only [positionEq] using selected) word functionAt
      have same : fun_type ⟨Store.decodeStore view code store,f.toFrame⟩ (.mk_uN type.val)=(Store.decodeFunction code store function).TYPE := by
        rw [typeLookup,←signatureEq];exact sameType.symm
      rw [if_pos same] at resolved
      cases defined : function.code with
      | Host id => exact (host ⟨f,rest,table.val,type.val,position,after,front++args,address,function,id,rfl,values,bounded,resolved,functionAt,defined⟩).elim
      | Wasm instanceIndex functionIndex =>
        apply DivSpec.of_spec
        apply WP.spec_mono (Machine.call_indirect_selected memory hooks floats allocator allocation interrupts view code exec store platform index raw compiled C targets next output
          ambient f rest table.val type.val position after front args params results pc base {store:=store.id,index:=address} function instanceIndex functionIndex
          compiledFunctions functionTyping functionAt defined resolved (sameType.trans signatureEq) last hf pcEq values bounded argumentTypes
          (by rw [baseOffset,basePosition]) heights slots program point (by simpa only [pcEq] using tail.current) expected machine)
        intro out effect
        refine ⟨effect.1,effect.2.1,?_⟩
        intro error rejected
        obtain ⟨calleeInst,callee,calleeInstAt,calleeAt,cause⟩ := effect.2.2 error rejected
        exact Or.inr ⟨entry,selector,offset,table,type,pc,address,base,function,instanceIndex,functionIndex,calleeInst,callee,
          fetch,pair,functionAt,defined,calleeInstAt,calleeAt,baseOffset,pcEq,cause,
          f,rest,after,front,args,position,params,results,0,Spec.StepsHN.refl machine.typed.typed.decode_wf,values,bounded,resolved,sameType.trans signatureEq,argumentTypes,basePosition,machine.stack.source_base last hf⟩
end Itasca.Runtime.Integration

end

/-! ## Measure -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std Itasca.Runtime.Interp
theorem Machine.Advance.widen {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation} {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {expected : List valtype} {small large pc : Nat} {pending : Bool} {before : SourceMachine.AState}
    (advance : Machine.Advance view code store exec expected small pc pending before) (bound : small ≤ large) :
    Machine.Advance view code store exec expected large pc pending before := by
  obtain ⟨nextPC,nextPending,after,invariant,simulation,ownership,ambient,bounded⟩ := advance
  exact ⟨nextPC,nextPending,after,invariant,simulation.widen bound,ownership,ambient,bounded⟩

theorem SupportedStepOutcome.widen {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {view : M → Slice U8} {code : Store.CodeInterpretation} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {expected : List valtype} {small large pc : Nat}
    {pending : Bool} {source : SourceMachine.AState} {out}
    (outcome : SupportedStepOutcome allocator hooks view code exec store platform expected small pc pending source out)
    (bound : small ≤ large) :
    SupportedStepOutcome allocator hooks view code exec store platform expected large pc pending source out := by
  obtain ⟨sameStore, transition⟩ := outcome
  refine ⟨sameStore, ?_⟩
  cases status : out.1 with
  | Ok u =>
    simp only [status] at transition ⊢
    exact Machine.Advance.widen transition bound
  | Err error => simpa only [status] using transition

end Itasca.Runtime.Integration

end

/-! ## Normalization -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std Itasca.Runtime.Interp
theorem Machine.Advance.prepend_normalization {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution} {expected : List valtype} {codeLength pc : Nat}
    {count : Nat} {before middle : SourceMachine.AFrame} {s : _root_.store} {ambient : frame} {rest : List SourceMachine.AFrame}
    (chain : ErasedSteps count before middle)
    (typed : SourceMachine.ATyped ⟨s,ambient,before::rest,[]⟩)
    (advance : Machine.Advance view code store exec expected codeLength pc false ⟨s,ambient,middle::rest,[]⟩) :
    Machine.Advance view code store exec expected codeLength pc false ⟨s,ambient,before::rest,[]⟩ := by
  obtain ⟨nextPC,nextPending,after,invariant,simulation,ownership,ambientEq,bounded⟩ := advance
  exact ⟨nextPC,nextPending,after,invariant,simulation.prepend_normalization chain s ambient rest typed,
    fun bound owned => ownership bound (chain.ownership.stateful owned),ambientEq,fun bound h => bounded bound (chain.code_bound h)⟩

theorem SupportedStepOutcome.prepend_normalization {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P} {expected : List valtype}
    {codeLength pc count : Nat} {before middle : SourceMachine.AFrame} {s : _root_.store} {ambient : frame} {rest : List SourceMachine.AFrame}
    {out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P}
    (chain : ErasedSteps count before middle)
    (typed : SourceMachine.ATyped ⟨s,ambient,before::rest,[]⟩)
    (outcome : SupportedStepOutcome allocator hooks view code exec store platform expected codeLength pc false ⟨s,ambient,middle::rest,[]⟩ out) :
    SupportedStepOutcome allocator hooks view code exec store platform expected codeLength pc false ⟨s,ambient,before::rest,[]⟩ out := by
  obtain ⟨mutation,transition⟩ := outcome
  refine ⟨mutation,?_⟩
  cases status : out.1 with
  | Ok unit =>
    simp only [status] at transition ⊢
    exact Machine.Advance.prepend_normalization chain typed transition
  | Err error =>
    simp only [status] at transition ⊢
    exact ⟨transition.1.prepend_normalization chain typed,transition.2⟩
end Itasca.Runtime.Integration

end
