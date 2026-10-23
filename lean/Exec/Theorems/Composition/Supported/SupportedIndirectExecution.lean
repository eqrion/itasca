import Exec.Interp.StructuredMachine.SourceBase
import Exec.Theorems.Composition.Cumulative.CumulativeIndirectExecution
import Exec.Theorems.Composition.Supported.SupportedExecutionOutcome
import Exec.Interp.StructuredMachine.IndirectOperands
import Exec.Interp.StructuredMachine.IndirectSelected
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
theorem step_indirect_supported_execution
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    [StructuredMachine.IndirectProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (table type : U32) (after : List instr)
    (last : index.val+1=exec.frames.length) (hf : exec.frames.val[index.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some inst) (hc : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module=Store.decodeInstance store inst)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (point : StructuredMachine.FramePoint (Store.decodeStore view code store) raw {f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after} compiled C targets next output)
    (expected : List valtype)
    (machine : StructuredMachine.Execution view code store exec ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩ expected raw.pc.val false)
    (shaped : Store.Shape view store)
    (compiledFunctions : StructuredMachine.CompiledFunctions code store)
    (functionTyping : CoreFunctionsTyped view code store) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩
    SourceIndirectHostBoundary store initial ∨ runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1=store ∧
      (out.1=.Ok () → StructuredMachine.Advance view code store out.2.1 expected compiled.code.length raw.pc.val false initial) ∧
      (∀ error,out.1=.Err error →
        ((∃ trap,error=.Trap trap ∧ IndirectTrap trap) ∧ ∃ count,0<count ∧ Spec.StepsHN count (Abs.decode initial) [] ⟨⟨initial.store,ambient⟩,[.TRAP]⟩) ∨
        SourceIndirectCallCause allocator hooks code exec store platform index raw compiled initial error) ⦄ := by
  dsimp only
  have frameTyped : Abs.FrameTyped (Store.decodeStore view code store) {f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after} [] := by
    cases machine.typed.typed.frames with | cons head _ => exact head
  rcases StructuredMachine.indirect_values_head table.val type.val after point frameTyped with skip | actual
  · obtain ⟨target,forward,fetch,tail⟩ := skip
    apply Or.inr
    apply WP.spec_mono (StructuredMachine.step_forward_jump memory hooks floats allocator view code exec store platform index raw inst compiled ambient
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
    have decodedPosition : Abs.integer numtype.I32 (Abs.integerVal .I32 position)=some position := Abs.integer_accepts .I32 position bounded
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩
    have trapped (missing : Abs.Indirect.resolve (Store.decodeStore view code store) f table.val type.val position=none) :
        ∃count,0<count ∧ Spec.StepsHN count (Abs.decode initial) [] ⟨⟨initial.store,ambient⟩,[.TRAP]⟩ := by
      apply Abs.Indirect.trap_simulation _ _ _ _ _ _ _ machine.typed
      simp only [Abs.Indirect.step,values,Abs.pop_append,decodedPosition,missing]
    classical
    by_cases host : SourceIndirectHostBoundary store initial
    · exact Or.inl host
    apply Or.inr
    apply step_indirect_call_shaped memory hooks floats allocator view code exec store platform index raw entry selector offset
      inst compiled table type tableAddress object positionWord signatureIndex base rawSignature shaped funcref last hf fetch
      (program.fetched_bound _ fetch) hi hc pair tableMapped tableFound input selectorBound signatureMapped baseOffset signatureFound
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
        apply WP.spec_mono (StructuredMachine.call_indirect_selected memory hooks floats allocator allocation interrupts view code exec store platform index raw compiled C targets next output
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
end Exec.Theorems
