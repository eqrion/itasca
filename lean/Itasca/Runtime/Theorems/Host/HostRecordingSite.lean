import Itasca.Runtime.Theorems.Composition.StructuredHostSite
import Itasca.Runtime.Theorems.Composition.Supported.SupportedIndirectExecution
import Itasca.Runtime.Interp.Relations.StepRecordingInversion
import Itasca.Runtime.Interp.StructuredMachine.RecordingHeads
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

theorem HostFrameSite.indirect_recording_boundary {M : Type}

    {view : M → Slice U8} {code : Store.CodeInterpretation} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {expected : List valtype} {ambient : frame} {f : Abs.AFrame} {rest : List Abs.AFrame}
    (table type : U32) (after : List instr)
    (site : HostFrameSite view code exec store expected ambient
      {f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after} rest)
    [StructuredMachine.IndirectProjection (emission site.compiled) site.compiled.indirect.val]
    (shaped : Store.Shape view store) (address : runtime.FuncAddr)
    (selected : hostStepAddress exec store=some address) :
    SourceIndirectHostBoundary store ⟨Store.decodeStore view code store,ambient,
      {f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩ := by
  have frameTyped : Abs.FrameTyped (Store.decodeStore view code store) {f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after} [] := by
    cases site.machine.typed.typed.frames with | cons head _ => exact head
  rcases StructuredMachine.indirect_values_head table.val type.val after site.point frameTyped with skip | actual
  · obtain ⟨target,forward,fetch,tail⟩ := skip
    rw [hostStepAddress_at _ _ _ _ _ _ _ site.last site.frameAt site.instanceAt site.compiledAt fetch] at selected
    simp [hostInstructionAddress,Bind.bind,Option.bind] at selected
  · obtain ⟨front,args,params,results,position,typeIndex,tableIndex,entry,selector,offset,bounds,typeEq,tableEq,values,bounded,arguments,argumentTypes,heights,caller,
      signature,tableType,pair,basePosition,indexPosition,fetch,tail⟩ := actual
    have typesSame : typeIndex=type := UScalar.eq_of_val_eq typeEq
    have tablesSame : tableIndex=table := UScalar.eq_of_val_eq tableEq
    subst typeIndex
    subst tableIndex
    have moduleEq : f.module=Store.decodeInstance store site.inst := site.moduleEq
    have bindings : Abs.ModuleBindings (Store.decodeStore view code store) (Store.decodeInstance store site.inst) site.context := by
      simpa only [moduleEq] using site.point.bindings
    obtain ⟨signatureIndex,rawSignature,tableAddress,object,signatureMapped,signatureFound,signatureEq,tableMapped,tableFound,funcref,typeLookup,tableLookup⟩ :=
      indirect_bindings_raw view code store site.inst f.toFrame site.context shaped (List.mem_of_getElem? site.instanceAt) bindings moduleEq type table _ bounds signature tableType
    obtain ⟨positionWord,positionEq,selectorBound,input⟩ := indirect_call_slots site.slots values argumentTypes basePosition indexPosition bounded
    have wordAt : exec.slots.val[site.raw.base.val+selector.val]?=some exec.slots.val[site.raw.base.val+selector.val]! := by
      rw [getElem!_pos exec.slots.val (site.raw.base.val+selector.val) selectorBound]
      exact List.getElem?_eq_getElem selectorBound
    rw [hostStepAddress_at _ _ _ _ _ _ _ site.last site.frameAt site.instanceAt site.compiledAt fetch] at selected
    obtain ⟨reference,function,host,referenceAt,nonzero,word,addressStore,functionAt,sameSignature,hostCode⟩ :=
      hostInstructionAddress_indirect_inv exec store site.raw site.inst site.compiled entry selector offset table type tableAddress object exec.slots.val[site.raw.base.val+selector.val]! signatureIndex
        pair tableMapped tableFound wordAt signatureMapped address selected
    have castEq := shaped.table_function_reference_cast object (List.mem_of_getElem? tableFound) funcref _ reference referenceAt
    have fullWord : reference.val=address.index.val+1 := castEq.symm.trans word
    have resolved := indirect_resolve_reference view code store f table.val type.val position object reference address.index function tableLookup funcref
      (by simpa only [input,positionEq] using referenceAt) fullWord functionAt
    have decodedSignature := (shaped.function_signature_eq_iff code function (List.mem_of_getElem? functionAt) signatureIndex rawSignature signatureFound).mp sameSignature
    have same : fun_type ⟨Store.decodeStore view code store,f.toFrame⟩ (.mk_uN type.val)=(Store.decodeFunction code store function).TYPE := by
      rw [typeLookup,←signatureEq]
      exact decodedSignature.symm
    rw [if_pos same] at resolved
    exact ⟨f,rest,table.val,type.val,position,after,front++args,address.index,function,host,rfl,values,bounded,resolved,functionAt,hostCode⟩
theorem HostFrameSite.direct_recording_instruction {M : Type}

    {view : M → Slice U8} {code : Store.CodeInterpretation} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {expected : List valtype} {ambient : frame} {f : Abs.AFrame} {rest : List Abs.AFrame}
    (index : U32) (after : List instr)
    (site : HostFrameSite view code exec store expected ambient
      {f with code:=.CALL (.mk_uN index.val)::after} rest)
    [StructuredMachine.OrdinaryHeads (emission site.compiled)]
    (address : runtime.FuncAddr) (selected : hostStepAddress exec store=some address) :
    DirectHostInstruction store site.raw site.inst site.compiled (.CALL (.mk_uN index.val)) := by
  rcases StructuredMachine.codeRel_call_inv index site.point.code.current with skip | actual
  · obtain ⟨target,forward,fetch,tail⟩ := skip
    rw [hostStepAddress_at _ _ _ _ _ _ _ site.last site.frameAt site.instanceAt site.compiledAt fetch] at selected
    simp [hostInstructionAddress,Bind.bind,Option.bind] at selected
  · obtain ⟨front,params,results,base,values,signature,offset,fetch,tail⟩ := actual
    rw [hostStepAddress_at _ _ _ _ _ _ _ site.last site.frameAt site.instanceAt site.compiledAt fetch] at selected
    obtain ⟨function,host,addressAt,functionAt,hostCode⟩ := hostInstructionAddress_direct_inv exec store site.raw site.inst site.compiled index base address selected
    exact ⟨index,base,address,function,host,rfl,fetch,addressAt,functionAt,hostCode⟩

theorem HostFrameSite.recording_ready {M : Type}

    [∀compiled,StructuredMachine.OrdinaryHeads (emission compiled)]
    [∀compiled,StructuredMachine.IndirectProjection (emission compiled) compiled.indirect.val]
    [∀compiled,StructuredMachine.RecordingHeads (emission compiled)]
    {view : M → Slice U8} {code : Store.CodeInterpretation} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {expected : List valtype} {ambient : frame} {f : Abs.AFrame} {rest : List Abs.AFrame}
    (op : instr) (after : List instr)
    (site : HostFrameSite view code exec store expected ambient {f with code:=op::after} rest)
    (ready : ReadyInstruction op) (shaped : Store.Shape view store)
    (address : runtime.FuncAddr) (selected : hostStepAddress exec store=some address) :
    StructuredHostSite view code exec store expected site.raw.pc.val false
      ⟨Store.decodeStore view code store,ambient,{f with code:=op::after}::rest,[]⟩ := by
  obtain ⟨instruction,fetch,selectedHead⟩ := hostStepAddress_instruction exec store site.index site.raw site.inst site.compiled
    site.last site.frameAt site.instanceAt site.compiledAt address selected
  have calls := hostInstructionAddress_callTag exec store site.raw site.inst site.compiled instruction address selectedHead
  rcases StructuredMachine.code_recording_source ready site.point.code.current fetch calls with direct | indirect
  · obtain ⟨index,rfl⟩ := direct
    exact .ready site (Or.inl (site.direct_recording_instruction index after address selected))
  · obtain ⟨table,type,rfl⟩ := indirect
    exact .ready site (Or.inr ⟨table,type,rfl,site.indirect_recording_boundary table type after shaped address selected⟩)
end Itasca.Runtime.Theorems
