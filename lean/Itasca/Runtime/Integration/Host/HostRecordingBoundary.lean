import Itasca.Runtime.Integration.Execution.Dispatch.Host
import Itasca.Runtime.Integration.Execution.Dispatch.Normalization
import Itasca.Runtime.Interp.Relations.ArgumentRejectionKind
import Itasca.Runtime.Interp.Machine.Coverage.RecordingHeads
import Itasca.Runtime.Interp.Machine.Frames.FrameDepth
import Itasca.Runtime.Interp.Machine.Normalization.NormalizeExecution

/-!
Sections, each formerly its own module: HostRecordingSite, HostRecordingBoundary.
-/

/-! ## HostRecordingSite -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

theorem HostFrameSite.indirect_recording_boundary {M : Type}

    {view : M → Slice U8} {code : Store.CodeInterpretation} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {expected : List valtype} {ambient : frame} {f : SourceMachine.AFrame} {rest : List SourceMachine.AFrame}
    (table type : U32) (after : List instr)
    (site : HostFrameSite view code exec store expected ambient
      {f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after} rest)
    [Machine.IndirectProjection (emission site.compiled) site.compiled.indirect.val]
    (shaped : Store.Shape view store) (address : runtime.FuncAddr)
    (selected : hostStepAddress exec store=some address) :
    SourceIndirectHostBoundary store ⟨Store.decodeStore view code store,ambient,
      {f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩ := by
  have frameTyped : SourceMachine.FrameTyped (Store.decodeStore view code store) {f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after} [] := by
    cases site.machine.typed.typed.frames with | cons head _ => exact head
  rcases Machine.indirect_values_head table.val type.val after site.point frameTyped with skip | actual
  · obtain ⟨target,forward,fetch,tail⟩ := skip
    rw [host_step_address_at _ _ _ _ _ _ _ site.last site.frameAt site.instanceAt site.compiledAt fetch] at selected
    simp [hostInstructionAddress,Bind.bind,Option.bind] at selected
  · obtain ⟨front,args,params,results,position,typeIndex,tableIndex,entry,selector,offset,bounds,typeEq,tableEq,values,bounded,arguments,argumentTypes,heights,caller,
      signature,tableType,pair,basePosition,indexPosition,fetch,tail⟩ := actual
    have typesSame : typeIndex=type := UScalar.eq_of_val_eq typeEq
    have tablesSame : tableIndex=table := UScalar.eq_of_val_eq tableEq
    subst typeIndex
    subst tableIndex
    have moduleEq : f.module=Store.decodeInstance store site.inst := site.moduleEq
    have bindings : SourceMachine.ModuleBindings (Store.decodeStore view code store) (Store.decodeInstance store site.inst) site.context := by
      simpa only [moduleEq] using site.point.bindings
    obtain ⟨signatureIndex,rawSignature,tableAddress,object,signatureMapped,signatureFound,signatureEq,tableMapped,tableFound,funcref,typeLookup,tableLookup⟩ :=
      indirect_bindings_raw view code store site.inst f.toFrame site.context shaped (List.mem_of_getElem? site.instanceAt) bindings moduleEq type table _ bounds signature tableType
    obtain ⟨positionWord,positionEq,selectorBound,input⟩ := indirect_call_slots site.slots values argumentTypes basePosition indexPosition bounded
    have wordAt : exec.slots.val[site.raw.base.val+selector.val]?=some exec.slots.val[site.raw.base.val+selector.val]! := by
      rw [getElem!_pos exec.slots.val (site.raw.base.val+selector.val) selectorBound]
      exact List.getElem?_eq_getElem selectorBound
    rw [host_step_address_at _ _ _ _ _ _ _ site.last site.frameAt site.instanceAt site.compiledAt fetch] at selected
    obtain ⟨reference,function,host,referenceAt,nonzero,word,addressStore,functionAt,sameSignature,hostCode⟩ :=
      host_instruction_address_indirect_inv exec store site.raw site.inst site.compiled entry selector offset table type tableAddress object exec.slots.val[site.raw.base.val+selector.val]! signatureIndex
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
    {store : runtime.store.Store M} {expected : List valtype} {ambient : frame} {f : SourceMachine.AFrame} {rest : List SourceMachine.AFrame}
    (index : U32) (after : List instr)
    (site : HostFrameSite view code exec store expected ambient
      {f with code:=.CALL (.mk_uN index.val)::after} rest)
    [Machine.OrdinaryHeads (emission site.compiled)]
    (address : runtime.FuncAddr) (selected : hostStepAddress exec store=some address) :
    DirectHostInstruction store site.raw site.inst site.compiled (.CALL (.mk_uN index.val)) := by
  rcases Machine.code_rel_call_inv index site.point.code.current with skip | actual
  · obtain ⟨target,forward,fetch,tail⟩ := skip
    rw [host_step_address_at _ _ _ _ _ _ _ site.last site.frameAt site.instanceAt site.compiledAt fetch] at selected
    simp [hostInstructionAddress,Bind.bind,Option.bind] at selected
  · obtain ⟨front,params,results,base,values,signature,offset,fetch,tail⟩ := actual
    rw [host_step_address_at _ _ _ _ _ _ _ site.last site.frameAt site.instanceAt site.compiledAt fetch] at selected
    obtain ⟨function,host,addressAt,functionAt,hostCode⟩ := host_instruction_address_direct_inv exec store site.raw site.inst site.compiled index base address selected
    exact ⟨index,base,address,function,host,rfl,fetch,addressAt,functionAt,hostCode⟩

theorem HostFrameSite.recording_ready {M : Type}

    [∀compiled,Machine.OrdinaryHeads (emission compiled)]
    [∀compiled,Machine.IndirectProjection (emission compiled) compiled.indirect.val]
    [∀compiled,Machine.RecordingHeads (emission compiled)]
    {view : M → Slice U8} {code : Store.CodeInterpretation} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {expected : List valtype} {ambient : frame} {f : SourceMachine.AFrame} {rest : List SourceMachine.AFrame}
    (op : instr) (after : List instr)
    (site : HostFrameSite view code exec store expected ambient {f with code:=op::after} rest)
    (ready : ReadyInstruction op) (shaped : Store.Shape view store)
    (address : runtime.FuncAddr) (selected : hostStepAddress exec store=some address) :
    StructuredHostSite view code exec store expected site.raw.pc.val false
      ⟨Store.decodeStore view code store,ambient,{f with code:=op::after}::rest,[]⟩ := by
  obtain ⟨instruction,fetch,selectedHead⟩ := host_step_address_instruction exec store site.index site.raw site.inst site.compiled
    site.last site.frameAt site.instanceAt site.compiledAt address selected
  have calls := host_instruction_address_call_tag exec store site.raw site.inst site.compiled instruction address selectedHead
  rcases Machine.code_recording_source ready site.point.code.current fetch calls with direct | indirect
  · obtain ⟨index,rfl⟩ := direct
    exact .ready site (Or.inl (site.direct_recording_instruction index after address selected))
  · obtain ⟨table,type,rfl⟩ := indirect
    exact .ready site (Or.inr ⟨table,type,rfl,site.indirect_recording_boundary table type after shaped address selected⟩)
end Itasca.Runtime.Integration

end

/-! ## HostRecordingBoundary -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

theorem HostFrameSite.recording_normal {M : Type}

    [∀compiled,Machine.OrdinaryHeads (emission compiled)]
    [∀compiled,Machine.IndirectProjection (emission compiled) compiled.indirect.val]
    [∀compiled,Machine.RecordingHeads (emission compiled)]
    {view : M → Slice U8} {code : Store.CodeInterpretation} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {expected : List valtype} {ambient : frame} {f : SourceMachine.AFrame} {rest : List SourceMachine.AFrame}
    (site : HostFrameSite view code exec store expected ambient f rest)
    (ready : ReadySource f) (shaped : Store.Shape view store)
    (address : runtime.FuncAddr) (selected : hostStepAddress exec store=some address) :
    StructuredHostSite view code exec store expected site.raw.pc.val false
      ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ := by
  cases source : f.code with
  | nil =>
    have labels : f.labels=[] := by simpa only [ReadySource,source] using ready
    have same : {f with code:=[],labels:=[]}=f := by rw [←source,←labels]
    rcases Machine.function_end site.program (by simpa only [same] using site.point) with jump | returned
    · obtain ⟨target,forward,fetch,tail⟩ := jump
      rw [host_step_address_at _ _ _ _ _ _ _ site.last site.frameAt site.instanceAt site.compiledAt fetch] at selected
      simp [hostInstructionAddress,Bind.bind,Option.bind] at selected
    · obtain ⟨count,fetch,locals,width,bound⟩ := returned
      rw [host_step_address_at _ _ _ _ _ _ _ site.last site.frameAt site.instanceAt site.compiledAt fetch] at selected
      simp [hostInstructionAddress,Bind.bind,Option.bind] at selected
  | cons op after =>
    have same : {f with code:=op::after}=f := by rw [←source]
    have readyOp : ReadyInstruction op := by cases op <;> simp_all only [ReadyInstruction,ReadySource,source]
    let current : HostFrameSite view code exec store expected ambient {f with code:=op::after} rest :=
      ⟨site.index,site.raw,site.inst,site.compiled,site.context,site.targets,site.next,site.output,
        site.last,site.frameAt,site.instanceAt,site.compiledAt,site.program,site.slots,site.moduleEq,
        by simpa only [same] using site.point,by simpa only [same] using site.machine,by simpa only [same] using site.owned⟩
    have result := current.recording_ready op after readyOp shaped address selected
    simpa only [same] using result

theorem recording_frame_host_site {M : Type}
    [∀compiled,Machine.OrdinaryHeads (emission compiled)]
    [∀compiled,Machine.ErasedHeads (emission compiled)]
    [∀compiled,Machine.IndirectProjection (emission compiled) compiled.indirect.val]
    [∀compiled,Machine.RecordingHeads (emission compiled)]
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (last : index.val+1 = exec.frames.length) (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f) (moduleEq : f.module=Store.decodeInstance store inst)
    (pending : Bool)
    (point : Machine.ControlPoint (Store.decodeStore view code store) raw f compiled C targets next output pending)
    (expected : List valtype)
    (machine : Machine.Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ expected raw.pc.val pending)
    (shaped : Store.Shape view store)
    (owned : SourceMachine.Ownership.StateOwned (Store.ownershipBounds store) ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩)
    (address : runtime.FuncAddr) (selected : hostStepAddress exec store=some address) :
    StructuredHostSite view code exec store expected raw.pc.val pending
      ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ := by
  cases point with
  | jump target fetched continuation =>
    rw [host_step_address_at _ _ _ _ _ _ _ last hf hi hc fetched] at selected
    simp [hostInstructionAddress,Bind.bind,Option.bind] at selected
  | ready point =>
    obtain ⟨count,g,labels,stop,types,chain,bound,represented,continuation,retained,metadata,done⟩ :=
      Machine.normalize_execution view code store exec raw index compiled C targets next output ambient f rest
        last hf program slots point expected machine
    have nextProgram : FrameProgram store raw compiled (g.locals.map Compiler.valueType) g.resultTypes C.FUNCS := program.reposition raw.pc metadata
    rcases done with skip | ready
    · obtain ⟨target,forward,fetched,tail⟩ := skip
      rw [host_step_address_at _ _ _ _ _ _ _ last hf hi hc fetched] at selected
      simp [hostInstructionAddress,Bind.bind,Option.bind] at selected
    · have nextModule : g.module=Store.decodeInstance store inst := metadata.module.trans moduleEq
      have nextOwned : SourceMachine.Ownership.StateOwned (Store.ownershipBounds store) ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
        refine ⟨owned.1,?_⟩
        intro item member
        rcases List.mem_cons.mp member with rfl | member
        · exact chain.ownership _ (owned.2 f (by simp))
        · exact owned.2 item (List.mem_cons_of_mem f member)
      let site : HostFrameSite view code exec store expected ambient g rest :=
        ⟨index,raw,inst,compiled,C,labels,stop,types,last,hf,hi,hc,nextProgram,represented,nextModule,continuation,retained,nextOwned⟩
      exact .normalize chain (site.recording_normal ready shaped address selected)

theorem recording_host_site {M : Type}
    [∀compiled,Machine.OrdinaryHeads (emission compiled)]
    [∀compiled,Machine.ErasedHeads (emission compiled)]
    [∀compiled,Machine.IndirectProjection (emission compiled) compiled.indirect.val]
    [∀compiled,Machine.RecordingHeads (emission compiled)]
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (source : SourceMachine.AState) (expected : List valtype) (pc : Nat) (pending : Bool)
    (decoded : source.store=Store.decodeStore view code store) (shaped : Store.Shape view store)
    (owned : SourceMachine.Ownership.StateOwned (Store.ownershipBounds store) source)
    (invariant : Machine.Execution view code store exec source expected pc pending)
    (active : 0<exec.frames.length)
    (address : runtime.FuncAddr) (selected : hostStepAddress exec store=some address) :
    StructuredHostSite view code exec store expected pc pending source := by
  rcases source with ⟨s,ambient,frames,results⟩
  cases frames with
  | nil =>
    have stack := invariant.stack
    cases stack with
    | empty empty => simp only [alloc.vec.Vec.length,empty,List.length_nil] at active;omega
  | cons f rest =>
    have noResults := invariant.typed.typed.activeResults (by simp)
    change results=[] at noResults
    subst results
    obtain ⟨raw,compiled,C,targets,next,output,top,position,program,point⟩ := invariant.cursor
    obtain ⟨inst,hi,hc,functionTable⟩ := program.lookup
    have bound : exec.frames.length-1≤Usize.max := (Nat.sub_le _ _).trans exec.frames.property
    have encoded : exec.frames.length-1<2^UScalarTy.Usize.numBits := by scalar_tac
    let index : Usize := UScalar.ofNatCore (exec.frames.length-1) encoded
    have indexVal : index.val=exec.frames.length-1 := UScalar.ofNatCore_val_eq encoded
    have last : index.val+1=exec.frames.length := by omega
    have hf : exec.frames.val[index.val]?=some raw := by
      rw [indexVal]
      simpa only [List.getLast?_eq_getElem?] using top
    have current := invariant.stack.top raw top
    have moduleEq := current.binding.module_lookup inst hi
    change s=Store.decodeStore view code store at decoded
    subst s
    have result := recording_frame_host_site view code exec store index raw inst compiled C targets next output ambient f rest
      last hf hi hc program current.slots moduleEq pending point expected (by simpa only [position] using invariant) shaped owned address selected
    simpa only [position] using result
end Itasca.Runtime.Integration

end
