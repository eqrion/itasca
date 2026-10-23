import Exec.Theorems.Host.HostRecordingSite
import Exec.Interp.StructuredMachine.FunctionEnd
import Exec.Interp.StructuredMachine.NormalizeExecution
import Exec.Interp.StructuredMachine.SupportedControlSemantics
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

theorem HostFrameSite.recording_normal {M : Type}
    {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}
    [∀compiled,StructuredMachine.OrdinaryHeads (emission compiled)]
    [∀compiled,StructuredMachine.IndirectProjection (emission compiled) compiled.indirect.val]
    [∀compiled,StructuredMachine.RecordingHeads (emission compiled)]
    {view : M → Slice U8} {code : Store.CodeInterpretation} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {expected : List valtype} {ambient : frame} {f : Abs.AFrame} {rest : List Abs.AFrame}
    (site : HostFrameSite emission allowed view code exec store expected ambient f rest)
    (ready : ReadySource f) (shaped : Store.Shape view store)
    (address : runtime.FuncAddr) (selected : hostStepAddress exec store=some address) :
    StructuredHostSite emission allowed view code exec store expected site.raw.pc.val false
      ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ := by
  cases source : f.code with
  | nil =>
    have labels : f.labels=[] := by simpa only [ReadySource,source] using ready
    have same : {f with code:=[],labels:=[]}=f := by rw [←source,←labels]
    rcases StructuredMachine.function_end site.program (by simpa only [same] using site.point) with jump | returned
    · obtain ⟨target,forward,fetch,tail⟩ := jump
      rw [hostStepAddress_at _ _ _ _ _ _ _ site.last site.frameAt site.instanceAt site.compiledAt fetch] at selected
      simp [hostInstructionAddress,Bind.bind,Option.bind] at selected
    · obtain ⟨count,fetch,locals,width,bound⟩ := returned
      rw [hostStepAddress_at _ _ _ _ _ _ _ site.last site.frameAt site.instanceAt site.compiledAt fetch] at selected
      simp [hostInstructionAddress,Bind.bind,Option.bind] at selected
  | cons op after =>
    have same : {f with code:=op::after}=f := by rw [←source]
    have readyOp : ReadyInstruction op := by cases op <;> simp_all only [ReadyInstruction,ReadySource,source]
    let current : HostFrameSite emission allowed view code exec store expected ambient {f with code:=op::after} rest :=
      ⟨site.index,site.raw,site.inst,site.compiled,site.context,site.targets,site.next,site.output,
        site.last,site.frameAt,site.instanceAt,site.compiledAt,site.program,site.slots,site.moduleEq,
        by simpa only [same] using site.point,by simpa only [same] using site.machine,by simpa only [same] using site.owned⟩
    have result := current.recording_ready op after readyOp shaped address selected
    simpa only [same] using result

theorem recording_frame_host_site {M : Type} {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}
    [∀compiled,StructuredMachine.OrdinaryHeads (emission compiled)]
    [∀compiled,StructuredMachine.ErasedHeads (emission compiled)]
    [∀compiled,StructuredMachine.IndirectProjection (emission compiled) compiled.indirect.val]
    [∀compiled,StructuredMachine.RecordingHeads (emission compiled)]
    (language : Abs.Supported.Language allowed)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (last : index.val+1 = exec.frames.length) (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f) (moduleEq : f.module=Store.decodeInstance store inst)
    (pending : Bool)
    (point : StructuredMachine.ControlPoint emission (Store.decodeStore view code store) raw f compiled C targets next output pending)
    (expected : List valtype)
    (machine : StructuredMachine.Execution emission (Abs.SupportedState allowed) view code store exec
      ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ expected raw.pc.val pending)
    (shaped : Store.Shape view store)
    (owned : Abs.Ownership.StateOwned (Store.ownershipBounds store) ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩)
    (address : runtime.FuncAddr) (selected : hostStepAddress exec store=some address) :
    StructuredHostSite emission allowed view code exec store expected raw.pc.val pending
      ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ := by
  cases point with
  | jump target fetched continuation =>
    rw [hostStepAddress_at _ _ _ _ _ _ _ last hf hi hc fetched] at selected
    simp [hostInstructionAddress,Bind.bind,Option.bind] at selected
  | ready point =>
    obtain ⟨count,g,labels,stop,types,chain,bound,represented,continuation,retained,metadata,done⟩ :=
      StructuredMachine.normalize_execution (StructuredMachine.supportedControlSemantics language) view code store exec raw index compiled C targets next output ambient f rest
        last hf program slots point expected machine
    have nextProgram : FrameProgram store raw compiled (g.locals.map Code.valueType) g.resultTypes C.FUNCS := program.reposition raw.pc metadata
    rcases done with skip | ready
    · obtain ⟨target,forward,fetched,tail⟩ := skip
      rw [hostStepAddress_at _ _ _ _ _ _ _ last hf hi hc fetched] at selected
      simp [hostInstructionAddress,Bind.bind,Option.bind] at selected
    · have nextModule : g.module=Store.decodeInstance store inst := metadata.module.trans moduleEq
      have nextOwned : Abs.Ownership.StateOwned (Store.ownershipBounds store) ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
        refine ⟨owned.1,?_⟩
        intro item member
        rcases List.mem_cons.mp member with rfl | member
        · exact chain.ownership _ (owned.2 f (by simp))
        · exact owned.2 item (List.mem_cons_of_mem f member)
      let site : HostFrameSite emission allowed view code exec store expected ambient g rest :=
        ⟨index,raw,inst,compiled,C,labels,stop,types,last,hf,hi,hc,nextProgram,represented,nextModule,continuation,retained,nextOwned⟩
      exact .normalize chain (site.recording_normal ready shaped address selected)

theorem recording_host_site {M : Type} {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}
    [∀compiled,StructuredMachine.OrdinaryHeads (emission compiled)]
    [∀compiled,StructuredMachine.ErasedHeads (emission compiled)]
    [∀compiled,StructuredMachine.IndirectProjection (emission compiled) compiled.indirect.val]
    [∀compiled,StructuredMachine.RecordingHeads (emission compiled)]
    (language : Abs.Supported.Language allowed)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (source : Abs.AState) (expected : List valtype) (pc : Nat) (pending : Bool)
    (decoded : source.store=Store.decodeStore view code store) (shaped : Store.Shape view store)
    (owned : Abs.Ownership.StateOwned (Store.ownershipBounds store) source)
    (invariant : StructuredMachine.Execution emission (Abs.SupportedState allowed) view code store exec source expected pc pending)
    (active : 0<exec.frames.length)
    (address : runtime.FuncAddr) (selected : hostStepAddress exec store=some address) :
    StructuredHostSite emission allowed view code exec store expected pc pending source := by
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
    have result := recording_frame_host_site language view code exec store index raw inst compiled C targets next output ambient f rest
      last hf hi hc program current.slots moduleEq pending point expected (by simpa only [position] using invariant) shaped owned address selected
    simpa only [position] using result
end Exec.Theorems
