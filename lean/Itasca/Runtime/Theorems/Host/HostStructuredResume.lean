import Itasca.Runtime.Theorems.Host.HostCallFrames
import Itasca.Runtime.Interp.StructuredMachine.HostReturnFrames
import Itasca.Runtime.Theorems.Composition.Certified.CertifiedSupported
import Itasca.Runtime.Interp.StructuredMachine.HostCallStack
import Itasca.Runtime.Abs.HostCallSite
import Itasca.Runtime.Interp.StructuredMachine.Execution
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp
open Itasca.Runtime.Interp.StructuredMachine

theorem structured_host_next (s : _root_.store) (ambient : frame) (f : Abs.AFrame)
    (rest : List Abs.AFrame) (after : List instr) (index address identity : Nat)
    (params results : List valtype) (front args : List val)
    (resolve : f.module.FUNCS[index]? = some address)
    (host : HostFunction s address identity params results)
    (argumentTypes : args.map Code.valueType = params) :
    Abs.astep ⟨s,ambient,{f with code := .CALL (.mk_uN index)::after,vals := front++args}::rest,[]⟩ =
      .host address args results ⟨s,ambient,{f with code := after,vals := front}::rest,[]⟩ := by
  obtain ⟨moduleInst,lookup⟩ := host
  have types : args.map Abs.valueType = params := by
    have same : Abs.valueType = Code.valueType := by funext v; exact (valueType_eq_abs v).symm
    rw [same,argumentTypes]
  have length : params.length = args.length := by rw [← argumentTypes,List.length_map]
  simp [Abs.astep,Abs.call,resolve,lookup,length,types]

/-- Checked host results resume the complete generic machine. Raw metadata
retention is explicit; newly added functions come from the fresh certificate. -/
theorem host_structured_resume {M P : Type}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {ambient : frame} {f : Abs.AFrame} {rest : List Abs.AFrame} {op : instr} {after : List instr}
    {expected : List valtype} {sourcePC : Nat} {pendingFlag : Bool}
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := op::after}::rest,[]⟩ expected sourcePC pendingFlag)
    {raw : runtime.interp.Frame} {frameIndex : Usize} {pc : U32}
    (last : frameIndex.val+1=exec.frames.length)
    (lookup : exec.frames.val[frameIndex.val]?=some raw)
    (binding : FrameBinding store exec raw f) (slots : FrameSlots exec raw f)
    {compiled C targets next output}
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint (Store.decodeStore view code store) raw
      {f with code := op::after} compiled C targets next output)
    {front args consumed : List val} {returns : List valtype} {address : runtime.FuncAddr} {base : Usize}
    (split : f.vals=front++consumed)
    (destination : base.val=raw.base.val+Code.slots ((f.locals++front).map Code.valueType))
    (heights : ∀ label∈f.labels, label.height≤front.length)
    (continuation : Code.StructuredCode (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (front.map Code.valueType++returns) after pc.val next output)
    (pending : Abs.HostPending
      ⟨Store.decodeStore view code store,ambient,{f with code := after,vals := front}::rest,[]⟩ returns)
    {out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P}
    {callFrame : frame}
    (observed : HostCallSourceOutcome view code store callFrame address args base
      {exec with frames := exec.frames.set frameIndex {raw with pc := pc}} out)
    (success : out.1=.Ok ())
    (retained : FrameStorePrefix store out.2.2.1) (bounds : FrameTypeBounds store)
    (extension : Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1))
    (fresh : CertifiedSupportedStore view code out.2.2.1)
    (returned : ResultsTyped (Store.decodeStore view code out.2.2.1) returns (out.2.1.host_results.val.map sourceValue)) :
    ∃ finalPC, Execution view code out.2.2.1 out.2.1
      ⟨Store.decodeStore view code out.2.2.1,ambient,
        {f with code := after,vals := front++out.2.1.host_results.val.map sourceValue}::rest,[]⟩ expected finalPC false := by
  have valueTypes : (out.2.1.host_results.val.map sourceValue).map Code.valueType=returns := by
    have same : Code.valueType = Abs.valueType := by funext v; exact valueType_eq_abs v
    rw [same]; exact Abs.results_type_of_typed returned
  obtain ⟨stack,ready⟩ := machine.stack.host_call_return raw frameIndex pc last lookup binding slots program point
    front consumed after returns base.val split destination heights continuation out.2.2.1
    (Store.decodeStore view code out.2.2.1) retained bounds extension out.2.1
    (out.2.1.host_results.val.map sourceValue) (observed.return_effect success) valueTypes
  obtain ⟨finalPC,cursor⟩ := ready.cursor
  refine ⟨finalPC,rfl,⟨?_,fresh.contents_typed⟩,?_,?_,stack,cursor⟩
  · exact pending.finish_typed extension fresh.functions_typed returned
  · refine ⟨?_,fresh.supported⟩
    intro item member
    rcases List.mem_cons.mp member with rfl | member
    · have old := machine.core.active _ (List.mem_cons_self ..)
      exact ⟨fun instruction member => old.1 instruction (List.mem_cons_of_mem _ member),old.2⟩
    · exact machine.core.active item (List.mem_cons_of_mem _ member)
  · exact Abs.FramesReturn.replace machine.result rfl
end Itasca.Runtime.Theorems
