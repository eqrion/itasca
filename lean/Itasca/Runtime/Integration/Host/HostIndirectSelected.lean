import Itasca.Runtime.Integration.Host.HostCallSource
import Itasca.Runtime.Interp.Relations.FrameStorePrefix
import Itasca.Runtime.Integration.Host.HostResumeOwned
import Itasca.Runtime.Integration.Host.HostStructuredResume
import Itasca.Runtime.Integration.Host.HostIndirectContext
import Itasca.Runtime.Integration.Execution.Ownership.FrameTypeBounds
import Itasca.Runtime.Integration.Execution.Ownership.Entry
import Itasca.Runtime.SourceMachine.Indirect.HostTyping
namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp
open Itasca.Runtime.Interp.Machine

theorem structured_indirect_host_next (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame)
    (rest : List SourceMachine.AFrame) (after : List instr) (table type position address identity : Nat)
    (params results : List valtype) (front args : List val)
    (resolved : SourceMachine.Indirect.resolve s f table type position=some address)
    (bounded : position<2^32) (host : HostFunction s address identity params results)
    (argumentTypes : args.map Compiler.valueType=params) :
    SourceMachine.Indirect.step ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after, vals:=(front++args)++[SourceMachine.integerVal .I32 position]}::rest,[]⟩
      {f with vals:=(front++args)++[SourceMachine.integerVal .I32 position]} rest table type after =
      .host address args results ⟨s,ambient,{f with code:=after,vals:=front}::rest,[]⟩ := by
  obtain ⟨moduleInst,lookup⟩ := host
  have types : args.map SourceMachine.valueType=params := by
    simpa only [show Compiler.valueType=SourceMachine.valueType from funext value_type_eq_abs] using argumentTypes
  have length : params.length=args.length := by rw [←argumentTypes,List.length_map]
  have decoded : SourceMachine.integer numtype.I32 (SourceMachine.integerVal .I32 position)=some position := SourceMachine.integer_accepts .I32 position bounded
  have resolved' : SourceMachine.Indirect.resolve s {f with vals:=(front++args)++[SourceMachine.integerVal .I32 position]} table type position=some address := resolved
  simp only [SourceMachine.Indirect.step,SourceMachine.pop_append,decoded,resolved']
  simp [SourceMachine.Indirect.invoke,lookup,length,types]

end Itasca.Runtime.Integration
