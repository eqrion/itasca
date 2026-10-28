import Exec.Theorems.Host.HostCallSource
import Exec.Interp.Relations.FrameStorePrefix
import Exec.Theorems.Host.HostResumeOwned
import Exec.Theorems.Host.HostStructuredResume
import Exec.Theorems.Host.HostIndirectContext
import Exec.Theorems.Composition.FrameStorePrefixStaged
import Exec.Theorems.Composition.Core.CoreOwnership
import Exec.Abs.Indirect.HostTyping
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp
open Itasca.Runtime.Interp.StructuredMachine

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

end Itasca.Runtime.Theorems
