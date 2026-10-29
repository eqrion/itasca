import Itasca.Runtime.SourceMachine.Indirect.Definition
import Itasca.Runtime.SourceMachine.Results
namespace Itasca.Runtime.SourceMachine.Indirect

theorem invoke_result {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
    {original : List instr} {values : List val} {address : Nat} {after : List instr} {next : AState} {expected : List valtype}
    (result : InvocationResult expected ⟨s,ambient,{f with code:=original}::rest,[]⟩)
    (stepped : invoke ⟨s,ambient,{f with code:=original}::rest,[]⟩ {f with vals:=values} rest address after=.next next) :
    InvocationResult expected next := by
  simp only [invoke] at stepped
  repeat' first | split at stepped | contradiction
  cases stepped
  exact FramesReturn.under (FramesReturn.replace result rfl)

theorem step_result {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
    {table type : Nat} {after : List instr} {next : AState} {expected : List valtype}
    (result : InvocationResult expected ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩)
    (stepped : step ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ f rest table type after=.next next) :
    InvocationResult expected next := by
  unfold step at stepped
  repeat' first | split at stepped | contradiction
  exact invoke_result result stepped
end Itasca.Runtime.SourceMachine.Indirect
