import Exec.Abs.BrTableInvariants
import Exec.Abs.Core.Typing
namespace Exec.Abs.BrTable
open Ownership

theorem next_shape {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
    {after : List instr} {labels : List labelidx} {fallback : labelidx} {next : AState}
    (typed : ATyped ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after}::rest,[]⟩)
    (equation : step ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after}::rest,[]⟩
      {f with code := .BR_TABLE labels fallback::after} rest after labels fallback = .next next) :
    ∃ front bits, f.vals = front ++ [integerVal .I32 bits] ∧ bits < 2^32 ∧
      next = ⟨s,ambient,{f with code := .BR (select labels fallback bits)::after,vals := front}::rest,[]⟩ := by
  have frameTyped : FrameTyped s {f with code := .BR_TABLE labels fallback::after} [] := by
    cases typed.frames with | cons head _ => exact head
  obtain ⟨front,bits,values,bound⟩ := operands frameTyped
  have actual := step_eq s ambient f rest after front bits labels fallback bound
  have actual' : step ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after}::rest,[]⟩
      {f with code := .BR_TABLE labels fallback::after} rest after labels fallback =
      .next ⟨s,ambient,{f with code := .BR (select labels fallback bits)::after,vals := front}::rest,[]⟩ := by
    simpa only [← values] using actual
  exact ⟨front,bits,values,bound,AResult.next.inj (equation.symm.trans actual')⟩

theorem next_correct {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
    {after : List instr} {labels : List labelidx} {fallback : labelidx} {next : AState}
    (typed : CoreTyped ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after}::rest,[]⟩)
    (equation : step ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after}::rest,[]⟩
      {f with code := .BR_TABLE labels fallback::after} rest after labels fallback = .next next) :
    CoreTyped next ∧ NextSim ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after}::rest,[]⟩ next := by
  obtain ⟨front,bits,values,bound,rfl⟩ := next_shape typed.typed equation
  have original : ATyped ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after,vals := front ++ [integerVal .I32 bits]}::rest,[]⟩ := by
    simpa only [←values] using typed.typed
  obtain ⟨fresh,source⟩ := correct s ambient f rest after front bits labels fallback bound original
  exact ⟨⟨fresh,typed.contents⟩,by simpa only [←values] using source⟩

theorem next_owned {bounds : Bounds} {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
    {after : List instr} {labels : List labelidx} {fallback : labelidx} {next : AState}
    (typed : ATyped ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after}::rest,[]⟩)
    (before : StatefulOwned bounds ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after}::rest,[]⟩)
    (equation : step ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after}::rest,[]⟩
      {f with code := .BR_TABLE labels fallback::after} rest after labels fallback = .next next) :
    StatefulOwned bounds next := by
  obtain ⟨front,bits,values,bound,rfl⟩ := next_shape typed equation
  apply owned
  simpa only [←values] using before

theorem next_bound {bound : Nat} {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
    {after : List instr} {labels : List labelidx} {fallback : labelidx} {next : AState}
    (typed : ATyped ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after}::rest,[]⟩)
    (before : CodeBound bound ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after}::rest,[]⟩)
    (equation : step ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after}::rest,[]⟩
      {f with code := .BR_TABLE labels fallback::after} rest after labels fallback = .next next) :
    CodeBound bound next := by
  obtain ⟨front,bits,values,bitsBound,rfl⟩ := next_shape typed equation
  apply bounded
  simpa only [←values] using before

theorem next_covered {allowed : instr → Prop} (language : Supported.Language allowed)
    {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
    {after : List instr} {labels : List labelidx} {fallback : labelidx} {next : AState}
    (typed : ATyped ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after}::rest,[]⟩)
    (before : SupportedState allowed ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after}::rest,[]⟩)
    (equation : step ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after}::rest,[]⟩
      {f with code := .BR_TABLE labels fallback::after} rest after labels fallback = .next next) :
    SupportedState allowed next := by
  obtain ⟨front,bits,values,bound,rfl⟩ := next_shape typed equation
  apply covered language
  simpa only [←values] using before
end Exec.Abs.BrTable
