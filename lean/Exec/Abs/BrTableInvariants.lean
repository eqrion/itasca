import Exec.Abs.BrTable
import Exec.Abs.Cumulative.Heap
import Exec.Abs.Supported.Language
import Exec.Abs.Bound
namespace Exec.Abs.BrTable
open Ownership

/-- Selecting a label only removes the integer selector; all owned references
and every source heap component are retained. -/
theorem owned {bounds : Bounds} {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
    {after : List instr} {labels : List labelidx} {fallback : labelidx} {front : List val} {bits : Nat}
    (before : StatefulOwned bounds ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after,vals := front ++ [integerVal .I32 bits]}::rest,[]⟩) :
    StatefulOwned bounds ⟨s,ambient,{f with code := .BR (select labels fallback bits)::after,vals := front}::rest,[]⟩ := by
  have frame := before.values.2 _ (List.mem_cons_self ..)
  apply stateful_owned_advance (step := rfl) before.heap (valuesOwned_nil _) ?_ ?_
  · exact ⟨frame.1,(valuesOwned_append.mp frame.2).1⟩
  · exact fun item member => before.values.2 item (List.mem_cons_of_mem _ member)

theorem bounded {bound : Nat} {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
    {after : List instr} {labels : List labelidx} {fallback : labelidx} {front : List val} {bits : Nat}
    (before : CodeBound bound ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after,vals := front ++ [integerVal .I32 bits]}::rest,[]⟩) :
    CodeBound bound ⟨s,ambient,{f with code := .BR (select labels fallback bits)::after,vals := front}::rest,[]⟩ := by
  apply bound_replace_frame before
  have frame := before.frames _ (List.mem_cons_self ..)
  refine ⟨?_,frame.2⟩
  have size := frame.1
  have selected := select_size labels fallback bits
  simp at size ⊢
  omega

theorem covered {allowed : instr → Prop} (language : Supported.Language allowed)
    {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
    {after : List instr} {labels : List labelidx} {fallback : labelidx} {front : List val} {bits : Nat}
    (before : SupportedState allowed ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after,vals := front ++ [integerVal .I32 bits]}::rest,[]⟩) :
    SupportedState allowed ⟨s,ambient,{f with code := .BR (select labels fallback bits)::after,vals := front}::rest,[]⟩ := by
  have frame := before.active _ (List.mem_cons_self ..)
  refine ⟨?_,before.functions⟩
  intro item member
  rcases List.mem_cons.mp member with rfl | member
  · refine ⟨?_,frame.2⟩
    intro instruction member
    rcases List.mem_cons.mp member with rfl | member
    · exact language.cumulative (.core (.core (.slice (.br (select labels fallback bits)))))
    · exact frame.1 instruction (List.mem_cons_of_mem _ member)
  · exact before.active item (List.mem_cons_of_mem _ member)
end Exec.Abs.BrTable
