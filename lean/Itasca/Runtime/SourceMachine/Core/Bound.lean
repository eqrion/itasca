import Itasca.Runtime.SourceMachine.Bound
import Itasca.Runtime.SourceMachine.Core.Pure
namespace Itasca.Runtime.Abs.Core

/-- Code bounds depend on function bodies and frame continuations, so changing
only source object contents retains them. -/
theorem codeBound_store {bound : Nat} {s : AState} {target : _root_.store}
    (bounded : CodeBound bound s) (functions : target.FUNCS = s.store.FUNCS) :
    CodeBound bound {s with store := target} :=
  ⟨bounded.positive,bounded.frames,by simpa only [functions] using bounded.functions⟩

theorem advance_content_bound {bound : Nat} {s target : _root_.store} {ambient : frame}
    {f f' : AFrame} {rest : List AFrame} {next : AState}
    (bounded : CodeBound bound ⟨s,ambient,f::rest,[]⟩)
    (step : advance ⟨target,ambient,f::rest,[]⟩ f' rest = .next next)
    (functions : target.FUNCS = s.FUNCS) (frame : FrameCodeBound bound f') : CodeBound bound next :=
  advance_bound (codeBound_store (target := target) bounded functions) step frame

theorem instruction_bound (bound : Nat) (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (covered : CoreHead op) (typed : FrameTyped s {f with code := op::after} [])
    (bounded : CodeBound bound ⟨s,ambient,{f with code := op::after}::rest,[]⟩)
    (step : instruction s ambient f rest op after = .next next) : CodeBound bound next := by
  have hf := bounded.frames {f with code := op::after} (by simp)
  have ha : sizeOf after ≤ bound := by have hh := hf.1; simp at hh; omega
  have hl := hf.2
  cases covered with
  | pure pure =>
    rw [instruction_slice s ambient f rest op after pure typed] at step
    exact Abs.instruction_bound bound s ambient f rest op after next pure bounded step
  | const ty value => exact advance_bound bounded step ⟨ha,hl⟩
  | select =>
    simp only [instruction,select] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_bound bounded step ⟨ha,hl⟩
  | global_get index =>
    cases index
    simp only [instruction,globalGet] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_bound bounded step ⟨ha,hl⟩
  | global_set index =>
    cases index
    simp only [instruction,globalSet] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_content_bound bounded step rfl ⟨ha,hl⟩
  | load descriptor argument =>
    rw [instruction_load] at step
    simp only [load] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_bound bounded step ⟨ha,hl⟩
  | store descriptor argument =>
    rw [instruction_store] at step
    simp only [store] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_content_bound bounded step rfl ⟨ha,hl⟩

end Itasca.Runtime.Abs.Core
