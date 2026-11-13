import Itasca.Runtime.SourceMachine.Stateful.Ownership
import Itasca.Runtime.SourceMachine.Core.Trap
import Itasca.Runtime.SourceMachine.Indirect.Correct
import Itasca.Runtime.SourceMachine.Indirect.Transport
import Itasca.Runtime.SourceMachine.Supported.CoreStuck
import Itasca.Runtime.SourceMachine.Core.SelectPositive
import Itasca.Runtime.SourceMachine.Ownership.Core
import Itasca.Runtime.SourceMachine.Stateful.Bound
import Itasca.Runtime.SourceMachine.Float.Transition
import Itasca.Runtime.SourceMachine.Measure
import Itasca.Runtime.SourceMachine.Float.Results
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.Bound

/-!
Sections, each formerly its own module: Heap, Step.
-/

/-! ## Heap -/

section

namespace Itasca.Runtime.SourceMachine.Cumulative
open Itasca.Runtime.SourceMachine.Ownership

theorem core_heap_metadata {s next : AState} (equation : Core.step s = .next next) :
    next.store.TABLES = s.store.TABLES ∧ next.store.ELEMS = s.store.ELEMS ∧ next.store.FUNCS = s.store.FUNCS := by
  simp only [Core.step,Core.instruction,astep] at equation
  repeat' first | split at equation | contradiction
  all_goals
    simp only [advance,returnFrame,enterLabel,branch,call,Numeric.transition,Numeric.finish,
      Core.select,Core.globalGet,Core.globalSet,Core.load,Core.store] at equation
    repeat' first | split at equation | contradiction
    all_goals
      simp only [advance,AResult.next.injEq] at equation
      cases equation
      exact ⟨rfl,rfl,rfl⟩

theorem core_heap_owned {bounds s next} (heap : StatefulHeapOwned bounds s.store)
    (globals : GlobalsOwned bounds next.store) (equation : Core.step s = .next next) :
    StatefulHeapOwned bounds next.store := by
  obtain ⟨tables,elements,functions⟩ := core_heap_metadata equation
  exact ⟨globals,by simpa only [tables] using heap.tables,by simpa only [elements] using heap.elements,
    by simpa only [functions] using heap.functions⟩
end Itasca.Runtime.SourceMachine.Cumulative

end

/-! ## Step -/

section

namespace Itasca.Runtime.SourceMachine.Cumulative
open SpecExt Itasca.Runtime.Spec Itasca.Runtime.SourceMachine.Ownership

/-- Executable source transitions combine the deterministic mutable core with
the complete float result relation, preserving every permitted NaN result. -/
inductive Step : AState → AResult → Prop where
  | core {before result} (equation : Core.step before = result) (executable : result ≠ .stuck) : Step before result
  | scalar {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
      {after : List instr} {op : Float.Instruction} {result : AResult}
      (transition : Float.Transition ⟨s,ambient,{f with code := op.source :: after}::rest,[]⟩
        {f with code := op.source :: after} rest after op result) :
      Step ⟨s,ambient,{f with code := op.source :: after}::rest,[]⟩ result

  | stateful {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
      {after : List instr} {op : Stateful.Instruction} {result : AResult}
      (transition : Stateful.Transition ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩
        {f with code := op.source::after} rest after op result)
      (executable : result ≠ .stuck) :
      Step ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ result

  | indirect {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
      {after : List instr} {table type : Nat} {result : AResult}
      (equation : Indirect.step ⟨s,ambient,{f with code := .CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩
        f rest table type after = result) (executable : result ≠ .stuck) :
      Step ⟨s,ambient,{f with code := .CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ result

end Itasca.Runtime.SourceMachine.Cumulative

end
