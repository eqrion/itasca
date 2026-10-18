import Exec.Abs.Stateful.Ownership
import Exec.Abs.FloatCore.Ambient
namespace Exec.Abs.Cumulative
open Exec.Abs.Ownership

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
end Exec.Abs.Cumulative
