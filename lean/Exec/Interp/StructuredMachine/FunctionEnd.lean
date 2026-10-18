import Exec.Interp.StructuredMachine.IndexedEmpty
import Exec.Interp.StructuredMachine.FrameStack
import Exec.Interp.Core.EmptyInversion
import Exec.Code.Local.Control.Table.StructuredCodeWithTablesLabels
import Exec.Interp.Relations.Epilogue

namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std

/-- An empty outer source continuation either skips forward administratively
or fetches the compiler's exact final Return. Root alignment rules out falling
past the bytecode vector. -/
theorem function_end {M : Type} {emission : FunctionEmission} {store : runtime.store.Store M}
    {raw : runtime.interp.Frame} {source : Abs.AFrame}
    {compiled : runtime.bytecode.CompiledFunction} {C : context} {s : _root_.store} {targets next output}
    (program : FrameProgram store raw compiled (source.locals.map Code.valueType) source.resultTypes C.FUNCS)
    (point : FramePoint emission s raw { source with code := [], labels := [] }
      compiled C targets next output) :
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint emission s { raw with pc := target } { source with code := [], labels := [] }
        compiled C targets next output) ∨
    (∃ count : U32, compiled.code.val[raw.pc.val]? = some (.Return compiled.local_slots count) ∧
      compiled.local_slots.val = Code.slots (source.locals.map Code.valueType) ∧
      count.val = Code.slots source.resultTypes ∧ raw.pc.val < U32.max) := by
  have noTargets : targets = [] := by
    have empty : targets.length = 0 := point.labels.length.symm
    cases targets with
    | nil => rfl
    | cons head tail => simp at empty
  rcases structuredCodeWithTables_empty_inv point.code.current with skip | done
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    exact Or.inl ⟨target, forward, fetched,
      point.bindings,point.locals,point.labels, continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩
  · obtain ⟨position, _⟩ := done
    obtain ⟨endpoint, _, src, count, width, rootFetched⟩ := point.code.root noTargets
    obtain ⟨epilogue, actualCount, finalPosition, fetched⟩ := program.epilogue
    have same : raw.pc.val = epilogue.val := by omega
    have endpointSame : next = epilogue.val := by omega
    rw [endpointSame, fetched] at rootFetched
    have counts : actualCount = count := by
      have equal := Option.some.inj rootFetched
      simp only [runtime.bytecode.Instr.Return.injEq] at equal
      exact equal.2
    have actual : compiled.code.val[raw.pc.val]? = some (.Return compiled.local_slots actualCount) := by
      rw [same]; exact fetched
    exact Or.inr ⟨actualCount, actual, program.localSlots, by rw [counts]; exact width,
      program.fetched_bound _ actual⟩

end Exec.Interp.StructuredMachine
