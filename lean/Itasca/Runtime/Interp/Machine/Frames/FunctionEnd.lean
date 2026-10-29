import Itasca.Runtime.Interp.Machine.Normalization.IndexedEmpty
import Itasca.Runtime.Interp.Machine.Frames.FrameStack
import Itasca.Runtime.Interp.Machine.Emission.Empty
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredCodeLabels
import Itasca.Runtime.Interp.Relations.Epilogue

/-!
An empty outer source continuation either skips forward administratively or fetches the compiler's exact final Return. Root alignment rules out falling past the bytecode vector.

Main declarations: `function_end`. A direct consumer is `Interp.Machine.Frames.EpilogueExecution`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

/-- An empty outer source continuation either skips forward administratively
or fetches the compiler's exact final Return. Root alignment rules out falling
past the bytecode vector. -/
theorem function_end {M : Type} {store : runtime.store.Store M}
    {raw : runtime.interp.Frame} {source : SourceMachine.AFrame}
    {compiled : runtime.bytecode.CompiledFunction} {C : context} {s : _root_.store} {targets next output}
    (program : FrameProgram store raw compiled (source.locals.map Compiler.valueType) source.resultTypes C.FUNCS)
    (point : FramePoint s raw { source with code := [], labels := [] }
      compiled C targets next output) :
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint s { raw with pc := target } { source with code := [], labels := [] }
        compiled C targets next output) ∨
    (∃ count : U32, compiled.code.val[raw.pc.val]? = some (.Return compiled.local_slots count) ∧
      compiled.local_slots.val = Compiler.slots (source.locals.map Compiler.valueType) ∧
      count.val = Compiler.slots source.resultTypes ∧ raw.pc.val < U32.max) := by
  have noTargets : targets = [] := by
    have empty : targets.length = 0 := point.labels.length.symm
    cases targets with
    | nil => rfl
    | cons head tail => simp at empty
  rcases structured_code_empty_inv point.code.current with skip | done
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

end Itasca.Runtime.Interp.Machine
