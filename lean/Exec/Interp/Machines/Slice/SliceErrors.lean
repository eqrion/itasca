import Exec.Interp.Machines.Slice.SliceHistory

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- A defined call can reject only for interruption or one of its three
resource classes; the stronger `CallCause` retains the exact witnesses. -/
theorem CallCause.kind {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {base : Usize}
    {compiled : runtime.bytecode.CompiledFunction} {error : runtime.ExecError}
    (cause : CallCause allocator hooks exec store platform base compiled error) :
    error = .Terminated ∨ error = .Exhausted .CallStack ∨
      error = .Exhausted .Values ∨ error = .Exhausted .Allocation := by
  cases error <;> simp only [CallCause] at cause <;> simp_all
  rename_i resource
  cases resource <;> simp_all

theorem DirectCallCause.kind {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {index : Usize}
    {raw : runtime.interp.Frame} {inst : runtime.store.ModuleInst}
    {compiled : runtime.bytecode.CompiledFunction} {error : runtime.ExecError}
    (cause : DirectCallCause allocator hooks exec store platform index raw inst compiled error) :
    error = .Terminated ∨ error = .Exhausted .CallStack ∨
      error = .Exhausted .Values ∨ error = .Exhausted .Allocation := by
  obtain ⟨target, offset, pc, address, base, function, instanceIndex, functionIndex,
    callee, code, fetch, resolved, lookup, wasm, instanceLookup, codeLookup, baseEq, pcEq, rejection⟩ := cause
  exact rejection.kind

end Exec.Interp
