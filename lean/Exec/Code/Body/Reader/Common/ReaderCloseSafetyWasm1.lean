import Exec.Code.Body.Reader.Common.ReaderCloseSafety
import Exec.Code.Body.Reader.Common.ReaderSafety
import Exec.Code.Body.Reader.Common.ReaderCloseWasm1
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem StructuredCompilerPrefixWithTables.end_reader_wasm1_total {jumpTables : List U32} {A}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefixWithTables jumpTables emit initial compiler types functions returns locals parents current raw position)
    (bounded : position ≤ limits.MAX_MODULE_BYTES.val)
    {data env ctx bodyBt state} (p : Wasm1.Pending data env ctx bodyBt state)
    (coordinate : compiler.function.body_start.val+state.pos.val ≤ Usize.max)
    (emitCoordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max) :
    CoreVisitor.run (code.read_end state)
      (fun c s pair => (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_end c s pair.1 (Control.signature pair.2)) compiler ⦃ out =>
        out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  obtain ⟨C,outer,spine,header,base,typed,controls,values⟩ := p.opened
  have effect := code.read_end.realizes state (p.parents.map Wasm1.Frames.Saved.ctrl) p.current.ctrl
    outer p.current.vals controls values base (Nat.le_of_lt p.val_capacity)
  apply reader_run_reached _ _ compiler (fun s c => ObservedStack c s.vals.val)
  · exact WP.spec_mono effect (by simp)
  · intro out pair read
    rw [read,WP.spec_ok] at effect
    have positionEq : out.pos = state.pos := effect.1
    exact invariant.end_total ops law bounded out pair.1 (Control.signature pair.2)
      (by simpa [positionEq] using coordinate) emitCoordinate

theorem StructuredCompilerPrefixWithTables.else_reader_wasm1_total {jumpTables : List U32} {A}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefixWithTables jumpTables emit initial compiler types functions returns locals parents current raw position)
    (bounded : position ≤ limits.MAX_MODULE_BYTES.val)
    {data env ctx bodyBt state} (p : Wasm1.Pending data env ctx bodyBt state)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (emitCoordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max) :
    CoreVisitor.run (code.read_else state)
      (fun c s bt => (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_else c s (Control.signature bt)) compiler ⦃ out =>
        out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  obtain ⟨C,outer,spine,header,base,typed,controls,values⟩ := p.opened
  have effect := code.read_else.realizes state (p.parents.map Wasm1.Frames.Saved.ctrl) p.current.ctrl
    outer p.current.vals controls values base
  apply reader_run_reached _ _ compiler (fun s c => ObservedStack c s.vals.val)
  · exact WP.spec_mono effect (by simp)
  · intro out bt read
    exact invariant.else_total ops law bounded fixups out (Control.signature bt) emitCoordinate
end Exec.Code
