import Exec.Code.Body.Reader.Table.ReaderTableDispatchWasm1
import Exec.Code.Body.Reader.Table.ReaderTableWasm1
import Exec.Code.Body.Reader.Table.ReaderTableWasm2
import Exec.Code.Local.Coordinates.TableSourceCoordinates
import Exec.Code.Local.Publication.TableMapPublication

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Actual Wasm 1 label collection changes only budget and scratch. The final
table callback preserves both publication invariants at the reader's endpoint. -/
theorem reader_table_publication_wasm1 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st final : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (coordinates : SourceCoordinates before) (maps : ControlMapPublication before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ final.pos.val)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_BR_TABLE before = .ok (.Ok (),final,after)) :
    SourceCoordinates after ∧ ControlMapPublication after := by
  obtain ⟨actual,common,collected,read,callback⟩ := reader_table_dispatch_wasm1
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st final data env ctx before after accepted
  obtain ⟨count,first,last,ending,depths,budget,buffer,_,_,_,_,same,_⟩ :=
    compiler_read_br_table_wasm1 ops law before collected st final data actual common read
  subst collected
  exact ⟨compiler_br_table_source_coordinates ops law {before with budget,table_depths := buffer} after final actual
      (Control.resultView common) (by simpa only [SourceCoordinates] using coordinates) inside forward callback,
    compiler_br_table_map_publication ops law {before with budget,table_depths := buffer} after final actual
      (Control.resultView common) (maps.retained ⟨rfl,le_rfl⟩ rfl rfl le_rfl le_rfl) forward callback⟩

/-- Actual Wasm 2 table decoding, selector handling and label collection retain
publication bounds before its final table callback. -/
theorem reader_table_publication_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st final : code.BodyState) (data : Slice U8) (env : module.Env)
    (coordinates : SourceCoordinates before) (maps : ControlMapPublication before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ final.core.pos.val)
    (accepted : code.branch_table_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env before = .ok (.Ok (),final,after)) :
    SourceCoordinates after ∧ ControlMapPublication after := by
  obtain ⟨count,first,selector,popped,depths,fallback,types,last,readState,budget,buffer,_,_,_,_,_,_,_,callback⟩ :=
    compiler_read_br_table_wasm2 ops law before after st final data env accepted
  exact ⟨compiler_br_table_source_coordinates ops law {before with budget,table_depths := buffer} after final.core fallback
      types (by simpa only [SourceCoordinates] using coordinates) inside forward callback,
    compiler_br_table_map_publication ops law {before with budget,table_depths := buffer} after final.core fallback
      types (maps.retained ⟨rfl,le_rfl⟩ rfl rfl le_rfl le_rfl) forward callback⟩

end Exec.Code
