import Itasca.Runtime.Code.Body.Reader.Table.ReaderTableWasm2
import Itasca.Runtime.Code.Local.Coordinates.TableSourceCoordinates
import Itasca.Runtime.Code.Local.Publication.TableMapPublication
import Itasca.Runtime.Code.Body.Reader.Table.ReaderTableSuffix
import Itasca.Runtime.Code.Local.Relations.Table.BranchTableOperands
import Itasca.Runtime.Code.Body.Reader.Table.ReaderTableSource

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Actual Wasm 2 table decoding, selector handling and label collection retain
publication bounds before its final table callback. -/
theorem reader_table_publication_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st final : code.BodyState) (data : Slice U8) (env : module.Env)
    (coordinates : SourceCoordinates before) (maps : ControlMapPublication before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ final.core.pos.val)
    (accepted : code.branch_table_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env .Wasm2 before = .ok (.Ok (),final,after)) :
    SourceCoordinates after ∧ ControlMapPublication after := by
  obtain ⟨count,first,selector,popped,depths,fallback,types,last,readState,budget,buffer,_,_,_,_,_,_,_,callback⟩ :=
    compiler_read_br_table ops law before after st final data env _ accepted
  exact ⟨compiler_br_table_source_coordinates ops law {before with budget,table_depths := buffer} after final.core fallback
      types (by simpa only [SourceCoordinates] using coordinates) inside forward callback,
    compiler_br_table_map_publication ops law {before with budget,table_depths := buffer} after final.core fallback
      types (maps.retained ⟨rfl,le_rfl⟩ rfl rfl le_rfl le_rfl) forward callback⟩

end Itasca.Runtime.Code
