import Exec.Code.Body.Reader.Table.TableReaderCompilerPoint
import Exec.Code.Body.Reader.Common.CumulativeReaderCompilerPoint
namespace Exec.Code
open Aeneas Aeneas.Std

/-- Existing pair-only points are precisely the specialization of the common
four-table point whose emission relation ignores SIMD metadata. -/
theorem table_point_cumulative_wasm1 {A : Type}
    {C initial compiler types functions returns locals data env ctx bodyBt st} :
    TableReaderCompilerPointWasm1 (fun tables => CumulativeEmission tables.indirect C)
      (A := A) initial compiler types functions returns locals data env ctx bodyBt st ↔
    CumulativeReaderCompilerPointWasm1 C initial compiler types functions returns locals data env ctx bodyBt st := by
  constructor
  · intro point future
    exact point ⟨future,[],[],[]⟩
  · intro point future
    exact point future.indirect

theorem table_point_cumulative_wasm2 {A : Type}
    {C initial compiler types functions returns locals data env sourceLocals index ft st} :
    TableReaderCompilerPointWasm2 (fun tables => CumulativeEmission tables.indirect C)
      (A := A) initial compiler types functions returns locals data env sourceLocals index ft st ↔
    CumulativeReaderCompilerPointWasm2 C initial compiler types functions returns locals data env sourceLocals index ft st := by
  constructor
  · intro point future
    exact point ⟨future,[],[],[]⟩
  · intro point future
    exact point future.indirect
end Exec.Code
