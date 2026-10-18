import Exec.Code.Body.Reader.Common.ReaderMetadataWasm1
import Exec.Code.Body.Reader.Memory.ReaderMemoryMetadata
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm1

theorem reader_memory_size_wasm1 {data env ctx bt st}
    (p : Pending data env ctx bt st)
    (byte : data.val[p.start.val]'p.inbounds = 63#u8)
    (size : st.vals.val.length < Usize.max) (out : code.OpIterState)
    (accepted : code.read_memory_size st data env = .ok (.Ok (),out)) :
    MetadataReaderPostWasm1 p (code.read_bulk_memory st data env) (fun _ => [])
      (fun _ => some .I32) id (fun _ => .MEMORY_SIZE) () out := by
  rw [memory_size_fixed] at accepted
  apply reader_metadata_wasm1 p (code.read_bulk_memory st data env) (fun _ => [])
    (fun _ => some .I32) id (fun _ => .MEMORY_SIZE) ?_ ?_ ?_ ?_ size () out accepted
  · apply WP.spec_mono (code.read_bulk_memory.spec st data env)
    rintro ⟨result,middle⟩ ⟨values,controls,decoded⟩
    refine ⟨values,controls,?_⟩
    intro unit success
    cases unit
    exact .of_immediate p.inbounds byte p.pos .memorySize (decoded success).1
  · exact fun _ => .instr_case_62
  · rintro unit ⟨middle,read⟩ C matched
    cases unit
    have checked := code.read_bulk_memory.spec st data env
    rw [read,WP.spec_ok] at checked
    simpa [Wasm2.Simd.inputTypes,Wasm2.Simd.outputTypes,Translate.valueType] using matched.memory_size (checked.2.2 rfl).2
  · intro _ _
    exact .leaf _ _ (by trivial)

theorem reader_memory_grow_wasm1 {data env ctx bt st}
    (p : Pending data env ctx bt st)
    (byte : data.val[p.start.val]'p.inbounds = 64#u8)
    (size : st.vals.val.length < Usize.max) (out : code.OpIterState)
    (accepted : code.read_memory_grow st data env = .ok (.Ok (),out)) :
    MetadataReaderPostWasm1 p (code.read_bulk_memory st data env) (fun _ => [.I32])
      (fun _ => some .I32) id (fun _ => .MEMORY_GROW) () out := by
  rw [memory_grow_fixed] at accepted
  apply reader_metadata_wasm1 p (code.read_bulk_memory st data env) (fun _ => [.I32])
    (fun _ => some .I32) id (fun _ => .MEMORY_GROW) ?_ ?_ ?_ ?_ size () out accepted
  · apply WP.spec_mono (code.read_bulk_memory.spec st data env)
    rintro ⟨result,middle⟩ ⟨values,controls,decoded⟩
    refine ⟨values,controls,?_⟩
    intro unit success
    cases unit
    exact .of_immediate p.inbounds byte p.pos .memoryGrow (decoded success).1
  · exact fun _ => .instr_case_63
  · rintro unit ⟨middle,read⟩ C matched
    cases unit
    have checked := code.read_bulk_memory.spec st data env
    rw [read,WP.spec_ok] at checked
    simpa [Wasm2.Simd.inputTypes,Wasm2.Simd.outputTypes,Translate.valueType] using matched.memory_grow (checked.2.2 rfl).2
  · intro _ _
    exact .leaf _ _ (by trivial)

end Exec.Code
