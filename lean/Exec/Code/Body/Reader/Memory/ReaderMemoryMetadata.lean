import Exec.Code.Body.Reader.Common.ReaderMetadata
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2

theorem memory_size_fixed (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    code.read_memory_size st data env = metadataOperands (code.read_bulk_memory st data env)
      (fun _ => []) (fun _ => some .I32) id := by
  simp only [code.read_memory_size,code.read_bulk_memory,code.require_memory,alloc.vec.Vec.is_empty,metadataOperands,Simd.readFixed,Std.bind_assoc]
  repeat' first
    | rfl
    | (split <;> simp_all)
    | (congr 1
       funext pair
       obtain ⟨res,state⟩ := pair
       cases res <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
         core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
         Std.bind_assoc,Std.uncurry])

theorem memory_grow_fixed (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    code.read_memory_grow st data env = metadataOperands (code.read_bulk_memory st data env)
      (fun _ => [.I32]) (fun _ => some .I32) id := by
  simp only [code.read_memory_grow,code.read_bulk_memory,code.require_memory,alloc.vec.Vec.is_empty,metadataOperands,Simd.readFixed,Std.bind_assoc]
  repeat' first
    | rfl
    | (split <;> simp_all)
    | (congr 1
       funext pair
       obtain ⟨res,state⟩ := pair
       cases res <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
         core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
         Std.bind_assoc,Std.uncurry])

theorem reader_memory_size_wasm2 {data env locals index st}
    (p : Pending data env locals index st)
    (byte : data.val[p.start.val]'p.inbounds = 63#u8)
    (size : st.core.vals.val.length < Usize.max) (out : code.OpIterState)
    (accepted : code.read_memory_size st.core data env = .ok (.Ok (),out)) :
    MetadataReaderPost p (code.read_bulk_memory st.core data env) (fun _ => [])
      (fun _ => some .I32) id (fun _ => .MEMORY_SIZE) () out := by
  rw [memory_size_fixed] at accepted
  apply reader_metadata_wasm2 p (code.read_bulk_memory st.core data env) (fun _ => [])
    (fun _ => some .I32) id (fun _ => .MEMORY_SIZE) ?_ ?_ ?_ ?_ size () out accepted
  · apply WP.spec_mono (code.read_bulk_memory.spec st.core data env)
    rintro ⟨result,middle⟩ ⟨values,controls,decoded⟩
    refine ⟨values,controls,?_⟩
    intro unit success
    cases unit
    exact .plain (.of_immediate p.inbounds byte p.pos .memorySize (decoded success).1)
  · exact fun _ => .instr_case_62
  · rintro unit ⟨middle,read⟩ C matched
    cases unit
    have checked := code.read_bulk_memory.spec st.core data env
    rw [read,WP.spec_ok] at checked
    simpa [Simd.inputTypes,Simd.outputTypes,Translate.valueType] using matched.memory_size (checked.2.2 rfl).2
  · intro _ _
    simp [DeclaredReferences.Instruction,DeclaredReferences.instructionIndices]

theorem reader_memory_grow_wasm2 {data env locals index st}
    (p : Pending data env locals index st)
    (byte : data.val[p.start.val]'p.inbounds = 64#u8)
    (size : st.core.vals.val.length < Usize.max) (out : code.OpIterState)
    (accepted : code.read_memory_grow st.core data env = .ok (.Ok (),out)) :
    MetadataReaderPost p (code.read_bulk_memory st.core data env) (fun _ => [.I32])
      (fun _ => some .I32) id (fun _ => .MEMORY_GROW) () out := by
  rw [memory_grow_fixed] at accepted
  apply reader_metadata_wasm2 p (code.read_bulk_memory st.core data env) (fun _ => [.I32])
    (fun _ => some .I32) id (fun _ => .MEMORY_GROW) ?_ ?_ ?_ ?_ size () out accepted
  · apply WP.spec_mono (code.read_bulk_memory.spec st.core data env)
    rintro ⟨result,middle⟩ ⟨values,controls,decoded⟩
    refine ⟨values,controls,?_⟩
    intro unit success
    cases unit
    exact .plain (.of_immediate p.inbounds byte p.pos .memoryGrow (decoded success).1)
  · exact fun _ => .instr_case_63
  · rintro unit ⟨middle,read⟩ C matched
    cases unit
    have checked := code.read_bulk_memory.spec st.core data env
    rw [read,WP.spec_ok] at checked
    simpa [Simd.inputTypes,Simd.outputTypes,Translate.valueType] using matched.memory_grow (checked.2.2 rfl).2
  · intro _ _
    simp [DeclaredReferences.Instruction,DeclaredReferences.instructionIndices]

end Exec.Code
