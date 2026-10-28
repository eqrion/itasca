import Exec.Code.Module.Stream
import Itasca.Stream.DriverComplete

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

private theorem slice_value (data region : Slice U8) (first last : Usize)
    (ordered : first.val ≤ last.val) (bounded : last.val ≤ data.length)
    (called : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) data ⟨first,last⟩ = .ok region) :
    region.val = data.val.slice first.val last.val := by
  have post := core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec ⟨first,last⟩ data (by scalar_tac) bounded
  change core.slice.index.SliceIndexRangeUsizeSlice.index ⟨first,last⟩ data = .ok region at called
  rw [called,WP.spec_ok] at post
  exact post.1

/-- The runtime's immutable source makes every region of the canonical split
available whenever its scanner selected those same byte coordinates. -/
theorem compiler_source_regions_available (data : Slice U8) (regions : Itasca.stream.SliceSource)
    (codeStart codeEnd : Usize)
    (split : StreamCompleteRegions.Split data regions)
    (selected : Itasca.stream.find_code_region data = .ok (codeStart,codeEnd)) :
    StreamSource.Available runtime.compiler.CompileSource.Insts.ItascaStreamSource
      {bytes := data,code_start := codeStart,code_end := codeEnd} regions.env.val regions.code.val regions.tail.val := by
  obtain ⟨first,last,scanned,environment,code,tail⟩ := split
  have same : first = codeStart ∧ last = codeEnd := by
    simpa only [Result.ok.injEq,Prod.mk.injEq] using scanned.symm.trans selected
  simp only [same.1,same.2] at environment code tail
  obtain ⟨ordered,bounded⟩ := Itasca.stream.find_code_region.bounds data codeStart codeEnd selected
  have envValue := slice_value data regions.env 0#usize codeStart (by simp) (by omega) environment
  have codeValue := slice_value data regions.code codeStart codeEnd ordered bounded code
  have tailValue := slice_value data regions.tail codeEnd (Slice.len data) (by simpa using bounded) (by simp) tail
  have envEq : regions.env.val = data.val.take codeStart.val := by simpa [List.slice] using envValue
  have tailEq : regions.tail.val = data.val.drop codeEnd.val := by
    simp only [List.slice,Slice.len_val] at tailValue
    rw [←List.length_drop] at tailValue
    simpa only [List.take_length] using tailValue
  have available := source_available ({bytes := data,code_start := codeStart,code_end := codeEnd} : runtime.compiler.CompileSource)
    ⟨ordered,bounded⟩
  simpa only [sourceEnvironment,sourceCode,sourceTail,←envEq,←codeValue,←tailEq] using available

end Itasca.Runtime.Code
