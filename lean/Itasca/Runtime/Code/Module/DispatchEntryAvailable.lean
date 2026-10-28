import Itasca.Stream.EntryFrame
import Itasca.Runtime.Code.Module.CompileEntry

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096
private theorem count_room (count limit : Usize) (less : count.val < limit.val) :
    count.val+1 ≤ Usize.max := by scalar_tac


private theorem count_not_ge (count limit : Usize) (less : count.val < limit.val) :
    ¬ count ≥ limit := by scalar_tac

/-- Source framing and intrinsic coordinate bounds construct the actual next
scheduler dispatch, retaining the independent validation cursor unchanged. -/
theorem compiler_next_entry_available (batch : stream.CodeBatch) (content finish : Usize)
    (remaining : batch.num_dispatched.val < batch.num_funcs.val)
    (indices : batch.first_func.val+batch.num_funcs.val ≤ Usize.max)
    (extent : ModuleCode.Extent batch.code batch.dispatch_end content finish)
    (coordinates : batch.code_offset.val+finish.val ≤ limits.MAX_MODULE_BYTES.val) :
    ∃ index count frame, index.val = batch.first_func.val+batch.num_dispatched.val ∧
      count.val = batch.num_dispatched.val+1 ∧ frame.index = index ∧
      stream.CodeBatch.next_entry batch = .ok (.Ok frame,{batch with num_dispatched := count,dispatch_end := finish}) := by
  obtain ⟨index,added,indexValue⟩ := WP.spec_imp_exists
    (Usize.add_spec (x := batch.first_func) (y := batch.num_dispatched) (by scalar_tac))
  obtain ⟨frame,framed,content',finish',actual,same,_,_,endValue,_⟩ :=
    stream.frame_entry.complete batch.code batch.dispatch_end index batch.code_offset content finish extent coordinates
  have finishEq : finish' = finish := by
    obtain ⟨size,read,span,bound⟩ := actual
    obtain ⟨size',read',span',bound'⟩ := extent
    obtain ⟨sizes,contents⟩ := ModuleCode.decoded_unique read read'
    apply UScalar.eq_of_val_eq
    rw [span,span',←sizes,←contents]
  subst finish'
  obtain ⟨endOffset,subtracted,offsetValue⟩ := WP.spec_imp_exists
    (Usize.sub_spec (x := frame.end) (y := batch.code_offset) (by scalar_tac))
  have offsetEq : endOffset = finish := UScalar.eq_of_val_eq (by omega)
  subst endOffset
  obtain ⟨count,increment,countValue⟩ := WP.spec_imp_exists
    (Usize.add_spec (x := batch.num_dispatched) (y := 1#usize) (by simpa using count_room _ _ remaining))
  refine ⟨index,count,frame,indexValue,by simpa using countValue,same,?_⟩
  have more : ¬ batch.num_dispatched ≥ batch.num_funcs := count_not_ge _ _ remaining
  simp [Itasca.stream.CodeBatch.next_entry,more,added,framed,
    core.result.Result.Insts.CoreOpsTry.branch,subtracted,increment]

end Itasca.Runtime.Code
