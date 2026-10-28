import Itasca.Runtime.Code.Body.Reader.Table.TableDecodePrefix
import Itasca.Runtime.Code.Local.Source.SourceBudget

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

private theorem table_source_word_room : 3*limits.MAX_MODULE_BYTES.val ≤ Usize.max := by
  norm_num [limits.MAX_MODULE_BYTES]
  scalar_tac

/-- Source bytes pay for the dispatch and two words per arm. This bound holds
for every permitted usize width and does not assume a 64-bit target. -/
theorem table_instruction_room {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {data : Slice U8} {start finish : Usize} {depths : List U32} {fallback : U32} {position : Nat}
    (budget : SourceCodeBudget compiler position) (consumed : position < start.val)
    (decoded : BrTable.Decoded data start depths fallback finish)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val) :
    compiler.function.code.val.length+1+2*(depths.length+1) ≤ Usize.max := by
  obtain ⟨count,first,last,countDecoded,_,labels,defaultDecoded⟩ := decoded
  have countSpan := countDecoded.span
  have labelSpan := table_labels_length_span labels
  have defaultSpan := defaultDecoded.span
  change compiler.function.code.val.length ≤ 3*position at budget
  have paid : compiler.function.code.val.length+1+2*(depths.length+1) ≤ 3*data.length := by omega
  exact paid.trans ((Nat.mul_le_mul_left 3 sourceBound).trans table_source_word_room)

end Itasca.Runtime.Code
