import Exec.Code.Local.Source.SourceBudget
import Itasca.Binary.Wasm1.Encoding
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem leb_encoding_nonempty {bytes value} (encoded : Leb128.Encoding bytes value) :
    0 < bytes.length := by
  obtain ⟨front, last, rfl, _⟩ := encoded
  simp

theorem indices_encoding_length {indices bytes} (encoded : Wasm1.IndicesEncoding indices bytes) :
    indices.length ≤ bytes.length := by
  induction encoded with
  | nil => simp
  | cons first rest ih =>
    have nonempty := leb_encoding_nonempty first
    simp only [List.length_cons, List.length_append]
    omega

/-- Actual branch-table immediate bytes pay for every indexed target and default. -/
theorem branch_table_source_budget {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {data : Slice U8} {start pos finish : Usize} {indices : List U32} {default : U32}
    {count entries final : List U8}
    (budget : SourceCodeBudget before start.val)
    (opcode : pos.val = start.val + 1)
    (countBytes : Leb128.Encoding count indices.length)
    (entryBytes : Wasm1.IndicesEncoding indices entries)
    (defaultBytes : Leb128.Encoding final default.val)
    (span : Wasm1.BytesAt data pos (count ++ entries ++ final) finish)
    (growth : after.function.code.val.length ≤ before.function.code.val.length + 1 + 2 * (indices.length + 1)) :
    SourceCodeBudget after finish.val := by
  apply budget.table growth
  have countLength := leb_encoding_nonempty countBytes
  have entryLength := indices_encoding_length entryBytes
  have defaultLength := leb_encoding_nonempty defaultBytes
  have length := span.length
  simp only [List.length_append] at length
  omega
end Exec.Code
