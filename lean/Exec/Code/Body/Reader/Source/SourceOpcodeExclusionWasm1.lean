import Exec.Code.Body.Reader.Source.SourceOpcodeFamilies
import Exec.Code.Body.Reader.Acceptance.ReaderProfileAcceptanceWasm1

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Wasm 1 rejects every reserved byte and every later-profile numeric or
prefix extension in the actual extracted dispatcher. -/
theorem source_opcode_rejected_wasm1 {V : Type} (source : code.OpVisitor V)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (opcode : U8) (before after : V)
    (absent : (6 ≤ opcode.val ∧ opcode.val ≤ 10) ∨ (18 ≤ opcode.val ∧ opcode.val ≤ 25) ∨
      (28 ≤ opcode.val ∧ opcode.val ≤ 31) ∨ (37 ≤ opcode.val ∧ opcode.val ≤ 39) ∨ 192 ≤ opcode.val)
    (reference : code.step_profile source st data env ctx index .Wasm1 opcode before = .ok (.Ok (),out,after)) : False := by
  have raw := profile_raw_success_wasm1 source st out data env ctx index opcode before after reference
  by_cases high : 192 ≤ opcode.val
  · have absentMeaning : Numeric.opcodeMeaning opcode = none := by
      cases meaning : Numeric.opcodeMeaning opcode with
      | none => rfl
      | some operation =>
        have bounded := Numeric.NumericOp.bounds meaning
        omega
    rw [code.step.numeric_dispatch source st.core data env ctx opcode before (by omega),
      code.step_numeric.unrecognized source st.core opcode before absentMeaning] at raw
    simp at raw
  · rw [code.step.reserved source st.core data env ctx opcode before (by tauto)] at raw
    simp at raw

end Exec.Code
