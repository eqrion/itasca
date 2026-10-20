import Exec.Spec.Typing.TypingReplacement

/-! Lift generated source instruction typing to administrative typing. -/

namespace Exec.Spec

theorem source_instrs_administrative {s : store} (storeWf : wf_store s) {context : _root_.context}
    {code : List instr} {type : functype} (typed : Instrs_ok context code type) :
    Instrs_ok2 s context (code.map admininstr_instr) type := by
  induction typed using Instrs_ok.rec (motive_1 := fun _ _ _ _ => True)
  all_goals try trivial
  case empty => apply Instrs_ok2.empty <;> assumption
  case instr =>
    apply Instrs_ok2.instr
    · apply Instr_ok2.plain <;> assumption
    · exact storeWf
    · assumption
    · apply wf_admininstr_instr
      assumption
  case seq =>
    simp only [List.map_append]
    apply instrs_sequence <;> assumption
  case sub => apply instrs_subtype <;> assumption
  case frame => (apply instrs_frame; assumption)
end Exec.Spec
