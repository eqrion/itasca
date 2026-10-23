import Exec.Spec.Typing.SupportedReadPreservation
import Exec.Spec.Typing.CallReadTyping
import Exec.Spec.Typing.FunctionEntryTyping

/-! Configuration preservation for reads, block/loop entry, direct/indirect
dispatch, and defined-function entry. Bulk-operation expansion is separate. -/

namespace Exec.Spec
open SpecExt

def ControlReadInstruction (instruction : admininstr) : Prop :=
  SupportedReadInstruction instruction ∨
    match instruction with
    | .BLOCK _ _ | .LOOP _ _ | .CALL _ | .CALL_INDIRECT _ _ | .CALL_ADDR _ => True
    | _ => False

def ControlReadCode (code : List admininstr) : Prop :=
  ∃ instruction, code.getLast?=some instruction ∧ ControlReadInstruction instruction

private theorem getElem?_of_bangEq {A : Type} [Inhabited A] {xs : List A} {index : Nat} {value : A}
    (bound : index<xs.length) (same : xs[index]! = value) : xs[index]?=some value := by
  simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem bound,Option.getD_some] using congrArg some same

set_option maxHeartbeats 3200000 in
theorem control_read_typing_preserved {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) (components : SourceStoreComponents s)
    {before after : List admininstr} {input output : List valtype}
    (source : Step_read ⟨⟨s,frame⟩,before⟩ after) (scope : ControlReadCode before)
    (typed : Instrs_ok2 s context before (.mk_functype (.mk_list input) (.mk_list output))) :
    Instrs_ok2 s context after (.mk_functype (.mk_list input) (.mk_list output)) := by
  have original := source
  cases source
  all_goals try exact trap_typing_replacement _ _ context input output typed
  all_goals try {
    apply supported_read_typing_preserved environment components original ?_ typed
    simp [SupportedReadCode,SupportedReadInstruction,readInstructionSignature] }
  all_goals try { simp [ControlReadCode,ControlReadInstruction,SupportedReadInstruction,readInstructionSignature] at scope }
  case block =>
    rename_i k values block body arity params results _ _ _ _ _ _
    have expanded : fun_blocktype ⟨s,frame⟩ block=.mk_functype (.mk_list params) (.mk_list results) := by assumption
    have resultCount : arity=results.length := by assumption
    simpa only [Map,vals] using block_read_typing_preserved environment values block body arity params results
      expanded (by omega) resultCount typed
  case loop =>
    rename_i k values block body params arity results _ _ _ _ _ _
    have expanded : fun_blocktype ⟨s,frame⟩ block=.mk_functype (.mk_list params) (.mk_list results) := by assumption
    have branchCount : k=params.length := by assumption
    simpa only [Map,vals] using loop_read_typing_preserved environment values block body k params results
      expanded (by omega) branchCount typed
  case call => simpa only [fun_funcaddr] using call_read_typing_preserved environment _ typed
  case call_indirect_call =>
    apply indirect_call_read_typing_preserved environment _ _ _ _ typed <;> assumption
  case call_addr =>
    subst_vars
    apply function_entry_read_typing_preserved components (typed := typed)
    all_goals first
      | assumption
      | omega
      | rfl
      | (apply getElem?_of_bangEq <;> assumption)

end Exec.Spec
