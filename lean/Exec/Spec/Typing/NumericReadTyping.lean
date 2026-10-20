import Exec.Spec.Typing.ValueOperationTyping

/-! Semantic typing preservation for scalar/SIMD loads and memory/table sizes.
Generated well-formed output premises supply the actual numeric values. -/

namespace Exec.Spec
open SpecExt

def readInstructionSignature : admininstr → Option (List valtype × List valtype)
  | .LOAD nt _ _ => some ([.I32],[valtype_numtype nt])
  | .VLOAD _ _ _ => some ([.I32],[.V128])
  | .VLOAD_LANE _ _ _ _ => some ([.I32,.V128],[.V128])
  | .MEMORY_SIZE | .TABLE_SIZE _ => some ([],[.I32])
  | _ => none

private theorem integer_valtype_coercion (type : Inn) :
    valtype_Inn type=valtype_numtype (numtype_Inn type) := by
  cases type <;> rfl

set_option maxHeartbeats 1600000 in
theorem read_instruction_typing {s : store} {context : _root_.context} {instruction : admininstr}
    {input output params results : List valtype}
    (typed : Instr_ok2 s context instruction (.mk_functype (.mk_list input) (.mk_list output)))
    (signature : readInstructionSignature instruction=some (params,results)) : input=params ∧ output=results := by
  cases typed
  case plain =>
    rename_i source _ _ _ primitive
    cases primitive <;> simp_all [readInstructionSignature,admininstr_instr]
    all_goals aesop (add safe apply [integer_valtype_coercion])
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref,readInstructionSignature] at signature
  all_goals simp [readInstructionSignature] at signature

theorem numeric_read_values_preserved {s : store} {args returned : List val} {op : admininstr}
    {params results : List valtype} (storeWf : wf_store s)
    (signature : readInstructionSignature op=some (params,results))
    (arity : args.length=params.length) (values : ResultsTyped s results returned) :
    TypedReplacement s s (vals args++[op]) (vals returned) := by
  apply value_operation_preserved
  intro context input output typed
  have contextWf : wf_context context := by
    generalize same : op=instruction at typed
    cases typed <;> assumption
  obtain ⟨rfl,rfl⟩ := read_instruction_typing typed signature
  exact ⟨arity.symm,fun _ => values_instrs_ok storeWf contextWf values⟩

def configurationInstructions : config → List admininstr
  | ⟨_,code⟩ => code

set_option maxHeartbeats 2400000 in
theorem numeric_read_typing_preserved {s : store} {before : config} {after : List admininstr}
    (storeWf : wf_store s) (source : Step_read before after)
    (scope : (configurationInstructions before).getLast?.bind readInstructionSignature ≠ none) :
    TypedReplacement s s (configurationInstructions before) after := by
  cases source
  all_goals try exact trap_typing_replacement _ _
  all_goals try { exfalso; apply scope; simp [configurationInstructions,readInstructionSignature] }
  all_goals first
    | change TypedReplacement s s (vals []++[_]) (vals [.CONST _ _])
    | change TypedReplacement s s (vals [.CONST _ _]++[_]) (vals [.CONST _ _])
    | change TypedReplacement s s (vals [.CONST _ _]++[_]) (vals [.VCONST _ _])
    | change TypedReplacement s s (vals [.CONST _ _,.VCONST _ _]++[_]) (vals [.VCONST _ _])
  all_goals apply numeric_read_values_preserved (storeWf := storeWf)
  all_goals try rfl
  all_goals apply List.Forall₂.cons
  all_goals first
    | exact .nil
    | (apply Val_ok.numtype; exact storeWf; apply val_wf_of_admin; assumption)
    | (apply Val_ok.vectype; exact storeWf; apply val_wf_of_admin; assumption)

end Exec.Spec
