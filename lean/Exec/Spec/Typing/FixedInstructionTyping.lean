import Exec.Spec.Typing.TypingReplacement
import Exec.Spec.PureWf

/-! Fixed scalar/SIMD signatures and semantic typing preservation of their
generated pure reductions, including trap outcomes. -/

namespace Exec.Spec
open SpecExt

def fixedInstructionSignature : admininstr → Option (List valtype × List valtype)
  | .NOP => some ([],[])
  | .UNOP nt _ => some ([valtype_numtype nt],[valtype_numtype nt])
  | .BINOP nt _ => some ([valtype_numtype nt,valtype_numtype nt],[valtype_numtype nt])
  | .TESTOP nt _ => some ([valtype_numtype nt],[.I32])
  | .RELOP nt _ => some ([valtype_numtype nt,valtype_numtype nt],[.I32])
  | .CVTOP target source _ => some ([valtype_numtype source],[valtype_numtype target])
  | .EXTEND nt _ => some ([valtype_numtype nt],[valtype_numtype nt])
  | .VVUNOP _ _ | .VUNOP _ _ | .VEXTUNOP _ _ _ | .VCVTOP _ _ _ => some ([.V128],[.V128])
  | .VVBINOP _ _ | .VBINOP _ _ | .VRELOP _ _ | .VSWIZZLE _ | .VSHUFFLE _ _
    | .VEXTBINOP _ _ _ | .VNARROW _ _ _ => some ([.V128,.V128],[.V128])
  | .VVTERNOP _ _ => some ([.V128,.V128,.V128],[.V128])
  | .VVTESTOP _ _ | .VTESTOP _ _ | .VBITMASK _ => some ([.V128],[.I32])
  | .VSHIFTOP _ _ => some ([.V128,.I32],[.V128])
  | .VSPLAT shape => some ([valtype_numtype (shunpack shape)],[.V128])
  | .VEXTRACT_LANE shape _ _ => some ([.V128],[valtype_numtype (shunpack shape)])
  | .VREPLACE_LANE shape _ => some ([.V128,valtype_numtype (shunpack shape)],[.V128])
  | _ => none

set_option maxHeartbeats 1600000 in
theorem fixed_instruction_typing {s : store} {context : _root_.context} {instruction : admininstr}
    {input output params results : List valtype}
    (typed : Instr_ok2 s context instruction (.mk_functype (.mk_list input) (.mk_list output)))
    (signature : fixedInstructionSignature instruction = some (params,results)) : input=params ∧ output=results := by
  cases typed
  case plain =>
    rename_i source _ _ _ primitive
    cases primitive <;> simp_all [fixedInstructionSignature,admininstr_instr] <;> aesop
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref,fixedInstructionSignature] at signature
  all_goals simp [fixedInstructionSignature] at signature

theorem resulttype_sub_prefix {left right xs ys : List valtype}
    (sub : Resulttype_sub (.mk_list (left++xs)) (.mk_list (right++ys)))
    (suffixCount : xs.length=ys.length) : Resulttype_sub (.mk_list left) (.mk_list right) := by
  have relation := resulttype_sub_iff.mp sub
  have count : left.length=right.length := by
    have same := relation.length_eq
    simp only [List.length_append] at same
    omega
  have selected := List.forall₂_take left.length relation
  apply resulttype_sub_iff.mpr
  simp only [List.take_append,List.take_length,Nat.sub_self,List.take_zero,List.append_nil] at selected
  simpa only [count,List.take_length,Nat.sub_self,List.take_zero,List.append_nil] using selected

theorem fixed_value_operation_preserved {s : store} {args returned : List val} {op : admininstr}
    {params results : List valtype}
    (signature : fixedInstructionSignature op=some (params,results))
    (arity : args.length=params.length) (storeWf : wf_store s)
    (values : ResultsTyped s results returned) :
    TypedReplacement s s (vals args++[op]) (vals returned) := by
  intro context input output typed
  obtain ⟨base,types,inputBase,argsTyped,called⟩ := value_prefix_typing typed
  obtain ⟨callBase,callInput,callOutput,primitive,callSub,outputSub⟩ := instruction_typing_effect called op rfl
  obtain ⟨rfl,rfl⟩ := fixed_instruction_typing primitive signature
  have count : types.length=callInput.length := by have same := argsTyped.length_eq; omega
  have bases := resulttype_sub_prefix callSub count
  have inputSub := resulttype_sub_trans inputBase bases
  have contextWf := (instrs_ok2_wf typed).2.1
  have returnedTyped := instrs_frame (values_instrs_ok storeWf contextWf values) callBase
  simp only [List.append_nil] at returnedTyped
  exact instrs_subtype returnedTyped inputSub outputSub

theorem trap_typing_replacement (s : store) (before : List admininstr) :
    TypedReplacement s s before [.TRAP] := by
  intro context input output typed
  have wf := instrs_ok2_wf typed
  exact .instr _ _ _ _ _ (.trap _ _ _ _ wf.1 wf.2.1 .admininstr_case_73)
    wf.1 wf.2.1 (by constructor)

private theorem shunpack_numeric (nt : numtype) (count : Nat) :
    shunpack (.X (lanetype_numtype nt) (.mk_dim count)) = nt := by
  cases nt <;> rfl

private theorem shunpack_packed (pt : packtype) (count : Nat) :
    shunpack (.X (lanetype_packtype pt) (.mk_dim count)) = .I32 := by
  cases pt <;> rfl

set_option maxHeartbeats 2400000 in
theorem fixed_pure_step_preserves {s : store} {before after : List admininstr}
    (storeWf : wf_store s) (source : Step_pure before after)
    (fixed : before.getLast?.bind fixedInstructionSignature ≠ none) :
    TypedReplacement s s before after := by
  cases source
  all_goals try exact trap_typing_replacement _ _
  all_goals try { exfalso; apply fixed; rfl }
  all_goals first
    | change TypedReplacement s s (vals []++[_]) (vals [])
    | change TypedReplacement s s (vals [.CONST _ _]++[_]) (vals [.CONST _ _])
    | change TypedReplacement s s (vals [.CONST _ _,.CONST _ _]++[_]) (vals [.CONST _ _])
    | change TypedReplacement s s (vals [.VCONST _ _]++[_]) (vals [.VCONST _ _])
    | change TypedReplacement s s (vals [.VCONST _ _,.VCONST _ _]++[_]) (vals [.VCONST _ _])
    | change TypedReplacement s s (vals [.VCONST _ _,.VCONST _ _,.VCONST _ _]++[_]) (vals [.VCONST _ _])
    | change TypedReplacement s s (vals [.VCONST _ _]++[_]) (vals [.CONST _ _])
    | change TypedReplacement s s (vals [.VCONST _ _,.VCONST _ _]++[_]) (vals [.CONST _ _])
    | change TypedReplacement s s (vals [.VCONST _ _,.CONST _ _]++[_]) (vals [.VCONST _ _])
    | change TypedReplacement s s (vals [.CONST _ _]++[_]) (vals [.VCONST _ _])
  all_goals apply fixed_value_operation_preserved (storeWf := storeWf)
  all_goals try rfl
  all_goals first
    | exact .nil
    | (apply List.Forall₂.cons; swap; exact .nil)
  all_goals try simp only [shunpack_numeric,shunpack_packed]
  all_goals first
    | (apply Val_ok.numtype; exact storeWf; apply val_wf_of_admin; assumption)
    | (apply Val_ok.vectype; exact storeWf; apply val_wf_of_admin; assumption)

end Exec.Spec
