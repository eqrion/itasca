import Exec.Abs.Float.Descriptor
import Exec.Spec.FloatTrunc
import Exec.Abs.Typing

namespace Exec.Abs.Float
open SpecExt SpecExt.Builtins SpecExt.Builtins.Float

theorem Instruction.source_wf (op : Instruction) : wf_instr op.source := by
  cases op with
  | unary ty op => exact .instr_case_14 _ _ (.unop__case_1 _ _ _ rfl)
  | binary ty op => exact .instr_case_15 _ _ (.binop__case_1 _ _ _ rfl)
  | compare ty op => exact .instr_case_17 _ _ (.relop__case_1 _ _ _ rfl)
  | convert source target sign =>
    apply wf_instr.instr_case_18
    · exact .cvtop___case_1 _ _ _ _ _ (.cvtop__Inn_1_Fnn_2_case_0 _ _ _) rfl rfl
    · cases source <;> cases target <;> decide
  | truncate source target sign saturating =>
    apply wf_instr.instr_case_18
    · apply wf_cvtop__.cvtop___case_2
      · cases saturating
        · exact .cvtop__Fnn_1_Inn_2_case_0 _ _ _
        · exact .cvtop__Fnn_1_Inn_2_case_1 _ _ _
      · rfl
      · rfl
    · cases source <;> cases target <;> decide
  | reinterpretFloat source =>
    cases source
    all_goals exact .instr_case_18 _ _ _ (.cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_2 _ _ (by decide)) rfl rfl) (by decide)
  | reinterpretInt source =>
    cases source
    all_goals exact .instr_case_18 _ _ _ (.cvtop___case_1 _ _ _ _ _ (.cvtop__Inn_1_Fnn_2_case_1 _ _ (by decide)) rfl rfl) (by decide)
  | promote => exact .instr_case_18 _ _ _ (.cvtop___case_3 _ _ _ _ _ (.cvtop__Fnn_1_Fnn_2_case_0 _ _ (by decide)) rfl rfl) (by decide)
  | demote => exact .instr_case_18 _ _ _ (.cvtop___case_3 _ _ _ _ _ (.cvtop__Fnn_1_Fnn_2_case_1 _ _ (by decide)) rfl rfl) (by decide)

theorem numberOfBits_wf (ty : numtype) (bits : Nat) (bound : bits < 2^sizenn ty) :
    wf_num_ ty (numberOfBits ty bits) := by
  cases ty
  · exact Exec.Spec.unsigned_num_wf .I32 bits bound
  · exact Exec.Spec.unsigned_num_wf .I64 bits bound
  · exact Exec.Spec.float_num_wf .F32 _ (floatOfBits_wf 32 (by omega) _)
  · exact Exec.Spec.float_num_wf .F64 _ (floatOfBits_wf 64 (by omega) _)

theorem Instruction.operands_wf (op : Instruction) (a b : Nat)
    (first : a < 2^sizenn op.input) (second : b < 2^sizenn op.input) :
    Forall wf_val (op.operands a b) := by
  unfold operands
  split
  · intro value member
    simp only [List.mem_singleton] at member
    subst value
    exact .val_case_0 _ _ (numberOfBits_wf _ _ first)
  · intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .val_case_0 _ _ (numberOfBits_wf _ _ first)
    · exact .val_case_0 _ _ (numberOfBits_wf _ _ second)

def Instruction.signature (op : Instruction) : functype :=
  .mk_functype (.mk_list (List.replicate op.arity (valtype_numtype op.input))) (.mk_list [valtype_numtype op.output])

theorem numberOfBits_typed (s : store) (storeWf : wf_store s) (ty : numtype) (bits : Nat)
    (bound : bits < 2^sizenn ty) :
    Val_ok s (.CONST ty (numberOfBits ty bits)) (valtype_numtype ty) :=
  .numtype _ _ _ storeWf (.val_case_0 _ _ (numberOfBits_wf ty bits bound))

end Exec.Abs.Float
