import Exec.Abs.Float.Results
import Exec.Abs.Sim.Typed
namespace Exec.Abs.Float
open SpecExt Exec.Spec SpecExt.Builtins SpecExt.Builtins.Float

theorem number_encoding (ty : numtype) (number : num_) (valid : wf_num_ ty number) :
    ∃ bits, number = numberOfBits ty bits ∧ bits < 2^sizenn ty := by
  cases valid with
  | num__case_0 ity value _ bounded same =>
    subst ty
    cases value with
    | mk_uN bits =>
      refine ⟨bits, (numberOfBits_integer ity bits).symm, ?_⟩
      cases bounded with
      | uN_case_0 _ limit =>
        cases ity <;> norm_num [sizenn, numtype_Inn, valtype_numtype, valtype_Inn, size] at limit ⊢ <;> omega
  | num__case_1 fty value valid same =>
    subst ty
    obtain ⟨bits, bound, encoding⟩ := float_encoding fty value valid
    refine ⟨bits, ?_, bound⟩
    rw [numberOfBits_float, encoding]

theorem numeric_val_encoding {s : store} {ty : numtype} {value : val}
    (typed : Val_ok s value (valtype_numtype ty)) :
    ∃ bits, value = .CONST ty (numberOfBits ty bits) ∧ bits < 2^sizenn ty := by
  have valid := val_ok_wf typed
  have typeEq := value_type_of_typed typed
  cases valid with
  | val_case_0 nt number valid =>
    have same : nt = ty := by cases nt <;> cases ty <;> simp_all [valueType, valtype_numtype]
    subst nt
    obtain ⟨bits, rfl, bound⟩ := number_encoding ty number valid
    exact ⟨bits, rfl, bound⟩
  | val_case_1 vt bits _ => cases ty <;> simp_all [valueType, valtype_numtype]
  | val_case_2 rt => cases ty <;> cases rt <;> simp_all [valueType, valtype_numtype, valtype_reftype]
  | val_case_3 address => cases ty <;> simp_all [valueType, valtype_numtype]
  | val_case_4 address => cases ty <;> simp_all [valueType, valtype_numtype]

theorem Instruction.typed_operands (op : Instruction) {s : store} {f : AFrame}
    {after : List instr} (typed : FrameTyped s { f with code := op.source :: after } []) :
    ∃ front a b, f.vals = front ++ op.operands a b ∧ a < 2^sizenn op.input ∧ b < 2^sizenn op.input ∧
      Forall wf_val front ∧ (∀ label ∈ f.labels, label.height ≤ front.length) := by
  obtain ⟨C, front, operands, ins, outs, _, _, step, split, typedOperands, frontWf, heights⟩ := frame_typed_operands_bounds typed
  cases op <;> cases step
  all_goals first
    | cases typedOperands with
      | cons first rest =>
        cases rest with
        | cons second last =>
          cases last
          obtain ⟨a, rfl, firstBound⟩ := numeric_val_encoding first
          obtain ⟨b, rfl, secondBound⟩ := numeric_val_encoding second
          refine ⟨front, a, b, ?_, firstBound, secondBound, frontWf, heights⟩
          simpa [Instruction.operands, Instruction.arity, Instruction.input] using split
    | cases typedOperands with
      | cons first rest =>
        cases rest
        obtain ⟨a, rfl, firstBound⟩ := numeric_val_encoding first
        refine ⟨front, a, a, ?_, firstBound, firstBound, frontWf, heights⟩
        simpa [Instruction.operands, Instruction.arity, Instruction.input] using split

end Exec.Abs.Float
