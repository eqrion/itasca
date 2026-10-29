import Itasca.Runtime.SourceMachine.Safety
import Itasca.Runtime.SourceMachine.Numeric.Semantics

namespace Itasca.Runtime.Abs.Numeric
open SpecExt Itasca.Runtime.Spec

theorem word_bound (ty : Inn) (bits : BitVec (sizenn (numtype_Inn ty))) :
    bits.toNat < 2 ^ integerWidth ty := by cases ty <;> exact bits.isLt

theorem Instruction.arity_cases (op : Instruction) : op.arity = 1 ∨ op.arity = 2 := by
  cases op <;> simp [arity]

def Instruction.operands (op : Instruction)
    (a b : BitVec (sizenn (numtype_Inn op.input))) : List val :=
  if op.arity = 1 then [integerVal op.input a.toNat]
  else [integerVal op.input a.toNat, integerVal op.input b.toNat]

 theorem word_exists (ty : Inn) (bits : Nat) (bound : bits < 2^integerWidth ty) :
    ∃ word : BitVec (sizenn (numtype_Inn ty)), word.toNat = bits := by
  refine ⟨BitVec.ofNat _ bits, ?_⟩
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  cases ty <;> simpa [integerWidth, numtype_Inn, sizenn, size, valtype_numtype] using bound

 theorem Instruction.typed_operands (op : Instruction) {s : store} {f : AFrame}
    {after : List instr} (typed : FrameTyped s { f with code := op.source :: after } []) :
    ∃ front a b, f.vals = front ++ op.operands a b := by
  obtain ⟨C, first, operands, ins, outs, _, _, hop, hsplit, hoperands⟩ := frame_typed_operands typed
  cases op <;> cases hop
  all_goals
    first
    | cases hoperands with
      | cons hl hr =>
        cases hr with
        | cons hr hend =>
          cases hend
          obtain ⟨a, rfl, ha⟩ := integer_val_inv hl
          obtain ⟨b, rfl, hb⟩ := integer_val_inv hr
          obtain ⟨wa, hwa⟩ := word_exists _ a ha
          obtain ⟨wb, hwb⟩ := word_exists _ b hb
          exact ⟨first, wa, wb, by simpa [Instruction.operands, Instruction.arity, Instruction.input, hwa, hwb] using hsplit⟩
    | cases hoperands with
      | cons hv hend =>
        cases hend
        obtain ⟨a, rfl, ha⟩ := integer_val_inv hv
        obtain ⟨wa, hwa⟩ := word_exists _ a ha
        exact ⟨first, wa, wa, by simpa [Instruction.operands, Instruction.arity, Instruction.input, hwa] using hsplit⟩


end Itasca.Runtime.Abs.Numeric
