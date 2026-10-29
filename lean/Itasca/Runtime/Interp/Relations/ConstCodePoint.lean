import Itasca.Runtime.SourceMachine.Numeric.Decode
import Itasca.Runtime.Interp.Relations.Execute
import Itasca.Runtime.Interp.Relations.Regions
import Itasca.Runtime.SourceMachine.Sim.Instruction

namespace Itasca.Runtime.Interp
open Aeneas.Std

theorem linearEmission_const32_inv {locals before after : List valtype} {emitted : List Code.Bytecode}
    (value : U32)
    (h : Code.LinearEmission locals before
      (.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))) emitted after) :
    ∃ dst,
      emitted = [.Const32 dst value] ∧ after = before ++ [.I32] ∧
      dst.val = Code.slots locals + Code.slots before := by
  generalize equality : instr.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) = instruction at h
  cases h with
  | const32 stack dst word position =>
    simp only [instr.CONST.injEq, num_.mk_num__0.injEq, uN.mk_uN.injEq, and_self_left] at equality
    have same : word = value := by scalar_tac
    subst word
    exact ⟨dst, rfl, rfl, position⟩
  | binary stack ity op left right hl hr => cases op <;> simp_all [Code.IntegerBinary.source]
  | numeric stack op a b ha hb =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    simp [Abs.Numeric.decodeInstruction_source, Abs.Numeric.decodeInstruction] at decoded
  | _ => simp_all

theorem linearEmission_const64_inv {locals before after : List valtype} {emitted : List Code.Bytecode}
    (value : U64)
    (h : Code.LinearEmission locals before
      (.CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val))) emitted after) :
    ∃ dst,
      emitted = [.Const64 dst value] ∧ after = before ++ [.I64] ∧
      dst.val = Code.slots locals + Code.slots before := by
  generalize equality : instr.CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) = instruction at h
  cases h with
  | const64 stack dst word position =>
    simp only [instr.CONST.injEq, num_.mk_num__0.injEq, uN.mk_uN.injEq, and_self_left] at equality
    have same : word = value := by scalar_tac
    subst word
    exact ⟨dst, rfl, rfl, position⟩
  | binary stack ity op left right hl hr => cases op <;> simp_all [Code.IntegerBinary.source]
  | numeric stack op a b ha hb =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    simp [Abs.Numeric.decodeInstruction_source, Abs.Numeric.decodeInstruction] at decoded
  | _ => simp_all

end Itasca.Runtime.Interp
