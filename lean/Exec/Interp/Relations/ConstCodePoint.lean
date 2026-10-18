import Exec.Abs.Numeric.Decode
import Exec.Interp.Relations.Const

namespace Exec.Interp
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

theorem linearPoint_const32 {raw : runtime.interp.Frame} {f : Abs.AFrame}
    {compiled : runtime.bytecode.CompiledFunction} {next : Nat} {output : List valtype}
    (value : U32) (after : List instr)
    (point : LinearPoint raw { f with
      code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after } compiled next output) :
    ∃ dst,
      dst.val = Code.slots ((f.locals ++ f.vals).map Code.valueType) ∧
      compiled.code.val[raw.pc.val]? = some (.Const32 dst value) ∧
      Code.LinearCodeRel (f.locals.map Code.valueType)
        ((f.vals ++ [Abs.integerVal .I32 value.val]).map Code.valueType)
        after compiled.code.val (raw.pc.val + 1) next output := by
  obtain ⟨middle, emitted, head, fetch, tail⟩ := linearCodeRel_head point
  obtain ⟨dst, emittedEq, afterEq, destination⟩ := linearEmission_const32_inv value head
  refine ⟨dst, ?_, fetch _ [] emittedEq, ?_⟩
  · simpa only [List.map_append, Code.slots_append] using destination
  · simpa only [emittedEq, afterEq, List.length_singleton, List.map_append, List.map_cons, List.map_nil,
      Abs.integerVal, Code.valueType, numtype_Inn, valtype_numtype] using tail

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

theorem linearPoint_const64 {raw : runtime.interp.Frame} {f : Abs.AFrame}
    {compiled : runtime.bytecode.CompiledFunction} {next : Nat} {output : List valtype}
    (value : U64) (after : List instr)
    (point : LinearPoint raw { f with
      code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after } compiled next output) :
    ∃ dst,
      dst.val = Code.slots ((f.locals ++ f.vals).map Code.valueType) ∧
      compiled.code.val[raw.pc.val]? = some (.Const64 dst value) ∧
      Code.LinearCodeRel (f.locals.map Code.valueType)
        ((f.vals ++ [Abs.integerVal .I64 value.val]).map Code.valueType)
        after compiled.code.val (raw.pc.val + 1) next output := by
  obtain ⟨middle, emitted, head, fetch, tail⟩ := linearCodeRel_head point
  obtain ⟨dst, emittedEq, afterEq, destination⟩ := linearEmission_const64_inv value head
  refine ⟨dst, ?_, fetch _ [] emittedEq, ?_⟩
  · simpa only [List.map_append, Code.slots_append] using destination
  · simpa only [emittedEq, afterEq, List.length_singleton, List.map_append, List.map_cons, List.map_nil,
      Abs.integerVal, Code.valueType, numtype_Inn, valtype_numtype] using tail

end Exec.Interp
