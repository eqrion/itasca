import Exec.Interp.Core.Point
import Exec.Abs.Numeric.Decode
namespace Exec.Interp.FloatConstant
open Aeneas Aeneas.Std SpecExt

theorem linearEmission_not_float {locals before after emitted} (ty : Fnn) (value : fN)
    (emission : Code.LinearEmission locals before (.CONST (numtype_Fnn ty) (.mk_num__1 ty value)) emitted after) : False := by
  generalize equality : instr.CONST (numtype_Fnn ty) (.mk_num__1 ty value) = instruction at emission
  cases emission with
  | binary stack type op a b left right => cases op <;> simp [Code.IntegerBinary.source] at equality
  | numeric stack op a b left right =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    cases ty <;> simp [Abs.Numeric.decodeInstruction,numtype_Fnn] at decoded
  | _ => cases ty <;> cases equality

theorem coreEmission_float32_inv {C before after emitted} (value : fN)
    (emission : Code.CoreEmission C before (.CONST .F32 (.mk_num__1 .F32 value)) emitted after) :
    ∃ dst bits, emitted = [.Const32 dst bits] ∧ after = before ++ [.F32] ∧
      value = Builtins.floatOfBits 32 bits.val ∧ dst.val = Code.slots C.LOCALS + Code.slots before := by
  generalize equality : instr.CONST .F32 (.mk_num__1 .F32 value) = instruction at emission
  cases emission with
  | pure pure =>
    rw [←equality] at pure
    exact False.elim (linearEmission_not_float .F32 value pure)
  | float32 stack dst bits slot =>
    cases equality
    exact ⟨dst,bits,rfl,rfl,rfl,slot⟩
  | load => simp [Abs.Memory.Load.source] at equality
  | store => simp [Abs.Memory.Store.source] at equality
  | _ => cases equality

theorem corePoint_float32_head {C returns code labels stack pc next output}
    (value : fN) (after : List instr)
    (point : Code.StructuredCode.Point (Code.CoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels stack
      (.CONST .F32 (.mk_num__1 .F32 value) :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode.Point (Code.CoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels stack
        (.CONST .F32 (.mk_num__1 .F32 value) :: after) target.val next output) ∨
    (∃ dst bits, value = Builtins.floatOfBits 32 bits.val ∧
      dst.val = Code.slots C.LOCALS + Code.slots stack ∧ code[pc]? = some (.Const32 dst bits) ∧
      Code.StructuredCode.Point (Code.CoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels
        (stack ++ [.F32]) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.CONST .F32 (.mk_num__1 .F32 value) :: after = source at relation
  cases relation with
  | linear head fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨dst,bits,emitted,result,valueEq,position⟩ := coreEmission_float32_inv value head
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨dst,bits,rfl,position,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => cases sourceEq

theorem coreEmission_float64_inv {C before after emitted} (value : fN)
    (emission : Code.CoreEmission C before (.CONST .F64 (.mk_num__1 .F64 value)) emitted after) :
    ∃ dst bits, emitted = [.Const64 dst bits] ∧ after = before ++ [.F64] ∧
      value = Builtins.floatOfBits 64 bits.val ∧ dst.val = Code.slots C.LOCALS + Code.slots before := by
  generalize equality : instr.CONST .F64 (.mk_num__1 .F64 value) = instruction at emission
  cases emission with
  | pure pure =>
    rw [←equality] at pure
    exact False.elim (linearEmission_not_float .F64 value pure)
  | float64 stack dst bits slot =>
    cases equality
    exact ⟨dst,bits,rfl,rfl,rfl,slot⟩
  | load => simp [Abs.Memory.Load.source] at equality
  | store => simp [Abs.Memory.Store.source] at equality
  | _ => cases equality

theorem corePoint_float64_head {C returns code labels stack pc next output}
    (value : fN) (after : List instr)
    (point : Code.StructuredCode.Point (Code.CoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels stack
      (.CONST .F64 (.mk_num__1 .F64 value) :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode.Point (Code.CoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels stack
        (.CONST .F64 (.mk_num__1 .F64 value) :: after) target.val next output) ∨
    (∃ dst bits, value = Builtins.floatOfBits 64 bits.val ∧
      dst.val = Code.slots C.LOCALS + Code.slots stack ∧ code[pc]? = some (.Const64 dst bits) ∧
      Code.StructuredCode.Point (Code.CoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels
        (stack ++ [.F64]) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.CONST .F64 (.mk_num__1 .F64 value) :: after = source at relation
  cases relation with
  | linear head fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨dst,bits,emitted,result,valueEq,position⟩ := coreEmission_float64_inv value head
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨dst,bits,rfl,position,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => cases sourceEq

end Exec.Interp.FloatConstant
