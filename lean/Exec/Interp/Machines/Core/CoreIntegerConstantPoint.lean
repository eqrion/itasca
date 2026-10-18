import Exec.Interp.Core.Point
import Exec.Interp.Relations.ConstCodePoint
namespace Exec.Interp.IntegerConstant
open Aeneas Aeneas.Std SpecExt

theorem coreEmission_integer32_inv {C before after emitted} (value : U32)
    (emission : Code.CoreEmission C before (.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))) emitted after) :
    ∃ dst bits, emitted = [.Const32 dst bits] ∧ after = before ++ [.I32] ∧
      value = bits ∧ dst.val = Code.slots C.LOCALS + Code.slots before := by
  generalize equality : instr.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) = instruction at emission
  cases emission with
  | pure pure =>
    rw [←equality] at pure
    obtain ⟨dst,emitted,result,position⟩ := linearEmission_const32_inv value pure
    exact ⟨dst,value,emitted,result,rfl,position⟩
  | load => simp [Abs.Memory.Load.source] at equality
  | store => simp [Abs.Memory.Store.source] at equality
  | _ => cases equality

theorem corePoint_integer32_head {C returns code labels stack pc next output}
    (value : U32) (after : List instr)
    (point : Code.StructuredCode.Point (Code.CoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels stack
      (.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode.Point (Code.CoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels stack
        (.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after) target.val next output) ∨
    (∃ dst bits, value = bits ∧
      dst.val = Code.slots C.LOCALS + Code.slots stack ∧ code[pc]? = some (.Const32 dst bits) ∧
      Code.StructuredCode.Point (Code.CoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels
        (stack ++ [.I32]) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after = source at relation
  cases relation with
  | linear head fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨dst,bits,emitted,result,valueEq,position⟩ := coreEmission_integer32_inv value head
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨dst,bits,rfl,position,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => cases sourceEq

theorem coreEmission_integer64_inv {C before after emitted} (value : U64)
    (emission : Code.CoreEmission C before (.CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val))) emitted after) :
    ∃ dst bits, emitted = [.Const64 dst bits] ∧ after = before ++ [.I64] ∧
      value = bits ∧ dst.val = Code.slots C.LOCALS + Code.slots before := by
  generalize equality : instr.CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) = instruction at emission
  cases emission with
  | pure pure =>
    rw [←equality] at pure
    obtain ⟨dst,emitted,result,position⟩ := linearEmission_const64_inv value pure
    exact ⟨dst,value,emitted,result,rfl,position⟩
  | load => simp [Abs.Memory.Load.source] at equality
  | store => simp [Abs.Memory.Store.source] at equality
  | _ => cases equality

theorem corePoint_integer64_head {C returns code labels stack pc next output}
    (value : U64) (after : List instr)
    (point : Code.StructuredCode.Point (Code.CoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels stack
      (.CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode.Point (Code.CoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels stack
        (.CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after) target.val next output) ∨
    (∃ dst bits, value = bits ∧
      dst.val = Code.slots C.LOCALS + Code.slots stack ∧ code[pc]? = some (.Const64 dst bits) ∧
      Code.StructuredCode.Point (Code.CoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels
        (stack ++ [.I64]) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after = source at relation
  cases relation with
  | linear head fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨dst,bits,emitted,result,valueEq,position⟩ := coreEmission_integer64_inv value head
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨dst,bits,rfl,position,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => cases sourceEq

end Exec.Interp.IntegerConstant
