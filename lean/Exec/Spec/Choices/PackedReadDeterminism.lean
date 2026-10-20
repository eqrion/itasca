import Exec.Spec.PackedMemory
import Exec.Spec.MemoryReadBounds

/-! Determinism of the repaired generated packed-load rules at all five
supported scalar widths. Bounds and bounded decoding exclude both forms of
accidental alternatives: success versus trap, and distinct decoded words. -/

namespace Exec.Spec.PackedMemory
open SpecExt SpecExt.Builtins

private def lastInstruction : config → Option admininstr
  | .mk_config _ body => body.getLast?

set_option maxHeartbeats 800000 in
theorem read_cases (op : PackedMemory) (sign : sx) (argument : memarg)
    (z : state) (address : num_) {before : config} {out : List admininstr}
    (source : Step_read before out)
    (same : before = ⟨z,[.CONST .I32 address,op.load sign argument]⟩) :
    (out = [.TRAP] ∧ (fun_mem z (.mk_uN 0)).BYTES.length <
      proj_uN_0 (proj_num__0 address).get!+proj_uN_0 argument.OFFSET+op.bytes) ∨ ∃ word,
      proj_uN_0 word < 2^op.bits ∧
      ibytes_ op.bits word = ((fun_mem z (.mk_uN 0)).BYTES.drop
        (proj_uN_0 (proj_num__0 address).get!+proj_uN_0 argument.OFFSET)).take op.bytes ∧
      out = [.CONST (numtype_Inn op.type)
        (.mk_num__0 op.type (extend__ op.bits (sizenn (numtype_Inn op.type)) sign word))] := by
  have last : lastInstruction before = some (op.load sign argument) := by rw [same]; rfl
  cases source <;> simp [lastInstruction,load,Map] at last
  case load_pack_val =>
    rename_i word _ _ encoding bound _ _ _
    refine Or.inr ⟨word,?_,?_,?_⟩ <;>
      simp_all [load,config.mk_config.injEq,byte_count,size_eq]
  all_goals simp_all [load,config.mk_config.injEq,byte_count]

private theorem packed_payload_bounds (op : PackedMemory) (bytes : List byte) (address : Nat) (word : uN)
    (read : ibytes_ op.bits word = (bytes.drop address).take op.bytes) :
    address+op.bytes ≤ bytes.length := by
  apply integer_read_bounds bytes address op.bits word (by cases op <;> decide) read

/-- For each supported packed width, the repaired generated relation has one
result. Success and trap cannot coexist, and successful extensions agree. -/
theorem read_deterministic (op : PackedMemory) (sign : sx) (argument : memarg)
    (z : state) (address : num_) (left right : List admininstr)
    (first : Step_read ⟨z,[.CONST .I32 address,op.load sign argument]⟩ left)
    (second : Step_read ⟨z,[.CONST .I32 address,op.load sign argument]⟩ right) : left = right := by
  rcases read_cases op sign argument z address first rfl with ⟨leftTrap,leftOutside⟩ | ⟨word,leftBound,leftRead,leftValue⟩
  · rcases read_cases op sign argument z address second rfl with ⟨rightTrap,_⟩ | ⟨other,_,rightRead,_⟩
    · exact leftTrap.trans rightTrap.symm
    · have inside := packed_payload_bounds op _ _ other rightRead
      omega
  · rcases read_cases op sign argument z address second rfl with ⟨_,rightOutside⟩ | ⟨other,rightBound,rightRead,rightValue⟩
    · have inside := packed_payload_bounds op _ _ word leftRead
      omega
    · have same := integer_read_value_unique op.bits (by cases op <;> decide) _ word other
        leftBound rightBound leftRead rightRead
      cases same
      exact leftValue.trans rightValue.symm

end Exec.Spec.PackedMemory

