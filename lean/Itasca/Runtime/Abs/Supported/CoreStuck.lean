import Itasca.Runtime.Abs.Core
import Itasca.Runtime.Abs.Core.Step
import Itasca.Runtime.Abs.BinaryInstr
import Itasca.Runtime.Abs.SupportedState

namespace Itasca.Runtime.Abs

/-- `Core.instruction` never executes the head; another transition relation handles it. -/
def CoreStuck (op : instr) : Prop :=
  ∀ s ambient f rest after, Core.instruction s ambient f rest op after = .stuck

theorem float_core_stuck (op : Float.Instruction) : CoreStuck op.source := by
  intro s ambient f rest after
  cases op <;> simp [Core.instruction,Float.Instruction.source,astep,Numeric.decodeInstruction]

theorem stateful_core_stuck (op : Stateful.Instruction) : CoreStuck op.source := by
  intro s ambient f rest after
  cases op <;> simp [Core.instruction,Stateful.Instruction.source,astep,Numeric.decodeInstruction]

theorem indirect_core_stuck (table : tableidx) (type : typeidx) : CoreStuck (.CALL_INDIRECT table type) := by
  intro s ambient f rest after
  simp [Core.instruction,astep,Numeric.decodeInstruction]

theorem SimdInstr.core_stuck {op : instr} (supported : SimdInstr op) : CoreStuck op := by
  intro s ambient f rest after
  cases supported with
  | pure signature => cases signature <;> rfl
  | constant => rfl
  | memory signature => cases signature <;> rfl

theorem BinaryInstr.core_head {op} (allowed : BinaryInstr op) : CoreHead op ∨ CoreStuck op := by
  cases allowed with
  | nop => exact .inl (.pure .nop)
  | unreachable => exact .inl (.pure .unreachable)
  | drop => exact .inl (.pure .drop)
  | const ty value => exact .inl (.const ty value)
  | numeric op => exact .inl (.pure (.numeric op))
  | float op => exact .inr (float_core_stuck op)
  | select => exact .inl .select
  | typed_select ty => exact .inr fun _ _ _ _ _ => rfl
  | local_get index => exact .inl (.pure (.local_get index))
  | local_set index => exact .inl (.pure (.local_set index))
  | local_tee index => exact .inl (.pure (.local_tee index))
  | global_get index => exact .inl (.global_get index)
  | global_set index => exact .inl (.global_set index)
  | load op argument => exact .inl (.load op argument)
  | store op argument => exact .inl (.store op argument)
  | stateful op => exact .inr (stateful_core_stuck op)
  | simd simd => exact .inr simd.core_stuck
  | block ty body _ => exact .inl (.pure (.block ty body))
  | loop ty body _ => exact .inl (.pure (.loop ty body))
  | ifelse ty yes no _ _ => exact .inl (.pure (.ifelse ty yes no))
  | br depth => exact .inl (.pure (.br depth))
  | br_if depth => exact .inl (.pure (.br_if depth))
  | br_table labels fallback => exact .inr fun _ _ _ _ _ => rfl
  | call index => exact .inl (.pure (.call index))
  | call_indirect table type => exact .inr (indirect_core_stuck table type)
  | ret => exact .inl (.pure .ret)

end Itasca.Runtime.Abs
