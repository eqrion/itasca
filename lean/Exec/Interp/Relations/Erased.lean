import Exec.Abs.Numeric.Decode
import Exec.Interp.Relations.Rel
import Exec.Abs.Sim.Instruction

/-! Source reductions whose compiler emission is empty. They advance the
abstract continuation while retaining the actual bytecode position and slot
storage; dead dropped words remain outside the live value relation. -/
namespace Exec.Interp
open Aeneas.Std

theorem linearEmission_nop_inv {locals before after : List valtype} {emitted : List Code.Bytecode}
    (h : Code.LinearEmission locals before .NOP emitted after) : emitted = [] ∧ after = before := by
  generalize equality : instr.NOP = instruction at h
  cases h with
  | binary stack ity op left right hl hr => cases op <;> simp_all [Code.IntegerBinary.source]
  | numeric stack op a b ha hb =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    simp [Abs.Numeric.decodeInstruction_source, Abs.Numeric.decodeInstruction] at decoded
  | _ => simp_all

theorem linearEmission_drop_inv {locals before after : List valtype} {emitted : List Code.Bytecode}
    (h : Code.LinearEmission locals before .DROP emitted after) :
    ∃ stack ty, before = stack ++ [ty] ∧ after = stack ∧ emitted = [] := by
  generalize equality : instr.DROP = instruction at h
  cases h with
  | drop stack ty => exact ⟨_, ty, rfl, rfl, rfl⟩
  | binary stack ity op left right hl hr => cases op <;> simp_all [Code.IntegerBinary.source]
  | numeric stack op a b ha hb =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    simp [Abs.Numeric.decodeInstruction_source, Abs.Numeric.decodeInstruction] at decoded
  | _ => simp_all

theorem linearCodeRel_nop {locals before after : List valtype} {source : List instr}
    {code : List Code.Bytecode} {pc next : Nat}
    (relation : Code.LinearCodeRel locals before (.NOP :: source) code pc next after) :
    Code.LinearCodeRel locals before source code pc next after := by
  obtain ⟨middle, emitted, head, _, tail⟩ := linearCodeRel_head relation
  obtain ⟨rfl, rfl⟩ := linearEmission_nop_inv head
  simpa using tail

theorem linearCodeRel_drop {locals stack after : List valtype} {ty : valtype} {source : List instr}
    {code : List Code.Bytecode} {pc next : Nat}
    (relation : Code.LinearCodeRel locals (stack ++ [ty]) (.DROP :: source) code pc next after) :
    Code.LinearCodeRel locals stack source code pc next after := by
  obtain ⟨middle, emitted, head, _, tail⟩ := linearCodeRel_head relation
  obtain ⟨remaining, ty', stackEq, middleEq, empty⟩ := linearEmission_drop_inv head
  have same : stack = remaining := (List.append_inj' stackEq (by simp)).1
  rw [middleEq, empty] at tail
  simpa only [← same, List.length_nil, Nat.add_zero] using tail

theorem erased_nop (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (compiled : runtime.bytecode.CompiledFunction) (next : Nat) (output : List valtype)
    (s : store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .NOP :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : LinearPoint raw { f with code := .NOP :: after } compiled next output) :
    FrameSlots exec raw { f with code := after } ∧
    LinearPoint raw { f with code := after } compiled next output ∧
    Abs.ATyped ⟨s, ambient, { f with code := after } :: rest, []⟩ ∧
    Abs.NextSim ⟨s, ambient, { f with code := .NOP :: after } :: rest, []⟩
      ⟨s, ambient, { f with code := after } :: rest, []⟩ := by
  have step : Abs.astep ⟨s, ambient, { f with code := .NOP :: after } :: rest, []⟩ =
      .next ⟨s, ambient, { f with code := after } :: rest, []⟩ := rfl
  exact ⟨slots, linearCodeRel_nop point,
    Abs.instruction_preservation s ambient f rest .NOP after _ .nop typed step,
    Abs.instruction_simulation s ambient f rest .NOP after _ .nop typed step⟩

theorem erased_drop (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (compiled : runtime.bytecode.CompiledFunction) (next : Nat) (output : List valtype)
    (s : store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (front : List val) (value : val)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .DROP :: after, vals := front ++ [value] } :: rest, []⟩)
    (slots : FrameSlots exec raw { f with vals := front ++ [value] })
    (point : LinearPoint raw { f with code := .DROP :: after, vals := front ++ [value] } compiled next output) :
    FrameSlots exec raw { f with code := after, vals := front } ∧
    LinearPoint raw { f with code := after, vals := front } compiled next output ∧
    Abs.ATyped ⟨s, ambient, { f with code := after, vals := front } :: rest, []⟩ ∧
    Abs.NextSim ⟨s, ambient, { f with code := .DROP :: after, vals := front ++ [value] } :: rest, []⟩
      ⟨s, ambient, { f with code := after, vals := front } :: rest, []⟩ := by
  have step : Abs.astep ⟨s, ambient, { f with code := .DROP :: after, vals := front ++ [value] } :: rest, []⟩ =
      .next ⟨s, ambient, { f with code := after, vals := front } :: rest, []⟩ := by
    simp only [Abs.astep, Abs.pop_append, Abs.advance]
  have values : ValuesAt exec.slots.val raw.base.val ((f.locals ++ front) ++ [value]) := by
    simpa only [FrameSlots, List.append_assoc] using slots
  have certificate : LinearPoint raw { f with code := after, vals := front } compiled next output := by
    simp only [LinearPoint, List.map_append, List.map_cons, List.map_nil] at point ⊢
    exact linearCodeRel_drop point
  exact ⟨values.locals, certificate,
    Abs.instruction_preservation s ambient { f with vals := front ++ [value] } rest .DROP after _ .drop typed step,
    Abs.instruction_simulation s ambient { f with vals := front ++ [value] } rest .DROP after _ .drop typed step⟩

end Exec.Interp
