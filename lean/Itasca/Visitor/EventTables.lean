import Itasca.Binary.Wasm2.NumericExtensions
import Itasca.Visitor.EventMeaning
import Mathlib.Tactic.IntervalCases

open Aeneas Aeneas.Std

namespace Itasca.VisitorTrace

@[simp] theorem NumericHook.ofOpcode_opcode (hook : NumericHook) :
    NumericHook.ofOpcode hook.opcode = some hook := by
  cases hook <;> rfl

@[simp] theorem MemoryHook.ofOpcode_opcode (hook : MemoryHook) :
    MemoryHook.ofOpcode hook.opcode = some hook := by
  cases hook <;> rfl

/-- The hook mnemonic's instruction agrees with the independent binary opcode map. -/
theorem NumericHook.opcode_meaning (hook : NumericHook) :
    (Numeric.opcodeMeaning hook.opcode).map Numeric.Operation.instruction =
      some hook.instruction := by
  cases hook <;> rfl

/-- Memory callback mnemonics retain load/store width, signedness, alignment and offset. -/
theorem MemoryHook.opcode_meaning (hook : MemoryHook) (arg : code.MemArg) :
    (MemoryMeaning.opcodeMeaning hook.opcode).map (fun op => op.op arg) =
      some (hook.instruction arg) := by
  cases hook <;> rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem NumericHook.ofOpcode_meaning (opcode : U8) :
    (NumericHook.ofOpcode opcode).map NumericHook.instruction =
      (Numeric.opcodeMeaning opcode).map Numeric.Operation.instruction := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change n < 256 at hn
  interval_cases n <;> rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem MemoryHook.ofOpcode_meaning (opcode : U8) (arg : code.MemArg) :
    (MemoryHook.ofOpcode opcode).map (fun hook => hook.instruction arg) =
      (MemoryMeaning.opcodeMeaning opcode).map (fun op => op.op arg) := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change n < 256 at hn
  interval_cases n <;> rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem NumericHook.ofOpcode_sound {opcode : U8} {hook : NumericHook}
    (h : NumericHook.ofOpcode opcode = some hook) : hook.opcode = opcode := by
  unfold NumericHook.ofOpcode at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> try contradiction
  all_goals subst hook
  all_goals apply UScalar.eq_of_val_eq
  all_goals first | assumption | (symm; assumption)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem MemoryHook.ofOpcode_sound {opcode : U8} {hook : MemoryHook}
    (h : MemoryHook.ofOpcode opcode = some hook) : hook.opcode = opcode := by
  unfold MemoryHook.ofOpcode at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> try contradiction
  all_goals subst hook
  all_goals apply UScalar.eq_of_val_eq
  all_goals first | assumption | (symm; assumption)

/-- A numeric binary row identifies the exact callback mnemonic. -/
theorem NumericHook.of_meaning {opcode : U8} {operation : Numeric.Operation}
    (h : Numeric.opcodeMeaning opcode = some operation) :
    ∃ hook, NumericHook.ofOpcode opcode = some hook ∧
      hook.opcode = opcode ∧ hook.instruction = operation.instruction := by
  have hm := NumericHook.ofOpcode_meaning opcode
  rw [h] at hm
  cases he : NumericHook.ofOpcode opcode with
  | none => simp [he] at hm
  | some hook =>
    refine ⟨hook, rfl, NumericHook.ofOpcode_sound he, ?_⟩
    simpa [he] using hm

/-- A memory binary row identifies the exact callback mnemonic and raw memarg translation. -/
theorem MemoryHook.of_meaning {opcode : U8} {operation : MemoryMeaning.Operation}
    (h : MemoryMeaning.opcodeMeaning opcode = some operation) :
    ∃ hook, MemoryHook.ofOpcode opcode = some hook ∧ hook.opcode = opcode ∧
      ∀ arg, hook.instruction arg = operation.op arg := by
  cases he : MemoryHook.ofOpcode opcode with
  | none =>
    have hm := MemoryHook.ofOpcode_meaning opcode ⟨0#u32, 0#u32⟩
    simp [he, h] at hm
  | some hook =>
    refine ⟨hook, rfl, MemoryHook.ofOpcode_sound he, ?_⟩
    intro arg
    simpa [he, h] using MemoryHook.ofOpcode_meaning opcode arg

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Exhaustive agreement of actual numeric dispatch with independently named callbacks. -/
theorem visit_numeric {V : Type} (visitor : code.OpVisitor V) (v : V)
    (st : code.OpIterState) (opcode : U8) :
    code.visit_numeric visitor v st opcode =
      match NumericHook.ofOpcode opcode with
      | some hook => invoke visitor v (.op st (.numeric hook))
      | none => .ok (.Ok (), v) := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change n < 256 at hn
  interval_cases n <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Exhaustive agreement of actual memory dispatch with independently named callbacks. -/
theorem visit_memory {V : Type} (visitor : code.OpVisitor V) (v : V)
    (st : code.OpIterState) (opcode : U8) (arg : code.MemArg) :
    code.visit_memory visitor v st opcode arg =
      match MemoryHook.ofOpcode opcode with
      | some hook => invoke visitor v (.op st (.memory hook arg))
      | none => .ok (.Ok (), v) := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change n < 256 at hn
  interval_cases n <;> with_unfolding_all rfl

theorem NumericHook.dispatch {V : Type} (visitor : code.OpVisitor V) (v : V)
    (st : code.OpIterState) (hook : NumericHook) :
    code.visit_numeric visitor v st hook.opcode =
      invoke visitor v (.op st (.numeric hook)) := by
  simp only [visit_numeric, NumericHook.ofOpcode_opcode]

theorem MemoryHook.dispatch {V : Type} (visitor : code.OpVisitor V) (v : V)
    (st : code.OpIterState) (hook : MemoryHook) (arg : code.MemArg) :
    code.visit_memory visitor v st hook.opcode arg =
      invoke visitor v (.op st (.memory hook arg)) := by
  simp only [visit_memory, MemoryHook.ofOpcode_opcode]

end Itasca.VisitorTrace

namespace Itasca.VisitorTrace

/-- Every scalar-extension callback names exactly its independently specified instruction. -/
theorem ExtendedNumericHook.meaning (hook : ExtendedNumericHook) :
    match hook.encoding.2 with
    | none => ∃ operation,
        MultiValue.NumericExtensions.signMeaning hook.encoding.1 = some operation ∧
        operation.instruction = hook.instruction
    | some subopcode => ∃ operation,
        MultiValue.NumericExtensions.saturatingMeaning subopcode = some operation ∧
        operation.instruction = hook.instruction := by
  cases hook <;> exact ⟨_, rfl, rfl⟩

/-- Extracted extension dispatch invokes the independently named callback. -/
theorem ExtendedNumericHook.dispatch {V : Type} (visitor : code.OpVisitor V)
    (v : V) (st : code.OpIterState) (hook : ExtendedNumericHook) :
    (match hook.encoding.2 with
    | none => code.visit_sign_extension visitor v st hook.encoding.1
    | some subopcode => code.visit_saturating visitor v st subopcode) =
      invoke visitor v (.op st (.extendedNumeric hook)) := by
  cases hook <;> rfl

end Itasca.VisitorTrace
