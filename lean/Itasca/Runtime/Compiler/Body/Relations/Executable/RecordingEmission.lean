import Itasca.Runtime.Compiler.Body.Relations.Executable.ExecutableEmission
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdConstructor
import Itasca.Runtime.Compiler.Local.Capacity.SimdMeaningBound

/-!
The emitted call-tag shape needed for exact event recording.

Main declarations: `callTag` and `RecordingEmissionShape`. A direct consumer is `Interp.Relations.StepRecordingInversion`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

def callTag : Bytecode → Nat
  | .Call .. => 1
  | .CallIndirect .. => 2
  | _ => 0

def RecordingEmissionShape (source : instr) (emitted : List Bytecode) : Prop :=
  (emitted=[] → source=.NOP ∨ source=.DROP) ∧
  ∀ first,emitted.head?=some first →
    (∀index offset,first≠.Call index offset) ∧
    (∀entry selector offset,first=.CallIndirect entry selector offset →
      ∃table type : U32,source=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val))

theorem RecordingEmissionShape.singleton (source : instr) (instruction : Bytecode)
    (silent : callTag instruction=0) : RecordingEmissionShape source [instruction] := by
  refine ⟨by simp,?_⟩
  intro first found
  have same : first=instruction := by simpa using found.symm
  subst first
  constructor
  · intro index offset equality
    rw [equality] at silent
    cases silent
  · intro entry selector offset equality
    rw [equality] at silent
    cases silent

theorem integerInstruction_callTag (op : Abs.Numeric.Instruction) (dst a b : U32) :
    callTag (integerInstruction op dst a b)=0 := by
  cases op with
  | binary ty operator => cases ty <;> cases operator <;> (try (rename_i sign; cases sign)) <;> rfl
  | compare ty operator => cases ty <;> cases operator <;> (try (rename_i sign; cases sign)) <;> rfl
  | unary ty operator => cases ty <;> cases operator <;> rfl
  | eqz ty => cases ty <;> rfl
  | conversion operator => cases operator <;> rfl

theorem floatInstruction_callTag (op : Abs.Float.Instruction) (dst a b : U32) :
    callTag (floatInstruction op dst a b)=0 := by
  cases op with
  | unary ty operator => cases ty <;> cases operator <;> rfl
  | binary ty operator => cases ty <;> cases operator <;> rfl
  | compare ty operator => cases ty <;> cases operator <;> rfl
  | convert source target sign => cases source <;> cases target <;> cases sign <;> rfl
  | truncate source target sign saturating => cases source <;> cases target <;> cases sign <;> cases saturating <;> rfl
  | reinterpretFloat source => cases source <;> rfl
  | reinterpretInt source => cases source <;> rfl
  | promote | demote => rfl

theorem LinearEmission.recording_shape {locals before source emitted after}
    (head : LinearEmission locals before source emitted after) : RecordingEmissionShape source emitted := by
  cases head with
  | nop => simp [RecordingEmissionShape]
  | drop => simp [RecordingEmissionShape]
  | binary stack ty op a b left right =>
    apply RecordingEmissionShape.singleton
    cases ty <;> cases op <;> rfl
  | numeric stack op a b left right => exact .singleton _ _ (integerInstruction_callTag ..)
  | localGet | localSet | localTee =>
    apply RecordingEmissionShape.singleton
    simp only [move]
    split <;> rfl
  | _ => exact .singleton _ _ rfl

theorem ScalarEmission.recording_shape {C before source emitted after}
    (head : ScalarEmission C before source emitted after) : RecordingEmissionShape source emitted := by
  cases head with
  | linear head => exact head.recording_shape
  | float => exact .singleton _ _ (floatInstruction_callTag ..)
  | select =>
    apply RecordingEmissionShape.singleton
    unfold selectInstruction
    split <;> rfl
  | globalGet =>
    apply RecordingEmissionShape.singleton
    unfold globalGetInstruction
    split <;> rfl
  | globalSet =>
    apply RecordingEmissionShape.singleton
    unfold globalSetInstruction
    split <;> rfl
  | load stack op argument address offset memory available sourceOffset slot =>
    apply RecordingEmissionShape.singleton
    cases op with
    | full ty => cases ty <;> rfl
    | packed ty width sign => cases ty <;> cases width <;> cases sign <;> rfl
  | store stack op argument address value offset memory available sourceOffset addressSlot valueSlot =>
    apply RecordingEmissionShape.singleton
    cases op with
    | full ty => cases ty <;> rfl
    | packed ty width => cases ty <;> cases width <;> rfl
  | _ => exact .singleton _ _ rfl

theorem StatefulEmission.recording_shape {pairs C before source emitted after}
    (head : StatefulEmission pairs C before source emitted after) : RecordingEmissionShape source emitted := by
  cases head with
  | instruction stack input output op signature first second a b entry firstSlot secondSlot arguments pair =>
    apply RecordingEmissionShape.singleton
    cases op <;> rfl

theorem IndirectCallEmission.recording_shape {pairs C before source emitted after}
    (head : IndirectCallEmission pairs C before source emitted after) : RecordingEmissionShape source emitted := by
  cases head
  refine ⟨by simp,?_⟩
  intro first found
  simp only [List.head?_cons,Option.some.injEq] at found
  subst first
  exact ⟨by intros; simp,by intros; exact ⟨_,_,rfl⟩⟩

theorem SimdEmission.recording_shape {immediates constants C before source emitted after}
    (head : SimdEmission immediates constants C before source emitted after) : RecordingEmissionShape source emitted := by
  cases head with
  | constant => exact .singleton _ _ rfl
  | instruction front input output source opcode operand entry immediate instruction meaning metadata constructed position =>
    apply RecordingEmissionShape.singleton
    have view := make_simd_roundtrip_bounded opcode operand operand entry instruction meaning.opcode_bound constructed
    cases instruction <;> first | rfl | simp [runtime.bytecode.Instr.simd,Result.ok.injEq] at view

theorem TypedSelectEmission.recording_shape {C before source emitted after}
    (head : TypedSelectEmission C before source emitted after) : RecordingEmissionShape source emitted := by
  cases head
  apply RecordingEmissionShape.singleton
  unfold selectInstruction
  split <;> rfl

theorem ExecutableEmission.recording_shape {tables C before source emitted after}
    (head : ExecutableEmission tables C before source emitted after) : RecordingEmissionShape source emitted := by
  cases head with
  | scalar h | stateful h | indirect h | simd h | typedSelect h => exact h.recording_shape
  | branchTable => exact .singleton _ _ rfl
end Itasca.Runtime.Code
