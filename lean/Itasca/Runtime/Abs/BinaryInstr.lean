import Itasca.Runtime.Abs.Simd.Source
import Itasca.Runtime.Abs.Float.Descriptor
import Itasca.Runtime.Abs.Stateful.Descriptor
import Itasca.Runtime.Abs.Memory.Descriptor
import Itasca.Runtime.Abs.Numeric.Semantics

/-!
# Binary instructions

`BinaryInstr` is the source syntax a decoded binary function body can contain: every
Wasm 2.0 instruction except the administrative forms. `Code/Local/Source/SourceExecutable`
proves that each decoded body satisfies it. It is an internal store invariant, never a
premise of a headline theorem.
-/

namespace Itasca.Runtime.Abs

inductive BinaryInstr : instr → Prop where
  | nop : BinaryInstr .NOP
  | unreachable : BinaryInstr .UNREACHABLE
  | drop : BinaryInstr .DROP
  | const (ty : numtype) (value : num_) : BinaryInstr (.CONST ty value)
  | numeric (op : Numeric.Instruction) : BinaryInstr op.source
  | float (op : Float.Instruction) : BinaryInstr op.source
  | select : BinaryInstr (.SELECT none)
  | typed_select (ty : valtype) : BinaryInstr (.SELECT (some [ty]))
  | local_get (index : idx) : BinaryInstr (.LOCAL_GET index)
  | local_set (index : idx) : BinaryInstr (.LOCAL_SET index)
  | local_tee (index : idx) : BinaryInstr (.LOCAL_TEE index)
  | global_get (index : idx) : BinaryInstr (.GLOBAL_GET index)
  | global_set (index : idx) : BinaryInstr (.GLOBAL_SET index)
  | load (op : Memory.Load) (argument : memarg) : BinaryInstr (op.source argument)
  | store (op : Memory.Store) (argument : memarg) : BinaryInstr (op.source argument)
  | stateful (op : Stateful.Instruction) : BinaryInstr op.source
  | simd {source} : SimdInstr source → BinaryInstr source
  | block (ty : blocktype) (body : List instr) : Forall BinaryInstr body → BinaryInstr (.BLOCK ty body)
  | loop (ty : blocktype) (body : List instr) : Forall BinaryInstr body → BinaryInstr (.LOOP ty body)
  | ifelse (ty : blocktype) (yes no : List instr) :
      Forall BinaryInstr yes → Forall BinaryInstr no → BinaryInstr (.IFELSE ty yes no)
  | br (depth : labelidx) : BinaryInstr (.BR depth)
  | br_if (depth : labelidx) : BinaryInstr (.BR_IF depth)
  | br_table (labels : List labelidx) (fallback : labelidx) : BinaryInstr (.BR_TABLE labels fallback)
  | call (index : funcidx) : BinaryInstr (.CALL index)
  | call_indirect (table : tableidx) (type : typeidx) : BinaryInstr (.CALL_INDIRECT table type)
  | ret : BinaryInstr .RETURN

/-- Structured control is never the source of an operation descriptor. -/
def structuredTag : instr → Bool
  | .BLOCK .. | .LOOP .. | .IFELSE .. => true
  | _ => false

private theorem numeric_unstructured (op : Numeric.Instruction) : structuredTag op.source = false := by
  cases op with
  | conversion op => cases op <;> rfl
  | _ => rfl

private theorem float_unstructured (op : Float.Instruction) : structuredTag op.source = false := by
  cases op <;> rfl

private theorem stateful_unstructured (op : Stateful.Instruction) : structuredTag op.source = false := by
  cases op <;> rfl

private theorem simd_unstructured {source} (simd : SimdInstr source) : structuredTag source = false := by
  cases simd with
  | pure signature => cases signature <;> rfl
  | constant => rfl
  | memory signature => cases signature <;> rfl

theorem BinaryInstr.block_body {ty body} (allowed : BinaryInstr (.BLOCK ty body)) :
    Forall BinaryInstr body := by
  generalize equal : instr.BLOCK ty body = source at allowed
  cases allowed with
  | block _ _ body => cases equal; exact body
  | numeric op => have tag := numeric_unstructured op; rw [← equal] at tag; cases tag
  | float op => have tag := float_unstructured op; rw [← equal] at tag; cases tag
  | stateful op => have tag := stateful_unstructured op; rw [← equal] at tag; cases tag
  | simd simd => have tag := simd_unstructured simd; rw [← equal] at tag; cases tag
  | _ => cases equal

theorem BinaryInstr.loop_body {ty body} (allowed : BinaryInstr (.LOOP ty body)) :
    Forall BinaryInstr body := by
  generalize equal : instr.LOOP ty body = source at allowed
  cases allowed with
  | loop _ _ body => cases equal; exact body
  | numeric op => have tag := numeric_unstructured op; rw [← equal] at tag; cases tag
  | float op => have tag := float_unstructured op; rw [← equal] at tag; cases tag
  | stateful op => have tag := stateful_unstructured op; rw [← equal] at tag; cases tag
  | simd simd => have tag := simd_unstructured simd; rw [← equal] at tag; cases tag
  | _ => cases equal

theorem BinaryInstr.if_bodies {ty yes no} (allowed : BinaryInstr (.IFELSE ty yes no)) :
    Forall BinaryInstr yes ∧ Forall BinaryInstr no := by
  generalize equal : instr.IFELSE ty yes no = source at allowed
  cases allowed with
  | ifelse _ _ _ yes no => cases equal; exact ⟨yes,no⟩
  | numeric op => have tag := numeric_unstructured op; rw [← equal] at tag; cases tag
  | float op => have tag := float_unstructured op; rw [← equal] at tag; cases tag
  | stateful op => have tag := stateful_unstructured op; rw [← equal] at tag; cases tag
  | simd simd => have tag := simd_unstructured simd; rw [← equal] at tag; cases tag
  | _ => cases equal

end Itasca.Runtime.Abs
