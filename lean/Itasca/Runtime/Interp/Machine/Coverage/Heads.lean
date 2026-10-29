import Itasca.Runtime.Interp.Machine.Point
import Itasca.Runtime.Interp.Machine.Emission.Empty
import Itasca.Runtime.SourceMachine.Core
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulEmission
import Itasca.Runtime.Compiler.Local.Relations.Calls.IndirectCallEmission
import Itasca.Runtime.Compiler.Local.Relations.Calls.IndirectCallExclusions
import Itasca.Runtime.Compiler.Local.Relations.Calls.IndirectCallInversion
import Itasca.Runtime.Compiler.Local.Source.TypedSelectEmission
import Itasca.Runtime.Compiler.Body.Lowering.Simd.SimdEmissionExclusion
import Itasca.Runtime.Compiler.Body.Relations.Executable.ExecutableProjection

/-!
# Emission head projections

Classes that project an emitted head of a contextual emission relation onto the leaf relation
of its instruction family: `OrdinaryHeads`, `ErasedHeads`, `FloatHeads`, `StatefulProjection`,
`IndirectProjection`, `SimdProjection` and `TypedSelectHeads`. The leaf emission relations and
`Compiler.ExecutableEmission` are instances, and so is the per-function `emission compiled` with the
function's retained metadata tables.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas.Std

def ordinarySource : instr → Bool
  | .BLOCK .. | .LOOP .. | .IFELSE .. | .BR .. | .BR_IF .. | .CALL .. | .RETURN | .UNREACHABLE => false
  | _ => true

/-- Emitted ordinary heads cannot impersonate structured control syntax. -/
class OrdinaryHeads (emission : ContextEmission) : Prop where
  ordinary : ∀ {C before instruction emitted after}, emission C before instruction emitted after → ordinarySource instruction = true

/-- Erased source operations emit exactly their existing empty linear fragments. -/
class ErasedHeads (emission : ContextEmission) : Prop where
  nop : ∀ {C before after emitted}, emission C before .NOP emitted after →
    Compiler.LinearEmission C.LOCALS before .NOP emitted after
  drop : ∀ {C before after emitted}, emission C before .DROP emitted after →
    Compiler.LinearEmission C.LOCALS before .DROP emitted after

/-- Projection of an emitted scalar head, independent of the following source program. -/
class FloatHeads (emission : ContextEmission) : Prop where
  project : ∀ {C before instruction emitted after}, SourceMachine.ScalarHead instruction →
    emission C before instruction emitted after → Compiler.ScalarEmission C before instruction emitted after

/-- The current stateful source head retains its exact immutable index-pair metadata. -/
class StatefulProjection (emission : ContextEmission) (pairs : List (U32 × U32)) : Prop where
  project : ∀ {C before op emitted after}, emission C before (SourceMachine.Stateful.Instruction.source op) emitted after →
    Compiler.StatefulEmission pairs C before op.source emitted after

/-- The current indirect call retains its actual immutable table/type pair. -/
class IndirectProjection (emission : ContextEmission) (pairs : List (U32 × U32)) : Prop where
  project : ∀ {C before table type emitted after},
    emission C before (.CALL_INDIRECT table type) emitted after →
    Compiler.IndirectCallEmission pairs C before (.CALL_INDIRECT table type) emitted after

/-- An emitted SIMD head retains the current function's exact SIMD and constant tables. -/
class SimdProjection (emission : ContextEmission)
    (simd : List runtime.bytecode.SimdImmediate) (constants : List U128) : Prop where
  project : ∀ {C before source emitted after}, SourceMachine.SimdInstr source →
    emission C before source emitted after → Compiler.SimdEmission simd constants C before source emitted after

class TypedSelectHeads (family : ContextEmission) : Prop where
  project : ∀ {C stack ty emitted output}, family C stack (.SELECT (some [ty])) emitted output →
    Compiler.TypedSelectEmission C stack (.SELECT (some [ty])) emitted output

theorem linear_emission_ordinary {locals before instruction emitted after}
    (head : Compiler.LinearEmission locals before instruction emitted after) : ordinarySource instruction = true := by
  cases head <;> try rfl
  case binary stack ty op a b left right => cases op <;> rfl
  case numeric stack op a b left right => cases op <;> (try casesm* SourceMachine.Numeric.Conversion) <;> rfl

theorem scalar_stateful_none {instruction} (covered : SourceMachine.ScalarHead instruction) :
    SourceMachine.Stateful.decodeInstruction instruction = none := by
  cases covered with
  | core h =>
    cases h with
    | pure h => cases h with
      | numeric op => cases op <;> rfl
      | _ => rfl
    | load op argument => cases op <;> rfl
    | store op argument => cases op <;> rfl
    | _ => rfl
  | float op => cases op <;> rfl

theorem scalar_not_indirect {table type} (covered : SourceMachine.ScalarHead (.CALL_INDIRECT table type)) : False := by
  generalize equal : instr.CALL_INDIRECT table type = instruction at covered
  cases covered with
  | core h =>
    cases h with
    | pure h => cases h with
      | numeric op => cases op <;> cases equal
      | _ => cases equal
    | load op arg => cases op <;> cases equal
    | store op arg => cases op <;> cases equal
    | _ => cases equal
  | float op => cases op <;> cases equal

end Itasca.Runtime.Interp.Machine

namespace Itasca.Runtime.Interp.Stateful

theorem linear_decode_none {locals before instruction emitted after}
    (head : Compiler.LinearEmission locals before instruction emitted after) :
    SourceMachine.Stateful.decodeInstruction instruction = none := by
  cases head with
  | binary stack type op a b left right => cases op <;> rfl
  | numeric stack op a b left right => cases op <;> rfl
  | _ => rfl

theorem scalar_decode_none {C before instruction emitted after}
    (head : Compiler.ScalarEmission C before instruction emitted after) :
    SourceMachine.Stateful.decodeInstruction instruction = none := by
  cases head with
  | linear h => exact linear_decode_none h
  | float stack op a b left right => cases op <;> rfl
  | _ => rfl

end Itasca.Runtime.Interp.Stateful

namespace Itasca.Runtime.Interp.Machine

instance : OrdinaryHeads Compiler.ScalarEmission where
  ordinary := by
    intro C before instruction emitted after head
    cases head <;> try rfl
    case linear h => exact linear_emission_ordinary h
    case float stack op left right leftSlot rightSlot => cases op <;> rfl

instance {pairs} : OrdinaryHeads (Compiler.StatefulEmission pairs) where
  ordinary := by
    intro C before instruction emitted after head
    cases head with
    | instruction stack input output op signature first second a b entry firstSlot secondSlot arguments pair =>
      cases op <;> rfl

instance (immediates constants) : OrdinaryHeads (Compiler.SimdEmission immediates constants) where
  ordinary := by
    intro C before source emitted after head
    have tag := head.allowed.source_tag
    cases source <;> simp_all [ordinarySource,SourceMachine.simdSourceTag]

instance : ErasedHeads Compiler.ScalarEmission := ⟨scalar_emission_nop_pure,scalar_emission_drop_pure⟩

instance {pairs} : ErasedHeads (Compiler.StatefulEmission pairs) where
  nop := by
    intro C before after emitted head
    generalize equality : instr.NOP = instruction at head
    cases head with
    | instruction stack input output op signature first second a b entry firstSlot secondSlot arguments pair =>
      cases op <;> cases equality
  drop := by
    intro C before after emitted head
    generalize equality : instr.DROP = instruction at head
    cases head with
    | instruction stack input output op signature first second a b entry firstSlot secondSlot arguments pair =>
      cases op <;> cases equality

instance (immediates constants) : ErasedHeads (Compiler.SimdEmission immediates constants) where
  nop := by
    intro C before after emitted head
    have impossible := head.allowed.source_tag
    cases impossible
  drop := by
    intro C before after emitted head
    have impossible := head.allowed.source_tag
    cases impossible

instance (tables : Compiler.CompilerTables) : OrdinaryHeads (Compiler.ExecutableEmission tables) where
  ordinary := by
    intro C before source emitted after head
    cases head with
    | scalar h | stateful h | simd h => exact OrdinaryHeads.ordinary h
    | indirect h => cases h; rfl
    | typedSelect h => cases h; rfl
    | branchTable => rfl

instance (tables : Compiler.CompilerTables) : ErasedHeads (Compiler.ExecutableEmission tables) where
  nop := by
    intro C before after emitted head
    generalize equal : instr.NOP = source at head
    cases head with
    | scalar h | stateful h | simd h => subst equal; exact ErasedHeads.nop h
    | indirect h => cases h; cases equal
    | typedSelect h => cases h; cases equal
    | branchTable => cases equal
  drop := by
    intro C before after emitted head
    generalize equal : instr.DROP = source at head
    cases head with
    | scalar h | stateful h | simd h => subst equal; exact ErasedHeads.drop h
    | indirect h => cases h; cases equal
    | typedSelect h => cases h; cases equal
    | branchTable => cases equal

instance (tables : Compiler.CompilerTables) : FloatHeads (Compiler.ExecutableEmission tables) where
  project := by
    intro C before source emitted after allowed head
    cases head with
    | scalar h => exact h
    | stateful h =>
      cases h with
      | instruction stack input output op =>
        have impossible := scalar_stateful_none allowed
        rw [SourceMachine.Stateful.decode_source] at impossible
        cases impossible
    | indirect h => cases h; exact False.elim (scalar_not_indirect allowed)
    | simd h => have := h.allowed.source_tag.symm.trans allowed.simd_tag; contradiction
    | typedSelect h => cases h; have := allowed.executable_extension_tag; contradiction
    | branchTable => have := allowed.executable_extension_tag; contradiction

instance (tables : Compiler.CompilerTables) : StatefulProjection (Compiler.ExecutableEmission tables) tables.indirect where
  project := by
    intro C before op emitted after head
    generalize sourceEq : op.source = source at head
    cases head with
    | scalar h =>
      have impossible := Stateful.scalar_decode_none h
      rw [← sourceEq, SourceMachine.Stateful.decode_source] at impossible
      contradiction
    | stateful h => subst sourceEq; exact h
    | indirect h =>
      cases h
      have impossible := congrArg SourceMachine.Stateful.decodeInstruction sourceEq
      rw [SourceMachine.Stateful.decode_source] at impossible
      contradiction
    | simd h =>
      have tag := h.allowed.source_tag
      rw [← sourceEq] at tag
      cases op <;> cases tag
    | typedSelect h => cases h; cases op <;> cases sourceEq
    | branchTable => cases op <;> cases sourceEq

instance (tables : Compiler.CompilerTables) : IndirectProjection (Compiler.ExecutableEmission tables) tables.indirect where
  project := by
    intro C before table type emitted after head
    generalize equal : instr.CALL_INDIRECT table type = source at head
    cases head with
    | scalar h => subst equal; exact False.elim (Compiler.scalar_emission_not_indirect h)
    | stateful h => subst equal; exact False.elim (Compiler.stateful_emission_not_indirect h)
    | indirect h => subst equal; exact h
    | simd h => have tag := h.allowed.source_tag; rw [← equal] at tag; cases tag
    | typedSelect h => cases h; cases equal
    | branchTable => cases equal

instance (tables : Compiler.CompilerTables) : SimdProjection (Compiler.ExecutableEmission tables) tables.simd tables.constants where
  project := by
    intro C before source emitted after allowed head
    have tag := allowed.source_tag
    cases head with
    | simd h => exact h
    | scalar h => rw [h.simd_tag] at tag; cases tag
    | stateful h => cases h with
      | instruction stack input output op => cases op <;> cases tag
    | indirect h => cases h; cases tag
    | typedSelect h => cases h; cases tag
    | branchTable => cases tag

instance (tables : Compiler.CompilerTables) : TypedSelectHeads (Compiler.ExecutableEmission tables) where
  project head := head.typed_select_inv

/-- Resolve retained-table projections at an actual compiled function. -/
instance executable_stateful_projection (compiled : runtime.bytecode.CompiledFunction) :
    StatefulProjection (emission compiled) compiled.indirect.val := by
  change StatefulProjection (Compiler.ExecutableEmission (Compiler.CompilerTables.ofFunction compiled))
    (Compiler.CompilerTables.ofFunction compiled).indirect
  infer_instance

instance executable_indirect_projection (compiled : runtime.bytecode.CompiledFunction) :
    IndirectProjection (emission compiled) compiled.indirect.val := by
  change IndirectProjection (Compiler.ExecutableEmission (Compiler.CompilerTables.ofFunction compiled))
    (Compiler.CompilerTables.ofFunction compiled).indirect
  infer_instance

instance executable_simd_projection (compiled : runtime.bytecode.CompiledFunction) :
    SimdProjection (emission compiled) compiled.simd.val compiled.v128_pool.val := by
  change SimdProjection (Compiler.ExecutableEmission (Compiler.CompilerTables.ofFunction compiled))
    (Compiler.CompilerTables.ofFunction compiled).simd (Compiler.CompilerTables.ofFunction compiled).constants
  infer_instance

end Itasca.Runtime.Interp.Machine
