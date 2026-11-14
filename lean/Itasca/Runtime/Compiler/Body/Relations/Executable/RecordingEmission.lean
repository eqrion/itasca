import Itasca.Runtime.Compiler.Body.Control.Embedding.OrdinaryEmbedding
import Itasca.Runtime.Compiler.Local.Control.Simd.StructuredSimdEmbedding
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables
import Itasca.Runtime.Compiler.Local.Source.SourceEntry
import Itasca.Runtime.Compiler.Local.Control.Function.CumulativeFunctionContext
import Itasca.Runtime.Compiler.Local.Relations.Function.Function
import Itasca.Support.Result
import Itasca.Runtime.Compiler.Body.Lowering.Simd.SimdEmissionExclusion
import Itasca.Runtime.SourceMachine.BrTable
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdMemoryValid
import Itasca.Runtime.Compiler.Local.Capacity.SimdAuxiliaryGrowth

/-!
Sections, each formerly its own module: ExecutableEmission, ExecutableFunction, ExecutableModuleFunctions, ExecutableProjection, ExecutableFunctionContext, RecordingEmission.
-/

/-! ## ExecutableEmission -/

section

/-!
Every emitted ordinary instruction, with the function-local index-pair, SIMD and constant tables it uses, and the branch-table control gate. A branch-table gate can only enter `StructuredCode` through its structural constructor, which retains the actual target-table layout.

Main declarations: `ExecutableEmission`. A direct consumer is `Compiler.Body.Relations.Checking.ExecutableInstructionAcceptance`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- Every emitted ordinary instruction, with the function-local index-pair, SIMD
and constant tables it uses, and the branch-table control gate. A branch-table gate
can only enter `StructuredCode` through its structural constructor, which retains
the actual target-table layout. -/
inductive ExecutableEmission (tables : CompilerTables) (C : context) :
    List valtype → instr → List Bytecode → List valtype → Prop where
  | scalar {before source emitted after} (head : ScalarEmission C before source emitted after) :
      ExecutableEmission tables C before source emitted after
  | stateful {before source emitted after} (head : StatefulEmission tables.indirect C before source emitted after) :
      ExecutableEmission tables C before source emitted after
  | indirect {before source emitted after} (head : IndirectCallEmission tables.indirect C before source emitted after) :
      ExecutableEmission tables C before source emitted after
  | simd {before source emitted after} (head : SimdEmission tables.simd tables.constants C before source emitted after) :
      ExecutableEmission tables C before source emitted after
  | typedSelect {before source emitted after} (head : TypedSelectEmission C before source emitted after) :
      ExecutableEmission tables C before source emitted after
  | branchTable (stack : List valtype) (depths : List labelidx) (fallback : labelidx)
      (selector start len : U32) :
      ExecutableEmission tables C (stack ++ [.I32]) (.BR_TABLE depths fallback)
        [.JumpTable selector start len] stack

instance (tables C) : OrdinaryEmbedding tables.indirect C (ExecutableEmission tables C) :=
  ⟨.scalar, .stateful, .indirect⟩
instance (tables C) : SimdEmbedding tables.simd tables.constants C (ExecutableEmission tables C) :=
  ⟨.simd⟩

end Itasca.Runtime.Compiler

end

/-! ## ExecutableFunction -/

section

/-!
Complete Wasm-profile function certificate, including typed SELECT, BR_TABLE and the actual function-local SIMD and target tables.

Main declarations: `ExecutableFunctionCode` and `DefinedExecutableFunctionCode`. A direct consumer is `Compiler.Body.Relations.Entry.ExecutableEntryCompilerFinish`.
-/

namespace Itasca.Runtime.Compiler

/-- Complete Wasm-profile function certificate, including typed SELECT,
BR_TABLE and the actual function-local SIMD and target tables. -/
abbrev ExecutableFunctionCode := IndexedFunctionCode ExecutableEmission
abbrev DefinedExecutableFunctionCode := DefinedIndexedFunctionCode ExecutableEmission
end Itasca.Runtime.Compiler

end

/-! ## ExecutableModuleFunctions -/

section

/-!
The executable-function certificate for a compiled module.

Main declarations: `ExecutableModuleFunctions`. A direct consumer is `Compiler.Module.ExecutableCollectedFunctions`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
structure ExecutableModuleFunctions (module : runtime.compiler.ExecutableModule)
    (sources : List funccode) : Prop where
  count : sources.length = module.module.env.func_type_indices.val.length
  entry : ∀ (index : Nat) (typeIndex : U32),
    module.module.env.func_type_indices.val[index]? = some typeIndex →
      ∃ compiled source, module.functions.val[index]? = some compiled ∧
        sources[index]? = some source ∧ DefinedExecutableFunctionCode module.module.env typeIndex source compiled

/-- Appending synthetic code preserves every defined-function certificate. -/
theorem ExecutableModuleFunctions.extend {before after : runtime.compiler.ExecutableModule} {sources}
    (certificate : ExecutableModuleFunctions before sources)
    (source : after.module = before.module)
    (preserved : after.functions.val.take before.functions.val.length = before.functions.val) :
    ExecutableModuleFunctions after sources := by
  refine ⟨by simpa only [source] using certificate.count, ?_⟩
  intro index typeIndex found
  obtain ⟨compiled, src, foundCode, sourceLookup, code⟩ := certificate.entry index typeIndex (by simpa only [source] using found)
  refine ⟨compiled, src, ?_, sourceLookup, by simpa only [source] using code⟩
  have bound := (List.getElem?_eq_some_iff.mp foundCode).1
  have same := (List.getElem?_eq_some_iff.mp foundCode).2
  have retained := congrArg (fun list => list[index]?) preserved
  simpa [List.getElem?_take, bound, same] using retained
end Itasca.Runtime.Compiler

end

/-! ## ExecutableProjection -/

section

/-!
Inversion of complete-profile emission into its operation-family cases.

Main declarations: `LinearEmission.executable_extension_tag` and `ExecutableEmission.typed_select_inv`. A direct consumer is `Interp.Machine.Coverage.Heads`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

theorem LinearEmission.executable_extension_tag {locals before source emitted after}
    (head : LinearEmission locals before source emitted after) : SourceMachine.executableExtensionTag source = false := by
  cases head with
  | binary stack ty op => cases op <;> rfl
  | numeric stack op => cases op with
    | conversion op => cases op <;> rfl
    | _ => rfl
  | _ => rfl

theorem ScalarEmission.executable_extension_tag {C before source emitted after}
    (head : ScalarEmission C before source emitted after) : SourceMachine.executableExtensionTag source = false := by
  cases head with
  | linear h => exact h.executable_extension_tag
  | float stack op => cases op <;> rfl
  | _ => rfl

theorem ExecutableEmission.typed_select_inv {tables C before declared emitted after}
    (head : ExecutableEmission tables C before (.SELECT (some declared)) emitted after) :
    TypedSelectEmission C before (.SELECT (some declared)) emitted after := by
  generalize equal : instr.SELECT (some declared) = source at head
  cases head with
  | scalar h => have tag := h.executable_extension_tag; rw [← equal] at tag; cases tag
  | stateful h => cases h with
    | instruction stack input output op => cases op <;> cases equal
  | indirect h => cases h; cases equal
  | simd h => have tag := h.allowed.executable_extension_tag; rw [← equal] at tag; cases tag
  | typedSelect h => subst equal; exact h
  | branchTable => cases equal

end Itasca.Runtime.Compiler

end

/-! ## ExecutableFunctionContext -/

section

/-!
Transport of executable emission and function certificates across source contexts.

Main declarations: `ExecutableEmission.context` and `ExecutableFunctionCode.complete_module`. A direct consumer is `Store.Invariant.ExecutableInstantiationCode`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

theorem ExecutableEmission.context {tables C D before instruction emitted after}
    (types : D.TYPES=C.TYPES) (functions : D.FUNCS=C.FUNCS) (locals : D.LOCALS=C.LOCALS)
    (globals : D.GLOBALS=C.GLOBALS) (tableTypes : D.TABLES=C.TABLES)
    (memories : D.MEMS=C.MEMS) (elements : D.ELEMS=C.ELEMS)
    (datas : ∀ index : Nat, C.DATAS[index]?=some datatype.OK → D.DATAS[index]?=some datatype.OK)
    (emission : ExecutableEmission tables C before instruction emitted after) :
    ExecutableEmission tables D before instruction emitted after := by
  cases emission with
  | scalar head => exact .scalar (head.context locals globals memories)
  | stateful head =>
    cases head with
    | instruction stack input output op signature first second a b entry firstSlot secondSlot arguments pair =>
      exact .stateful (.instruction stack input output op
        (signature.context functions tableTypes memories elements datas)
        first second a b entry (by simpa only [locals] using firstSlot) secondSlot arguments pair)
  | indirect head => exact .indirect (head.context types locals tableTypes)
  | simd head => exact .simd (head.context memories.symm locals.symm)
  | typedSelect head =>
    cases head with
    | select front ty left right condition leftPos rightPos conditionPos =>
      exact .typedSelect (.select front ty left right condition (by simpa only [locals] using leftPos) rightPos conditionPos)
  | branchTable => exact .branchTable _ _ _ _ _ _

theorem ExecutableFunctionCode.context {C D params declared results body compiled epilogue}
    (certificate : ExecutableFunctionCode C params declared results body compiled epilogue)
    (types : D.TYPES=C.TYPES) (functions : D.FUNCS=C.FUNCS) (locals : D.LOCALS=C.LOCALS)
    (globals : D.GLOBALS=C.GLOBALS) (tableTypes : D.TABLES=C.TABLES)
    (memories : D.MEMS=C.MEMS) (elements : D.ELEMS=C.ELEMS)
    (datas : ∀ index : Nat, C.DATAS[index]?=some datatype.OK → D.DATAS[index]?=some datatype.OK) :
    ExecutableFunctionCode D params declared results body compiled epilogue := by
  obtain ⟨localTypes,certificate⟩ := certificate
  refine ⟨locals.trans localTypes,?_⟩
  rw [types,functions]
  exact ⟨certificate.signature,certificate.locals,certificate.parameterSlots,certificate.localSlots,
    certificate.capacity,certificate.fetchBound,certificate.checked,
    certificate.bodyCode.map_emission (fun _ _ _ _ h => h.context types functions locals globals tableTypes memories elements datas),
    certificate.returnCode,certificate.endPosition⟩

theorem ExecutableFunctionCode.complete_module {module params declared results body compiled epilogue}
    (certificate : ExecutableFunctionCode
      (sourceFunctionContext module.module.env (params++declared) results)
      params declared results body compiled epilogue)
    (count : ∀ declared, module.module.env.data_count=some declared →
      declared.val=module.module.tail.data.val.length) :
    ExecutableFunctionCode (moduleFunctionContext module (params++declared) results)
      params declared results body compiled epilogue := by
  apply certificate.context (D:=moduleFunctionContext module (params++declared) results) rfl rfl rfl rfl rfl rfl rfl
  intro index found
  change (List.replicate module.module.tail.data.val.length datatype.OK)[index]?=some _
  change (Itasca.EnvTranslation.dataTypes module.module.env)[index]?=some _ at found
  cases declaredCount : module.module.env.data_count with
  | none => simp [Itasca.EnvTranslation.dataTypes,declaredCount] at found
  | some n => simpa only [Itasca.EnvTranslation.dataTypes,declaredCount,Option.map_some,
      Option.getD_some,count n declaredCount] using found
end Itasca.Runtime.Compiler

end

/-! ## RecordingEmission -/

section

/-!
The emitted call-tag shape needed for exact event recording.

Main declarations: `callTag` and `RecordingEmissionShape`. A direct consumer is `Interp.Relations.StepRecordingInversion`.
-/

namespace Itasca.Runtime.Compiler
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

theorem integer_instruction_call_tag (op : SourceMachine.Numeric.Instruction) (dst a b : U32) :
    callTag (integerInstruction op dst a b)=0 := by
  cases op with
  | binary ty operator => cases ty <;> cases operator <;> (try (rename_i sign; cases sign)) <;> rfl
  | compare ty operator => cases ty <;> cases operator <;> (try (rename_i sign; cases sign)) <;> rfl
  | unary ty operator => cases ty <;> cases operator <;> rfl
  | eqz ty => cases ty <;> rfl
  | conversion operator => cases operator <;> rfl

theorem float_instruction_call_tag (op : SourceMachine.Float.Instruction) (dst a b : U32) :
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
  | numeric stack op a b left right => exact .singleton _ _ (integer_instruction_call_tag ..)
  | localGet | localSet | localTee =>
    apply RecordingEmissionShape.singleton
    simp only [move]
    split <;> rfl
  | _ => exact .singleton _ _ rfl

theorem ScalarEmission.recording_shape {C before source emitted after}
    (head : ScalarEmission C before source emitted after) : RecordingEmissionShape source emitted := by
  cases head with
  | linear head => exact head.recording_shape
  | float => exact .singleton _ _ (float_instruction_call_tag ..)
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
end Itasca.Runtime.Compiler

end
