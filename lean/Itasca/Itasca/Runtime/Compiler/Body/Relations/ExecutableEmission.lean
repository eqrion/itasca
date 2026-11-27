import Itasca.Runtime.Compiler.Body.Definitions
import Itasca.Runtime.Compiler.Body.Control.BranchesAndDormantEntry
import Itasca.Runtime.Compiler.Local.Lowering.Simd.Emission
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables
import Itasca.Runtime.Compiler.Local.Source.InstructionSourceAndEntry
import Itasca.Runtime.Compiler.Local.Control.FunctionAssembly
import Itasca.Runtime.Compiler.Local.Relations.Function.RootLabel
import Itasca.Support.Translation
import Itasca.Runtime.Compiler.Body.Simd.EmissionTags
import Itasca.Runtime.SourceMachine.EntryAndBranchTables
import Itasca.Runtime.Compiler.Local.Lowering.Simd.ConstructionChecks
import Itasca.Runtime.Compiler.Local.Capacity.SimdAuxiliaryGrowth
import Itasca.Runtime.Compiler.Body.Reader.Calls.Instructions
import Itasca.Runtime.Compiler.Body.Relations.Entry.EntryLayout
import Itasca.Runtime.Compiler.Local.Relations.Calls.IndirectAndStatefulCallbacks
import Itasca.Runtime.Compiler.Local.Relations.Calls.BranchAndCallMetadata

open WebAssembly

/-!
Proofs for Runtime / Compiler / Body / Relations.

This module collects ExecutableEmission, IndirectCalls.
Each section documents its contracts and consumers.
-/

/-! ## ExecutableEmission -/

section

open Itasca.Representation

/-! ## ExecutableEmission -/

section

/-!
Every emitted ordinary instruction, with the function-local index-pair, SIMD and constant tables it uses, and the branch-table control gate. A branch-table gate can only enter `StructuredCode` through its structural constructor, which retains the actual target-table layout.

Main declarations: `ExecutableEmission`.
-/

namespace Itasca.Compiler
open Aeneas.Std

instance (tables C) : OrdinaryEmbedding tables.indirect C (ExecutableEmission tables C) :=
  ⟨.scalar, .stateful, .indirect⟩
instance (tables C) : SimdEmbedding tables.simd tables.constants C (ExecutableEmission tables C) :=
  ⟨.simd⟩

end Itasca.Compiler

end

/-! ## ExecutableFunction -/

section

/-!
Complete Wasm function certificate, including typed SELECT, BR_TABLE and the actual function-local SIMD and target tables.

Main declarations: `ExecutableFunctionCode` and `DefinedExecutableFunctionCode`.
-/

namespace Itasca.Compiler

/-- Complete Wasm function certificate, including typed SELECT,
BR_TABLE and the actual function-local SIMD and target tables. -/
abbrev ExecutableFunctionCode := IndexedFunctionCode ExecutableEmission
end Itasca.Compiler

end

/-! ## ExecutableModuleFunctions -/

section

/-!
The executable-function certificate for a compiled module.

Main declarations: `ExecutableModuleFunctions`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

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
end Itasca.Compiler

end

/-! ## ExecutableProjection -/

section

/-!
Inversion of complete emission into its operation-family cases.

Main declarations: `LinearEmission.executable_extension_tag` and `ExecutableEmission.typed_select_inv`.
-/

namespace Itasca.Compiler
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

end Itasca.Compiler

end

/-! ## ExecutableFunctionContext -/

section

/-!
Transport of executable emission and function certificates across source contexts.

Main declarations: `ExecutableEmission.context` and `ExecutableFunctionCode.complete_module`.
-/

namespace Itasca.Compiler
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
  change (Itasca.Translation.Environment.dataTypes module.module.env)[index]?=some _ at found
  cases declaredCount : module.module.env.data_count with
  | none => simp [Itasca.Translation.Environment.dataTypes,declaredCount] at found
  | some n => simpa only [Itasca.Translation.Environment.dataTypes,declaredCount,Option.map_some,
      Option.getD_some,count n declaredCount] using found
end Itasca.Compiler

end

/-! ## RecordingEmission -/

section

/-!
The emitted call-tag shape needed for exact event recording.

Main declarations: `callTag` and `RecordingEmissionShape`.
-/

namespace Itasca.Compiler
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
end Itasca.Compiler

end

end

/-! ## IndirectCalls -/

section

open Itasca.Representation

/-!
Indirect-call signature selection, callback effects and lowering certificates used by reader replay.
-/

/-! ## Indirect Call Effects -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body

/-- Successful indirect-call checking exposes the actual function/table metadata
and full parameter/result transfer, before any compiler callback. -/
theorem indirect_call_effect (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (outer segment : List code.StackType)
    (hvals : st.core.vals.val = outer ++ segment)
    (hbase : (Body.Control.base st.core).val = outer.length) :
    code.call st data env true ⦃ r => r.1 = .Ok () →
      ∃ (idx table : U32) (middle : Usize) (ft : wasm_types.FuncType) (tt : wasm_types.TableType) (rest : List code.StackType),
        Binary.Leb128.Decoded data st.core.pos idx middle ∧ Binary.Leb128.Decoded data middle table r.2.core.pos ∧
        env.types.val[idx.val]? = some ft ∧ env.table_types.val[table.val]? = some tt ∧ tt.elem = .FuncRef ∧
        r.2.core.vals.val = outer ++ (rest ++ ft.results.val.map code.StackType.Val) ∧
        (∀ ts, Body.Stack.Realizes (Body.Control.polymorphic st.core) rest ts →
          Body.Stack.Realizes (Body.Control.polymorphic st.core) segment
            (ts ++ (ft.params.val.map Translation.valueType ++ [.I32]))) ⦄ := by
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  cases r with
  | Err e => simp [code.call, code.call_indirect_info, code.take_index, hr,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨idx, middle⟩ := pair
    obtain ⟨rtable, hreadtable, hdtable⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data middle)
    cases rtable with
    | Err e => simp [code.call, code.call_indirect_info, code.take_index, hr, hreadtable,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      obtain ⟨table, next⟩ := pair
      by_cases htable : table.val < env.table_types.val.length
      · have htix : (UScalar.cast .Usize table).val < env.table_types.val.length := by simpa using htable
        obtain ⟨tt, hget, hgeteq⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.index_usize_spec env.table_types (UScalar.cast .Usize table) htix)
        have htt : env.table_types.val[table.val] = tt := by simpa using hgeteq.symm
        have htablesmall := Nat.not_le_of_gt htable
        cases helem : tt.elem with
        | ExternRef =>
          simp [code.call, code.call_indirect_info, code.take_index, hr, hreadtable, lift,
            htablesmall, hget, helem, Itasca.wasm_types.ElemType.value_type,
            core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
            Itasca.wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq,
            core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | FuncRef =>
          have hfun : env.table_types.val[table.val].elem = .FuncRef := by rw [htt]; exact helem
          by_cases hi : idx.val < env.types.val.length
          · have hix : (UScalar.cast .Usize idx).val < env.types.val.length := by simpa using hi
            obtain ⟨ft, hft, heq⟩ := WP.spec_imp_exists
              (alloc.vec.Vec.index_usize_spec env.types (UScalar.cast .Usize idx) hix)
            have htype : env.types.val[idx.val] = ft := by simpa using heq.symm
            have hsmall := Nat.not_le_of_gt hi
            obtain ⟨⟨rc, sc⟩, hcond, hcc, hpc, condrest, hvc, _, htc⟩ := WP.spec_imp_exists
              (code.pop_with_type.realizes { st.core with pos := next } outer segment .I32 hvals hbase)
            dsimp only at hcc hpc hvc htc
            cases rc with
            | Err e =>
              simp [code.call, code.call_indirect_info, code.take_index, hr, hreadtable, lift,
                htablesmall, hget, helem, Itasca.wasm_types.ElemType.value_type,
                core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
                Itasca.wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq, hsmall, hcond,
                core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok popped =>
              obtain ⟨⟨res, s⟩, hs, hout⟩ := WP.spec_imp_exists
                (code.apply_func_type.realizes sc ft outer condrest hvc
                  (by simpa [Body.Control.base, hcc] using hbase))
              cases res with
              | Err e =>
                simp [code.call, code.call_indirect_info, code.take_index, hr, hreadtable, lift,
                  htablesmall, hget, helem, Itasca.wasm_types.ElemType.value_type,
                  core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
                  Itasca.wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq, hsmall, hcond, hft, hs,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
              | Ok u =>
                obtain ⟨hc, hp, _, _, rest, hv, _, ht⟩ := hout rfl
                dsimp only at hc hp hv ht
                have htransfer : ∀ ts, Body.Stack.Realizes (Body.Control.polymorphic st.core) rest ts →
                    Body.Stack.Realizes (Body.Control.polymorphic st.core) segment
                      (ts ++ (ft.params.val.map Translation.valueType ++ [.I32])) := by
                  intro ts hts
                  have hparam := ht ts (by simpa [Body.Control.polymorphic, hcc] using hts)
                  have hargs := htc.2 _ (by simpa [Body.Control.polymorphic, hcc] using hparam)
                  simpa [Translation.valueType, List.append_assoc, Body.Control.polymorphic] using hargs
                rw [WP.spec_equiv_exists]
                refine ⟨(.Ok (), ⟨s⟩), ?_, fun _ => ?_⟩
                · simp [code.call, code.call_indirect_info, code.take_index, hr, hreadtable, lift,
                    htablesmall, hget, helem, Itasca.wasm_types.ElemType.value_type,
                    core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
                    Itasca.wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq, hsmall, hcond, hft, hs,
                    core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                · refine ⟨idx,table,middle,ft,tt,rest,hd,?_,?_,?_,helem,hv,htransfer⟩
                  · simpa [Binary.Leb128.Post,hp,hpc] using hdtable
                  · simpa [List.getElem?_eq_getElem hi] using congrArg some htype
                  · simpa [List.getElem?_eq_getElem htable] using congrArg some htt
          · have hlarge := Nat.le_of_not_gt hi
            simp [code.call, code.call_indirect_info, code.take_index, hr, hreadtable, lift,
              htablesmall, hget, helem, Itasca.wasm_types.ElemType.value_type,
              core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
              Itasca.wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq, hlarge,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · have hlarge := Nat.le_of_not_gt htable
        simp [code.call, code.call_indirect_info, code.take_index, hr, hreadtable, lift,
          hlarge, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Concrete live stacks and the actual reader determine the complete indirect
call signature and operand/result suffixes. -/
theorem reader_indirect_call_stack (st out : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (index table : U32) (outer segment : List code.StackType)
    (values : st.core.vals.val = outer ++ segment) (base : (Body.Control.base st.core).val = outer.length)
    (known : ConcreteStack st.core.vals.val) (monomorphic : Body.Control.polymorphic st.core = false)
    (shape : Body.Control.Shape st.core)
    (accepted : code.call_indirect_info st data env = .ok (.Ok (index,table),out)) :
    ∃ (ft : wasm_types.FuncType) (tt : wasm_types.TableType) (front : List wasm_types.ValueType),
      env.types.val[index.val]? = some ft ∧ env.table_types.val[table.val]? = some tt ∧ tt.elem = .FuncRef ∧
      Body.Stack.stackTypes st.core.vals.val = (front.map Translation.valueType ++ ft.params.val.map Translation.valueType) ++ [.I32] ∧
      out.core.vals.val = (front ++ ft.results.val).map code.StackType.Val := by
  have erased : code.call st data env true = .ok (.Ok (),out) := by
    simp [code.call,accepted,core.result.Result.Insts.CoreOpsTry.branch]
  have effect := indirect_call_effect st data env outer segment values base
  rw [erased,WP.spec_ok] at effect
  obtain ⟨idx,tab,middle,ft,tt,rest,decoded,decodedTable,typeFound,tableFound,elem,afterValues,transfer⟩ := effect rfl
  dsimp only at decoded decodedTable afterValues
  have info := code.call_indirect_info.bytes st data env shape
  rw [accepted,WP.spec_ok] at info
  obtain ⟨middle',indexBytes,tableBytes⟩ := info index table rfl
  obtain ⟨rfl,rfl⟩ := Binary.Leb128.Decoded.deterministic data st.core.pos index idx middle' middle indexBytes decoded
  obtain ⟨rfl,_⟩ := Binary.Leb128.Decoded.deterministic data middle' table tab out.core.pos out.core.pos tableBytes decodedTable
  rw [monomorphic] at transfer
  obtain ⟨front,beforeTypes,afterConcrete⟩ := call_full_stack_types (ft.params.val ++ [.I32]) ft.results.val known values afterValues
    (by simpa [List.map_append,Translation.valueType] using transfer)
  refine ⟨ft,tt,front,typeFound,tableFound,elem,?_,afterConcrete⟩
  simpa [List.map_append,Translation.valueType,List.append_assoc] using beforeTypes
end Itasca.Compiler

end

/-! ## Indirect Call Signature -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- The captured table supplies an actual readable signature at every canonical
source type index; its parameter width is derived from the captured sequence. -/
theorem SignatureSequence.indirect_call {signatures : Slice runtime.compiler.Signature}
    {types : List Itasca.wasm_types.FuncType} (sequence : SignatureSequence signatures.val types)
    (index : U32) (params results : List valtype)
    (source : (types.map Itasca.Translation.Environment.funcType)[index.val]? = some ⟨.mk_list params,.mk_list results⟩) :
    ∃ signature, Slice.index_usize signatures (UScalar.cast .Usize index) = .ok signature ∧
      SignatureMatches signature params results := by
  have inBounds : index.val < types.length := by
    have found := (List.getElem?_eq_some_iff.mp source).1
    simpa using found
  have signatureBound : index.val < signatures.val.length := by
    rw [List.Forall₂.length_eq sequence]; exact inBounds
  let signature := signatures.val[index.val]
  have found : signatures.val[index.val]? = some signature := List.getElem?_eq_getElem signatureBound
  obtain ⟨input,output,lookup,matched⟩ := sequence.table index.val signature found
  have same : params = input ∧ results = output := by
    rw [source] at lookup
    simpa only [Option.some.injEq,functype.mk_functype.injEq,list.mk_list.injEq] using lookup
  obtain ⟨r,read,result⟩ := WP.spec_imp_exists
    (Slice.index_usize_spec signatures (UScalar.cast .Usize index) (by simpa using signatureBound))
  refine ⟨signature,?_,?_⟩
  · have equal : r = signature := by simpa [signature] using result
    simpa only [equal] using read
  · simpa only [same.1,same.2] using matched
end Itasca.Compiler

end

/-! ## Indirect Call Lowered -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Successful indirect-call lowering appends the exact table/type pair and
emits the source-determined selector and argument coordinates. -/
theorem compiler_indirect_call_emission {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.wasm_types.ValueType)
    (C : context) (front params results : List valtype) (typeIndex tableIndex : U32)
    (bounds : limits) (signature : runtime.compiler.Signature)
    (signatureFound : C.TYPES[typeIndex.val]? = some ⟨.mk_list params,.mk_list results⟩)
    (tableFound : C.TABLES[tableIndex.val]? = some (.mk_tabletype bounds .FUNCREF))
    (read : Slice.index_usize before.signatures (UScalar.cast .Usize typeIndex) = .ok signature)
    (parameterWidth : signature.param_slots.val = slots params)
    (locals : C.LOCALS = compilerLocals before)
    (layout : CompilerLayout before ((front ++ params) ++ [.I32]))
    (reachable : before.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translation.valueType = front ++ results)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 17#u16 typeIndex tableIndex 0#u128 = .ok (.Ok (),after)) :
    after.function.indirect.val = before.function.indirect.val ++ [(tableIndex,typeIndex)] ∧
    ∃ instruction, Lowered before after instruction (front ++ results) ∧
      IndirectCallEmission after.function.indirect.val C ((front ++ params) ++ [.I32])
        (.CALL_INDIRECT (.mk_uN tableIndex.val) (.mk_uN typeIndex.val)) [instruction] (front ++ results) := by
  obtain ⟨total,base,added,subtracted,basePosition⟩ := indirect_call_arithmetic before front params signature layout parameterWidth
  obtain ⟨entry,paired,pairRun⟩ := lower_indirect_call_pair_success ops before after state typeIndex tableIndex total base
    signature reachable read added subtracted accepted
  obtain ⟨budget,pairs,pairedEq,pairsEq,indexEq⟩ := compiler_pair_success ops law before paired tableIndex typeIndex entry pairRun
  subst paired
  let paired := {before with budget, function := {before.function with indirect := pairs}}
  have pairedLayout : CompilerLayout paired ((front ++ params) ++ [.I32]) :=
    ⟨layout.localSlots,layout.localOffsets,layout.operandOffsets,layout.height,layout.capacity⟩
  obtain ⟨index,operand,indexPosition⟩ := indirect_call_operand ops paired front params pairedLayout
  rw [lower_indirect_call_eq ops before paired state typeIndex tableIndex total base entry index signature
    reachable read added subtracted pairRun operand] at accepted
  have lowered := finish_op ops law paired state types (.CallIndirect entry index base)
    _ pairedLayout concrete codeFits sourceFits coordinateFits
  rw [accepted,WP.spec_ok] at lowered
  have kept := compiler_finish_indirect ops law paired after state _ accepted
  have afterPairs : after.function.indirect.val = before.function.indirect.val ++ [(tableIndex,typeIndex)] := by
    rw [kept]; exact pairsEq
  refine ⟨afterPairs,.CallIndirect entry index base,?_,?_⟩
  · simpa only [typed,Lowered,paired,compilerLocals] using lowered rfl
  · apply IndirectCallEmission.call front params results typeIndex tableIndex entry index base bounds
      signatureFound tableFound
    · rw [afterPairs,indexEq]; simp
    · simpa only [locals] using basePosition
    · simp only [paired,compilerLocals] at indexPosition basePosition
      omega
/-- The public compiler-side constructor reads signature metadata from the actual
captured source sequence, rather than assuming a width or a successful lookup. -/
theorem compiler_indirect_call_emission_captured {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.wasm_types.ValueType)
    (sourceTypes : List Itasca.wasm_types.FuncType) (sequence : SignatureSequence before.signatures.val sourceTypes)
    (C : context) (contextTypes : C.TYPES = sourceTypes.map Itasca.Translation.Environment.funcType)
    (front params results : List valtype) (typeIndex tableIndex : U32) (bounds : limits)
    (signatureFound : C.TYPES[typeIndex.val]? = some ⟨.mk_list params,.mk_list results⟩)
    (tableFound : C.TABLES[tableIndex.val]? = some (.mk_tabletype bounds .FUNCREF))
    (locals : C.LOCALS = compilerLocals before)
    (layout : CompilerLayout before ((front ++ params) ++ [.I32]))
    (reachable : before.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translation.valueType = front ++ results)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 17#u16 typeIndex tableIndex 0#u128 = .ok (.Ok (),after)) :
    after.function.indirect.val = before.function.indirect.val ++ [(tableIndex,typeIndex)] ∧
    ∃ instruction, Lowered before after instruction (front ++ results) ∧
      IndirectCallEmission after.function.indirect.val C ((front ++ params) ++ [.I32])
        (.CALL_INDIRECT (.mk_uN tableIndex.val) (.mk_uN typeIndex.val)) [instruction] (front ++ results) := by
  obtain ⟨signature,read,matched⟩ := sequence.indirect_call typeIndex params results (by simpa only [contextTypes] using signatureFound)
  exact compiler_indirect_call_emission ops law before after state types C front params results typeIndex tableIndex bounds
    signature signatureFound tableFound read matched.paramWords locals layout reachable concrete typed
    codeFits sourceFits coordinateFits accepted
end Itasca.Compiler

end

end
