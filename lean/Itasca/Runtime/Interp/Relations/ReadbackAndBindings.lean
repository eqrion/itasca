import Itasca.Runtime.Interp.Recording
import Itasca.Runtime.Interp.Relations.SlotsAndDefaults
import Itasca.Runtime.Interp.Relations.Regions
import Itasca.Runtime.SourceMachine.EntryAndBranchTables
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.Representation.Store
import Itasca.Runtime.Interp.Calls.ReturnRefinement
import Itasca.Runtime.Compiler.Local.Relations.Function.RootLabel
import Itasca.Runtime.SourceMachine.StructureAndTyping
import Itasca.Runtime.SourceMachine.Sim.Structured

/-!
Proofs for Runtime / Interp / Relations.

This module collects ReadbackAndBindings, FrameStoreMetadata.
Each section documents its contracts and consumers.
-/

/-! ## ReadbackAndBindings -/

section

open Itasca.Representation

/-!
# Readback And Bindings

Machine readback and suspended-point bindings agree with the retained source state.
-/

/-! ## Readback -/

section

/-! Recover specification values from represented live result slots. -/
namespace Itasca.Interp
open Aeneas Aeneas.Std

def readPair (words : List U64) (position : Nat) (ty : Itasca.wasm_types.ValueType) : U64 × U64 :=
  (words[position]!, if Itasca.Translation.valueType ty = .V128 then words[position + 1]! else 0#u64)

theorem WordsAt.read_pair {words : List U64} {position : Nat} {bits : List Nat}
    (ty : Itasca.wasm_types.ValueType) (represented : WordsAt words position bits)
    (length : bits.length = Representation.width (Itasca.Translation.valueType ty)) :
    pairWords ty (readPair words position ty) = bits := by
  by_cases hv : Itasca.Translation.valueType ty = .V128
  · have hl : bits.length = 2 := by simpa [hv, Representation.width] using length
    apply List.ext_getElem
    · simp [pairWords, hv, hl]
    · intro i hi hb
      have hm : i = 0 ∨ i = 1 := by omega
      rcases hm with rfl | rfl
      · have h := (represented 0 hb).2
        simpa [pairWords, Itasca.Interp.readPair, hv, _root_.getElem!_pos bits 0 hb] using h
      · have h := (represented 1 hb).2
        simpa [pairWords, Itasca.Interp.readPair, hv, _root_.getElem!_pos bits 1 hb] using h
  · have hw : Representation.width (Itasca.Translation.valueType ty) = 1 := by cases ty <;> simp_all [Itasca.Translation.valueType, Representation.width]
    have hl : bits.length = 1 := length.trans hw
    apply List.ext_getElem
    · simp [pairWords, hv, hl]
    · intro i hi hb
      have hz : i = 0 := by omega
      subst i
      have h := (represented 0 hb).2
      simpa [pairWords, Itasca.Interp.readPair, hv, _root_.getElem!_pos bits 0 hb] using h

theorem encode_value_f32_low (value : val) (wellFormed : wf_val value)
    (typed : Representation.valueType value = .F32) : (Representation.encodeValue value)[0]! < 2^32 := by
  cases wellFormed with
  | val_case_0 ty value hv =>
    cases hv with
    | num__case_0 kind bits _ hb hty =>
      subst ty
      cases kind <;> simp [Representation.valueType, valtype_numtype, numtype_Inn, numtype_Fnn] at typed
    | num__case_1 kind value hv hty =>
      subst ty
      cases kind with
      | F32 =>
        change SpecExt.Builtins.floatBits 32 value < 2^32
        exact SpecExt.Builtins.Float.float_bits_lt_32 value hv
      | F64 => simp [Representation.valueType, valtype_numtype, numtype_Inn, numtype_Fnn] at typed
  | val_case_1 ty value _ _ => simp [Representation.valueType] at typed
  | val_case_2 ty => cases ty <;> simp [Representation.valueType] at typed
  | val_case_3 address => simp [Representation.valueType] at typed
  | val_case_4 address => simp [Representation.valueType] at typed

/-- Reference words fit usize before the decoder subtracts the null sentinel.
The store's issued-address bounds establish this condition for live results. -/
def ResultIndexFits : val → Prop
  | .REF_FUNC_ADDR address | .REF_HOST_ADDR address => address + 1 ≤ Usize.max
  | _ => True

theorem encode_value_reference_low (value : val) (fits : ResultIndexFits value)
    (typed : Representation.valueType value = .FUNCREF ∨ Representation.valueType value = .EXTERNREF) :
    (Representation.encodeValue value)[0]! ≤ Usize.max := by
  cases value with
  | CONST ty n => cases ty <;> simp [Representation.valueType, valtype_numtype, numtype_Inn, numtype_Fnn] at typed
  | VCONST ty n => simp [Representation.valueType] at typed
  | REF_NULL ty => simp [Representation.encodeValue]
  | REF_FUNC_ADDR address | REF_HOST_ADDR address => simpa [Representation.encodeValue, ResultIndexFits] using fits

@[step] theorem decode_slot_represents (slots : Slice U64) (position : Usize)
    (ty : Itasca.wasm_types.ValueType) (store : Usize) (value : val)
    (wellFormed : wf_val value) (typed : Itasca.Translation.valueType ty = Representation.valueType value)
    (represented : WordsAt slots.val position.val (Representation.encodeValue value))
    (bound : position.val + Representation.width (Itasca.Translation.valueType ty) ≤ slots.length)
    (floatBound : ty = .F32 → slots.val[position.val]!.val < 2^32)
    (referenceBound : ty = .FuncRef ∨ ty = .ExternRef → slots.val[position.val]!.val ≤ Usize.max) :
    runtime.interp.decode_slot slots position ty store ⦃ result =>
      rawType result = ty ∧ sourceValue result = value ⦄ := by
  let pair := readPair slots.val position.val ty
  have hp : pairWords ty pair = Representation.encodeValue value :=
    represented.read_pair ty (by rw [Representation.encode_value_length, ← typed])
  obtain ⟨result, hd, hty, hv⟩ := WP.spec_imp_exists
    (decode_value_represents ty pair.1 pair.2 store value wellFormed typed hp floatBound referenceBound)
  step with decode_slot_spec slots position ty store pair.1 pair.2 result bound rfl (by simp only [pair, Itasca.Interp.readPair]; split <;> simp_all) hd
    as ⟨actual, ha⟩
  simpa [ha] using And.intro hty hv

/-- The live-value representation supplies the decoder's numeric bounds;
only the independent issued-address bound remains explicit. -/
@[step] theorem decode_slot_value (slots : Slice U64) (position : Usize)
    (ty : Itasca.wasm_types.ValueType) (store : Usize) (value : val)
    (wellFormed : wf_val value) (typed : Itasca.Translation.valueType ty = Representation.valueType value)
    (represented : WordsAt slots.val position.val (Representation.encodeValue value))
    (fits : ResultIndexFits value) :
    runtime.interp.decode_slot slots position ty store ⦃ result =>
      rawType result = ty ∧ sourceValue result = value ⦄ := by
  have length : (Representation.encodeValue value).length = Representation.width (Itasca.Translation.valueType ty) := by
    rw [Representation.encode_value_length, ← typed]
  have positive := Representation.width_positive (Itasca.Translation.valueType ty)
  have first : slots.val[position.val]!.val = (Representation.encodeValue value)[0]! := by
    simpa using (represented 0 (by omega)).2
  have bound : position.val + Representation.width (Itasca.Translation.valueType ty) ≤ slots.length := by
    have last := (represented ((Representation.encodeValue value).length - 1) (by omega)).1
    change position.val + Representation.width (Itasca.Translation.valueType ty) ≤ slots.val.length
    omega
  apply decode_slot_represents slots position ty store value wellFormed typed represented bound
  · intro ht
    rw [first]
    apply encode_value_f32_low value wellFormed
    simpa [ht, Itasca.Translation.valueType] using typed.symm
  · intro ht
    rw [first]
    apply encode_value_reference_low value fits
    rcases ht with rfl | rfl
    · exact Or.inl typed.symm
    · exact Or.inr typed.symm

end Itasca.Interp

end

/-! ## ReferenceArguments -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std

/-- A retained source reference bound discharges the concrete result decoder's
usize conversion, including its nonzero reference sentinel. -/
theorem result_index_fits_of_reference_bound (value : val)
    (bounded : SourceMachine.ReferenceBound Usize.max value) : ResultIndexFits value := by
  cases value <;> simp_all [SourceMachine.ReferenceBound, ResultIndexFits] <;> omega

end Itasca.Interp

end

/-! ## FrameBindings -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std

/-- The module bound to the active source frame is the decoded instance found
by the concrete frame's instance index. -/
theorem FrameBinding.module_lookup {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {raw : runtime.interp.Frame} {source : SourceMachine.AFrame}
    (binding : FrameBinding store exec raw source) (inst : runtime.store.ModuleInst)
    (lookup : store.instances.val[raw.instance.val]? = some inst) :
    source.module = Representation.decodeInstance store inst := by
  obtain ⟨actual, fn, compiled, signature, _, _, found, _, _, _, _, moduleEq, _⟩ := binding
  have same : actual = inst := Option.some.inj (found.symm.trans lookup)
  exact same ▸ moduleEq

/-- Raw direct-call lookup and source CALL lookup use the identical retained
instance function map. -/
theorem FrameBinding.resolve_call {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {raw : runtime.interp.Frame} {source : SourceMachine.AFrame}
    (binding : FrameBinding store exec raw source) (inst : runtime.store.ModuleInst)
    (lookup : store.instances.val[raw.instance.val]? = some inst)
    (index : Nat) (address : runtime.FuncAddr)
    (found : inst.funcs.val[index]? = some address) :
    source.module.FUNCS[index]? = some address.index.val := by
  rw [binding.module_lookup inst lookup]
  simp only [Representation.decodeInstance, List.getElem?_map, found, Option.map_some]

/-- A concrete defined-function entry selects precisely the retained source
body and owning module in the decoded store. -/
theorem defined_function_lookup {M : Type} (view : M → Slice U8)
    (code : Representation.CodeInterpretation) (store : runtime.store.Store M)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (signature : Itasca.wasm_types.FuncType) (instanceIndex functionIndex : Usize)
    (inst : runtime.store.ModuleInst) (sourceCode : funccode)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (hi : store.instances.val[instanceIndex.val]? = some inst)
    (hc : code instanceIndex.val inst.module functionIndex.val = sourceCode) :
    (Representation.decodeStore view code store).FUNCS[address.index.val]? =
      some ⟨Itasca.Translation.Environment.funcType signature, Representation.decodeInstance store inst, sourceCode⟩ := by
  simp [Representation.decodeStore, Representation.decodeFunction, List.getD_eq_getElem?_getD, hf, hs, hw, hi, hc]

end Itasca.Interp

end

/-! ## SuspendedPoint -/

section

namespace Itasca.Interp
open Aeneas.Std

/-- Appending returned values leaves every saved outer label prefix intact. -/
theorem LabelsMatch.append {values : List val} {labels targets}
    (matching : LabelsMatch values labels targets) (results : List val)
    (heights : ∀ label ∈ labels, label.height ≤ values.length) :
    LabelsMatch (values ++ results) labels targets := by
  apply matching.reprefix
  intro label member
  exact (List.take_append_of_le_length (heights label member)).symm

end Itasca.Interp

end

end

/-! ## FrameStoreMetadata -/

section

open Itasca.Representation

/-! ## CompiledFunctions -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std

/-- A frame's retained signature list belongs to its actual instance. -/
theorem FrameProgram.function_table {M : Type} {store : runtime.store.Store M}
    {raw compiled locals results functions}
    (program : FrameProgram store raw compiled locals results functions)
    (inst : runtime.store.ModuleInst)
    (lookup : store.instances.val[raw.instance.val]? = some inst) :
    FunctionTable store inst functions := by
  obtain ⟨actual, found, _, table⟩ := program.lookup
  have same : actual = inst := Option.some.inj (found.symm.trans lookup)
  exact same ▸ table

/-- Resolving a compiler CALL signature exposes the exact issued raw address,
function entry, and canonical signature consumed by interpreter dispatch. -/
theorem FrameProgram.resolve_call {M : Type} {store : runtime.store.Store M}
    {raw compiled locals results functions}
    (program : FrameProgram store raw compiled locals results functions)
    (inst : runtime.store.ModuleInst)
    (lookup : store.instances.val[raw.instance.val]? = some inst)
    (index : Nat) (ty : functype) (signature : functions[index]? = some ty) :
    ∃ address function rawType, inst.funcs.val[index]? = some address ∧
      address.store = store.id ∧ store.funcs.val[address.index.val]? = some function ∧
      store.types.val[function.signature.val]? = some rawType ∧ Itasca.Translation.Environment.funcType rawType = ty :=
  (program.function_table inst lookup).resolve index ty signature

end Itasca.Interp

end

/-! ## ControlPoint -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std

/-- Simulation counts positive SpecTec reductions and explicitly measures all
concrete administrative dispatches. -/
def ConcreteSim (codeLength : Nat) (beforePC afterPC : Nat) (beforePending afterPending : Bool)
    (before after : SourceMachine.AState) : Prop :=
  (SourceMachine.decode before = SourceMachine.decode after ∧
    dispatchMeasure afterPending codeLength afterPC after < dispatchMeasure beforePending codeLength beforePC before) ∨
  ∃ n, 0 < n ∧ Spec.StepsHN n (SourceMachine.decode before) [] (SourceMachine.decode after)

theorem dispatch_measure_source_any {before after : SourceMachine.AState}
    (beforePending afterPending : Bool) (codeLength pc target : Nat)
    (decrease : SourceMachine.administrativeMeasure after < SourceMachine.administrativeMeasure before) :
    dispatchMeasure afterPending codeLength target after < dispatchMeasure beforePending codeLength pc before := by
  have adjacent : SourceMachine.administrativeMeasure after + 1 ≤ SourceMachine.administrativeMeasure before := decrease
  have multiplied := Nat.mul_le_mul_right (2 * (codeLength + 1)) adjacent
  simp only [Nat.add_mul, Nat.one_mul] at multiplied
  cases beforePending <;> cases afterPending <;>
    simp only [dispatchMeasure, Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem ConcreteSim.of_source {before after : SourceMachine.AState}
    (codeLength beforePC afterPC : Nat) (beforePending afterPending : Bool)
    (simulation : SourceMachine.NextSim before after) :
    ConcreteSim codeLength beforePC afterPC beforePending afterPending before after := by
  rcases simulation with ⟨same, decrease⟩ | ⟨n, positive, steps⟩
  · exact Or.inl ⟨same, dispatch_measure_source_any beforePending afterPending codeLength beforePC afterPC decrease⟩
  · exact Or.inr ⟨n, positive, steps⟩

end Itasca.Interp

end

/-! ## StackRelation -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std

/-- The compiler's code-length certificate rules out PC increment overflow
whenever the interpreter fetches an actual instruction. -/
theorem FrameProgram.fetched_bound {M : Type} {store : runtime.store.Store M}
    {raw compiled locals results functions} (program : FrameProgram store raw compiled locals results functions)
    (instruction : runtime.bytecode.Instr)
    (fetched : compiled.code.val[raw.pc.val]? = some instruction) : raw.pc.val < U32.max := by
  have bound := (List.getElem?_eq_some_iff.mp fetched).1
  exact lt_of_lt_of_le bound program.fetchBound

end Itasca.Interp

end

/-! ## Store.MetadataPreserved -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std

theorem _root_.Itasca.Store.MetadataPreserved.refl {M : Type} (store : runtime.store.Store M) :
    Store.MetadataPreserved store store := ⟨rfl,rfl,rfl,rfl⟩

theorem _root_.Itasca.Store.MetadataPreserved.decode_instance {M : Type} {before after : runtime.store.Store M}
    (metadata : Store.MetadataPreserved before after) (inst : runtime.store.ModuleInst) :
    Representation.decodeInstance after inst = Representation.decodeInstance before inst := by
  simp only [Representation.decodeInstance, metadata.types]

theorem _root_.Itasca.Representation.FunctionTable.store_metadata {M : Type} {before after : runtime.store.Store M}
    (metadata : Store.MetadataPreserved before after) {inst functions}
    (table : FunctionTable before inst functions) : FunctionTable after inst functions := by
  simpa only [FunctionTable, metadata.identity, metadata.functions, metadata.types] using table

theorem FrameBinding.store_metadata {M : Type} {before after : runtime.store.Store M}
    (metadata : Store.MetadataPreserved before after) {exec raw source}
    (binding : FrameBinding before exec raw source) : FrameBinding after exec raw source := by
  simpa only [FrameBinding, metadata.identity, metadata.functions, metadata.types,
    metadata.instances, metadata.decode_instance] using binding

theorem FrameProgram.store_metadata {M : Type} {before after : runtime.store.Store M}
    (metadata : Store.MetadataPreserved before after) {raw compiled locals results functions}
    (program : FrameProgram before raw compiled locals results functions) :
    FrameProgram after raw compiled locals results functions := by
  refine ⟨?_,program.checked,program.fetchBound,program.localSlots,program.epilogue⟩
  obtain ⟨inst,found,code,table⟩ := program.lookup
  exact ⟨inst,by simpa only [metadata.instances] using found,code,table.store_metadata metadata⟩

end Itasca.Interp

end

end
