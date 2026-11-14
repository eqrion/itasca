import Itasca.Runtime.Interp.ValueSlots
import Itasca.Runtime.Interp.Relations.Defaults
import Itasca.Runtime.Interp.Relations.Regions
import Itasca.Runtime.SourceMachine.BrTable
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Interp.Control.StructuredLinear

/-!
Sections, each formerly its own module: Readback, ReferenceArguments, FrameBindings, SuspendedPoint.
-/

/-! ## Readback -/

section

/-! Recover specification values from represented live result slots. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

def readPair (words : List U64) (position : Nat) (ty : Itasca.wasm_types.ValueType) : U64 × U64 :=
  (words[position]!, if sourceType ty = .V128 then words[position + 1]! else 0#u64)

theorem WordsAt.read_pair {words : List U64} {position : Nat} {bits : List Nat}
    (ty : Itasca.wasm_types.ValueType) (represented : WordsAt words position bits)
    (length : bits.length = Compiler.width (sourceType ty)) :
    pairWords ty (readPair words position ty) = bits := by
  by_cases hv : sourceType ty = .V128
  · have hl : bits.length = 2 := by simpa [hv, Compiler.width] using length
    apply List.ext_getElem
    · simp [pairWords, hv, hl]
    · intro i hi hb
      have hm : i = 0 ∨ i = 1 := by omega
      rcases hm with rfl | rfl
      · have h := (represented 0 hb).2
        simpa [pairWords, Itasca.Runtime.Interp.readPair, hv, _root_.getElem!_pos bits 0 hb] using h
      · have h := (represented 1 hb).2
        simpa [pairWords, Itasca.Runtime.Interp.readPair, hv, _root_.getElem!_pos bits 1 hb] using h
  · have hw : Compiler.width (sourceType ty) = 1 := by cases ty <;> simp_all [sourceType, Compiler.width]
    have hl : bits.length = 1 := length.trans hw
    apply List.ext_getElem
    · simp [pairWords, hv, hl]
    · intro i hi hb
      have hz : i = 0 := by omega
      subst i
      have h := (represented 0 hb).2
      simpa [pairWords, Itasca.Runtime.Interp.readPair, hv, _root_.getElem!_pos bits 0 hb] using h

theorem encode_value_f32_low (value : val) (wellFormed : wf_val value)
    (typed : Compiler.valueType value = .F32) : (Compiler.encodeValue value)[0]! < 2^32 := by
  cases wellFormed with
  | val_case_0 ty value hv =>
    cases hv with
    | num__case_0 kind bits _ hb hty =>
      subst ty
      cases kind <;> simp [Compiler.valueType, valtype_numtype, numtype_Inn, numtype_Fnn] at typed
    | num__case_1 kind value hv hty =>
      subst ty
      cases kind with
      | F32 =>
        change SpecExt.Builtins.floatBits 32 value < 2^32
        exact SpecExt.Builtins.Float.floatBits_lt_32 value hv
      | F64 => simp [Compiler.valueType, valtype_numtype, numtype_Inn, numtype_Fnn] at typed
  | val_case_1 ty value _ _ => simp [Compiler.valueType] at typed
  | val_case_2 ty => cases ty <;> simp [Compiler.valueType] at typed
  | val_case_3 address => simp [Compiler.valueType] at typed
  | val_case_4 address => simp [Compiler.valueType] at typed

/-- Reference words fit usize before the decoder subtracts the null sentinel.
The store's issued-address bounds establish this condition for live results. -/
def ResultIndexFits : val → Prop
  | .REF_FUNC_ADDR address | .REF_HOST_ADDR address => address + 1 ≤ Usize.max
  | _ => True

theorem encode_value_reference_low (value : val) (fits : ResultIndexFits value)
    (typed : Compiler.valueType value = .FUNCREF ∨ Compiler.valueType value = .EXTERNREF) :
    (Compiler.encodeValue value)[0]! ≤ Usize.max := by
  cases value with
  | CONST ty n => cases ty <;> simp [Compiler.valueType, valtype_numtype, numtype_Inn, numtype_Fnn] at typed
  | VCONST ty n => simp [Compiler.valueType] at typed
  | REF_NULL ty => simp [Compiler.encodeValue]
  | REF_FUNC_ADDR address | REF_HOST_ADDR address => simpa [Compiler.encodeValue, ResultIndexFits] using fits

@[step] theorem decode_slot_represents (slots : Slice U64) (position : Usize)
    (ty : Itasca.wasm_types.ValueType) (store : Usize) (value : val)
    (wellFormed : wf_val value) (typed : sourceType ty = Compiler.valueType value)
    (represented : WordsAt slots.val position.val (Compiler.encodeValue value))
    (bound : position.val + Compiler.width (sourceType ty) ≤ slots.length)
    (floatBound : ty = .F32 → slots.val[position.val]!.val < 2^32)
    (referenceBound : ty = .FuncRef ∨ ty = .ExternRef → slots.val[position.val]!.val ≤ Usize.max) :
    runtime.interp.decode_slot slots position ty store ⦃ result =>
      rawType result = ty ∧ sourceValue result = value ⦄ := by
  let pair := readPair slots.val position.val ty
  have hp : pairWords ty pair = Compiler.encodeValue value :=
    represented.read_pair ty (by rw [Compiler.encode_value_length, ← typed])
  obtain ⟨result, hd, hty, hv⟩ := WP.spec_imp_exists
    (decode_value_represents ty pair.1 pair.2 store value wellFormed typed hp floatBound referenceBound)
  step with decode_slot_spec slots position ty store pair.1 pair.2 result bound rfl (by simp only [pair, Itasca.Runtime.Interp.readPair]; split <;> simp_all) hd
    as ⟨actual, ha⟩
  simpa [ha] using And.intro hty hv

/-- The live-value representation supplies the decoder's numeric bounds;
only the independent issued-address bound remains explicit. -/
@[step] theorem decode_slot_value (slots : Slice U64) (position : Usize)
    (ty : Itasca.wasm_types.ValueType) (store : Usize) (value : val)
    (wellFormed : wf_val value) (typed : sourceType ty = Compiler.valueType value)
    (represented : WordsAt slots.val position.val (Compiler.encodeValue value))
    (fits : ResultIndexFits value) :
    runtime.interp.decode_slot slots position ty store ⦃ result =>
      rawType result = ty ∧ sourceValue result = value ⦄ := by
  have length : (Compiler.encodeValue value).length = Compiler.width (sourceType ty) := by
    rw [Compiler.encode_value_length, ← typed]
  have positive := Compiler.width_positive (sourceType ty)
  have first : slots.val[position.val]!.val = (Compiler.encodeValue value)[0]! := by
    simpa using (represented 0 (by omega)).2
  have bound : position.val + Compiler.width (sourceType ty) ≤ slots.length := by
    have last := (represented ((Compiler.encodeValue value).length - 1) (by omega)).1
    change position.val + Compiler.width (sourceType ty) ≤ slots.val.length
    omega
  apply decode_slot_represents slots position ty store value wellFormed typed represented bound
  · intro ht
    rw [first]
    apply encode_value_f32_low value wellFormed
    simpa [ht, sourceType] using typed.symm
  · intro ht
    rw [first]
    apply encode_value_reference_low value fits
    rcases ht with rfl | rfl
    · exact Or.inl typed.symm
    · exact Or.inr typed.symm

end Itasca.Runtime.Interp

end

/-! ## ReferenceArguments -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- A retained source reference bound discharges the concrete result decoder's
usize conversion, including its nonzero reference sentinel. -/
theorem result_index_fits_of_reference_bound (value : val)
    (bounded : SourceMachine.ReferenceBound Usize.max value) : ResultIndexFits value := by
  cases value <;> simp_all [SourceMachine.ReferenceBound, ResultIndexFits] <;> omega

end Itasca.Runtime.Interp

end

/-! ## FrameBindings -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- The module bound to the active source frame is the decoded instance found
by the concrete frame's instance index. -/
theorem FrameBinding.module_lookup {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {raw : runtime.interp.Frame} {source : SourceMachine.AFrame}
    (binding : FrameBinding store exec raw source) (inst : runtime.store.ModuleInst)
    (lookup : store.instances.val[raw.instance.val]? = some inst) :
    source.module = Store.decodeInstance store inst := by
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
  simp only [Store.decodeInstance, List.getElem?_map, found, Option.map_some]

/-- A concrete defined-function entry selects precisely the retained source
body and owning module in the decoded store. -/
theorem defined_function_lookup {M : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (signature : Itasca.wasm_types.FuncType) (instanceIndex functionIndex : Usize)
    (inst : runtime.store.ModuleInst) (sourceCode : funccode)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (hi : store.instances.val[instanceIndex.val]? = some inst)
    (hc : code instanceIndex.val inst.module functionIndex.val = sourceCode) :
    (Store.decodeStore view code store).FUNCS[address.index.val]? =
      some ⟨Store.decodeFuncType signature, Store.decodeInstance store inst, sourceCode⟩ := by
  simp [Store.decodeStore, Store.decodeFunction, List.getD_eq_getElem?_getD, hf, hs, hw, hi, hc]

end Itasca.Runtime.Interp

end

/-! ## SuspendedPoint -/

section

namespace Itasca.Runtime.Interp
open Aeneas.Std

/-- Appending returned values leaves every saved outer label prefix intact. -/
theorem LabelsMatch.append {values : List val} {labels targets}
    (matching : LabelsMatch values labels targets) (results : List val)
    (heights : ∀ label ∈ labels, label.height ≤ values.length) :
    LabelsMatch (values ++ results) labels targets := by
  apply matching.reprefix
  intro label member
  exact (List.take_append_of_le_length (heights label member)).symm

end Itasca.Runtime.Interp

end
