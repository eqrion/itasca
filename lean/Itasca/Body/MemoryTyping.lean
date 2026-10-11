import Itasca.Body.MemoryMeaning
import Itasca.Body.EnvTranslation

open Aeneas Aeneas.Std

namespace Itasca.MemoryMeaning

def Operation.inputs (op : Operation) : List types.ValueType :=
  if op.store then [.I32, op.ty] else [.I32]

def Operation.outputs (op : Operation) : List types.ValueType :=
  if op.store then [] else [op.ty]

theorem memArg_wf (arg : code.MemArg) : wf_memarg (memArg arg) :=
  .memarg_case_ _ _ (EnvTranslation.index_wf _) (EnvTranslation.index_wf _)

theorem alignment_mono (a b : Nat) (h : a ≤ b) : (2 : Rat) ^ a ≤ 2 ^ b := by
  exact pow_le_pow_right₀ (by norm_num) h

/-- The independent row's declared stack effect is an instance of the generated
    memory rule, once the runtime memory and alignment checks have succeeded. -/
def Operation.Typed (op : Operation) : Prop :=
  ∀ (arg : code.MemArg) (C : context) (mt : memtype),
    wf_context C → 0 < C.MEMS.length → C.MEMS[0]! = mt → wf_memtype mt →
    arg.align.val ≤ op.naturalAlign.val →
    wf_instr (op.op arg) ∧ Instr_ok C (op.op arg)
      (.mk_functype (.mk_list (op.inputs.map Translate.valueType))
        (.mk_list (op.outputs.map Translate.valueType)))

theorem fullLoad_typed (ty : types.ValueType) (nt : numtype) (alignment : U32)
    (bits : Nat) (hty : valtype_numtype nt = Translate.valueType ty)
    (hbits : size (valtype_numtype nt) = some bits)
    (halign : (2 : Rat) ^ alignment.val ≤ (bits : Rat) / 8) :
    (fullLoad ty nt alignment).Typed := by
  intro arg C mt hC hm he hmt ha
  have hw : wf_instr (.LOAD nt none (memArg arg)) :=
    .instr_case_56 _ _ _ (by simp [Forall]) (memArg_wf _)
  refine ⟨hw, ?_⟩
  have hp : (2 : Rat) ^ (proj_uN_0 (memArg arg).ALIGN) ≤
      (Option.get! (size (valtype_numtype nt)) : Rat) / 8 := by
    simpa [memArg, proj_uN_0, hbits] using (alignment_mono _ _ ha).trans halign
  simpa [Operation.inputs, Operation.outputs, fullLoad, hty, Translate.valueType] using
    Instr_ok.load_val C nt (memArg arg) mt hm he (by simp [hbits]) hp hC hmt hw

theorem fullStore_typed (ty : types.ValueType) (nt : numtype) (alignment : U32)
    (bits : Nat) (hty : valtype_numtype nt = Translate.valueType ty)
    (hbits : size (valtype_numtype nt) = some bits)
    (halign : (2 : Rat) ^ alignment.val ≤ (bits : Rat) / 8) :
    (fullStore ty nt alignment).Typed := by
  intro arg C mt hC hm he hmt ha
  have hw : wf_instr (.STORE nt none (memArg arg)) :=
    .instr_case_57 none _ _ _ (by simp [Forall]) (memArg_wf _)
      (by simp) (by simp [Forall₂])
  refine ⟨hw, ?_⟩
  have hp : (2 : Rat) ^ (proj_uN_0 (memArg arg).ALIGN) ≤
      (Option.get! (size (valtype_numtype nt)) : Rat) / 8 := by
    simpa [memArg, proj_uN_0, hbits] using (alignment_mono _ _ ha).trans halign
  simpa [Operation.inputs, Operation.outputs, fullStore, hty, Translate.valueType] using
    Instr_ok.store_val C nt (memArg arg) mt hm he (by simp [hbits]) hp hC hmt hw

theorem packedLoad_typed (ty : types.ValueType) (it : Inn) (width : Nat)
    (extension : sx) (alignment : U32)
    (hty : valtype_Inn it = Translate.valueType ty)
    (hw : wf_sz (.mk_sz width)) (hfit : width < sizenn (numtype_Inn it))
    (halign : (2 : Rat) ^ alignment.val ≤ (width : Rat) / 8) :
    (packedLoad ty it width extension alignment).Typed := by
  intro arg C mt hC hm he hmt ha
  have hwf : wf_instr ((packedLoad ty it width extension alignment).op arg) := by
    apply wf_instr.instr_case_56
    · simp only [Option.toList_some, Forall, List.mem_singleton, forall_eq]
      exact .loadop__case_0 _ _ _ (.loadop_Inn_case_0 _ _ _ hw hfit) rfl
    · exact memArg_wf _
  refine ⟨hwf, ?_⟩
  have hp : (2 : Rat) ^ (proj_uN_0 (memArg arg).ALIGN) ≤ (width : Rat) / 8 :=
    (alignment_mono _ _ ha).trans halign
  simpa [Operation.inputs, Operation.outputs, packedLoad, hty, Translate.valueType] using
    Instr_ok.load_pack C it width extension (memArg arg) mt hm he hp hC hmt hwf

theorem packedStore_typed (ty : types.ValueType) (it : Inn) (width : Nat) (alignment : U32)
    (hty : valtype_Inn it = Translate.valueType ty)
    (hw : wf_sz (.mk_sz width)) (hfit : width < sizenn (numtype_Inn it))
    (halign : (2 : Rat) ^ alignment.val ≤ (width : Rat) / 8) :
    (packedStore ty it width alignment).Typed := by
  intro arg C mt hC hm he hmt ha
  have hwf : wf_instr ((packedStore ty it width alignment).op arg) := by
    apply wf_instr.instr_case_57 (some it)
    · simpa [Forall] using hw
    · exact memArg_wf _
    · simp
    · simpa [Forall₂, proj_sz_0] using hfit
  refine ⟨hwf, ?_⟩
  have hp : (2 : Rat) ^ (proj_uN_0 (memArg arg).ALIGN) ≤ (width : Rat) / 8 :=
    (alignment_mono _ _ ha).trans halign
  simpa [Operation.inputs, Operation.outputs, packedStore, hty, Translate.valueType] using
    Instr_ok.store_pack C it width (memArg arg) mt hm he hp hC hmt hwf

theorem opcodeMeaning_typed (opcode : U8) (op : Operation)
    (h : opcodeMeaning opcode = some op) : op.Typed := by
  unfold opcodeMeaning at h
  split at h <;> cases h
  all_goals first
    | exact fullLoad_typed _ _ _ 32 rfl rfl (by norm_num)
    | exact fullLoad_typed _ _ _ 64 rfl rfl (by norm_num)
    | exact fullStore_typed _ _ _ 32 rfl rfl (by norm_num)
    | exact fullStore_typed _ _ _ 64 rfl rfl (by norm_num)
    | apply packedLoad_typed
    | apply packedStore_typed
  all_goals try (apply wf_sz.sz_case_0; norm_num)
  all_goals norm_num [valtype_numtype, valtype_Inn, Translate.valueType, size, sizenn, numtype_Inn]

end Itasca.MemoryMeaning

namespace Itasca.EnvTranslation

theorem Matches.memory_operation {env ctx C} (h : Matches env ctx C)
    (opcode : U8) (op : MemoryMeaning.Operation) (hrow : MemoryMeaning.opcodeMeaning opcode = some op)
    (arg : code.MemArg) (hm : 0 < env.mem_types.val.length)
    (ha : arg.align.val ≤ op.naturalAlign.val) :
    wf_instr (op.op arg) ∧ Instr_ok C (op.op arg)
      (.mk_functype (.mk_list (op.inputs.map Translate.valueType))
        (.mk_list (op.outputs.map Translate.valueType))) := by
  apply MemoryMeaning.opcodeMeaning_typed opcode op hrow arg C (memType (env.mem_types.val[0]))
    h.wf _ _ (memType_wf _) ha
  · simpa [h.mems] using hm
  · simp only [h.mems]
    rw [getElem!_pos _ _ (by simpa using hm), List.getElem_map]

end Itasca.EnvTranslation
