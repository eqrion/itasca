import Exec.Interp.Simd.Common.SimdInputValues
import Exec.Interp.Simd.Common.SimdNumericResultSlots
import Exec.Interp.Simd.Common.SimdShuffleRelation
import Exec.Interp.Simd.Common.SimdExecuteSource
namespace Exec.Interp
open Aeneas Aeneas.Std Itasca.Wasm2.Simd

theorem execute_simd_shuffle_values {M F : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (interpretation : Store.CodeInterpretation) (view : M → Slice U8) (memoryLaws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instIndex function base : Usize) (operand entry : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (imm : runtime.bytecode.SimdImmediate) (low high : U64) (front values : List val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : inst.module.functions.val[function.val]? = some code)
    (immediate : code.simd.val[entry.val]? = some imm)
    (combined : imm.bits.val = low.val + high.val*2^64)
    (valid : ∀ lane ∈ shuffleIndices low high, proj_uN_0 lane < 32)
    (memories : ∀ ma, inst.memories.val[0]? = some ma → ∃ object, store.memories.val[ma.index.val]? = some object)
    (position : operand.val = Code.slots (front.map Code.valueType))
    (represented : ValuesAt exec.slots.val base.val (front ++ values))
    (wellFormed : Forall wf_val values) (typed : values.map Code.valueType = [.V128,.V128])
    (space : base.val + operand.val + 4 ≤ Usize.max)
    (capacity : base.val + operand.val + 2 ≤ exec.slots.length) :
    runtime.interp.execute_simd memory floats exec store instIndex function base 13#u32 operand operand entry
      ⦃ out => SimdStoreMutation view store out.2.2 ∧ ∃ value, Step_pure (values.map admininstr_val ++ [admininstr_instr (shuffle low high)])
          [admininstr_val (Spec.Simd.valueOfBits .V128 value.bv)] ∧
        out.1 = .Ok () ∧ Store.decodeStore view interpretation out.2.2 = Store.decodeStore view interpretation store ∧
        FrameStoreMetadata store out.2.2 ∧
        SlotsEffect exec out.2.1 (simdResultSlots exec.slots.val (base.val+operand.val) 2#u32 value) ∧
        ValuesAt out.2.1.slots.val base.val (front ++ [Spec.Simd.valueOfBits .V128 value.bv]) ⦄ := by
  have numeric : ∀ value ∈ values, Code.valueType value ≠ .FUNCREF ∧ Code.valueType value ≠ .EXTERNREF := by
    intro value member
    have m : Code.valueType value ∈ [.V128,.V128] := by rw [←typed]; exact List.mem_map_of_mem member
    simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at m
    rw [m]
    decide
  have arity : values.length ≤ 3 := by
    have length := congrArg List.length typed
    simp only [List.length_map,List.length_cons,List.length_nil] at length
    omega
  have inputs := represented.operands.simd_operands wellFormed numeric arity
  dsimp only at inputs
  rw [typed,←position] at inputs
  change Spec.Simd.operandValues [.V128,.V128]
    (simdInput exec.slots.val (base.val+operand.val) 2#u32).bv
    (simdInput exec.slots.val (base.val+operand.val+2) 2#u32).bv
    (simdInput exec.slots.val (base.val+operand.val+2+2) 0#u32).bv = values at inputs
  have shape := (Code.SimdImmediateMeaning.shuffle (C := default) imm low high combined).shape
  apply WP.spec_mono (execute_simd_source_mutation_bounded memory floats interpretation view memoryLaws exec store instIndex function base
    13#u32 operand operand entry inst code imm 2#u32 2#u32 0#u32 2#u32
    (fun value => Step_pure (values.map admininstr_val ++ [admininstr_instr (shuffle low high)])
      [admininstr_val (Spec.Simd.valueOfBits .V128 value.bv)])
    found compiled immediate shape memories (by scalar_tac) (by intro impossible; contradiction) capacity ?_)
  · rintro out ⟨mutation,value,source,ok,decoded,metadata,slots⟩
    refine ⟨mutation,value,source,ok,decoded,metadata,slots,?_⟩
    rw [slots.1,position]
    exact represented.locals.simd_numeric_result .V128 value (by decide)
      (by intro impossible; rcases impossible with h | h <;> cases h) (by change base.val + Code.slots (front.map Code.valueType) + 2 ≤ exec.slots.length; simpa only [position] using capacity)
  · intro bytes
    apply WP.spec_mono (Simd.shuffle_entry_sound floats imm.offset imm.lane imm.bits
      (simdInput exec.slots.val (base.val+operand.val) 2#u32)
      (simdInput exec.slots.val (base.val+operand.val+2) 2#u32)
      (simdInput exec.slots.val (base.val+operand.val+2+2) 0#u32) bytes low high combined valid)
    rintro result ⟨value,returned,source⟩
    refine ⟨value,returned,?_⟩
    unfold Simd.ShuffleSourceEffect at source
    rw [inputs] at source
    exact source
end Exec.Interp
