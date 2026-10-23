import Exec.Interp.Simd.Memory.SimdMemorySourceExecute
import Exec.Interp.Simd.Common.SimdInputValues
import Exec.Interp.Simd.Common.SimdNumericResultSlots
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt Itasca.Wasm2.Simd

private theorem memory_inputs_numeric (op : MemoryOperation) (ty : valtype) (member : ty ∈ op.inputs) :
    ty ≠ .FUNCREF ∧ ty ≠ .EXTERNREF := by
  cases ty <;> cases op <;> simp_all [MemoryOperation.inputs,MemoryOperation.store,MemoryOperation.laneCount]

private theorem memory_source_shape (opcode : U32) (op : MemoryOperation) (meaning : memoryMeaning opcode.val = some op) :
    runtime.bytecode.simd_shape opcode = .ok (some (Code.simdSourceShape op.inputs op.outputs)) := by
  let C : context := {(default : context) with MEMS := [default]}
  exact (Code.SimdImmediateMeaning.memory (C := C) opcode ⟨0#u32,0#u32,0#u128⟩ op meaning
    ⟨.mk_uN 0,.mk_uN 0⟩ 0#u8 default rfl rfl (fun _ => rfl)).shape

theorem ValuesAt.simd_memory_result {words : List U64} {base : Nat} {front : List val}
    (represented : ValuesAt words base front) (op : MemoryOperation) (value : U128)
    (capacity : base + Code.slots (front.map Code.valueType) +
      (Code.simdSourceWidth op.outputs[0]?).val ≤ words.length) :
    ValuesAt (simdResultSlots words (base+Code.slots (front.map Code.valueType))
      (Code.simdSourceWidth op.outputs[0]?) value) base
      (front ++ Spec.Simd.operandValues op.outputs value.bv 0 0) := by
  cases writes : op.store with
  | false =>
    have result := represented.simd_numeric_result .V128 value (by decide)
      (by intro impossible;rcases impossible with h | h <;> cases h)
      (by simpa only [MemoryOperation.outputs,writes,Bool.false_eq_true,↓reduceIte,List.getElem?_cons_zero] using capacity)
    simpa only [MemoryOperation.outputs,writes,Bool.false_eq_true,↓reduceIte,List.getElem?_cons_zero,
      Spec.Simd.operandValues,List.zipWith_cons_cons,List.zipWith_nil_left] using result
  | true =>
    simpa [MemoryOperation.outputs,writes,Code.simdSourceWidth,simdResultSlots,Spec.Simd.operandValues] using represented

theorem execute_simd_memory_values {M F : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (interpretation : Store.CodeInterpretation) (view : M → Slice U8) (memoryLaws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instIndex function base : Usize) (opcode operand entry : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (imm : runtime.bytecode.SimdImmediate) (op : MemoryOperation) (front values : List val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : inst.module.functions.val[function.val]? = some code)
    (immediate : code.simd.val[entry.val]? = some imm) (meaning : memoryMeaning opcode.val = some op)
    (ma : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (mapped : inst.memories.val[0]? = some ma) (issued : store.memories.val[ma.index.val]? = some object)
    (position : operand.val = Code.slots (front.map Code.valueType))
    (represented : ValuesAt exec.slots.val base.val (front ++ values))
    (wellFormed : Forall wf_val values) (typed : values.map Code.valueType = op.inputs)
    (space : base.val + operand.val + (Code.simdSourceWidth op.inputs[0]?).val +
      (Code.simdSourceWidth op.inputs[1]?).val ≤ Usize.max)
    (lastSpace : Code.simdSourceWidth op.inputs[2]? = 2#u32 → base.val + operand.val +
      (Code.simdSourceWidth op.inputs[0]?).val + (Code.simdSourceWidth op.inputs[1]?).val < Usize.max)
    (capacity : base.val + operand.val + (Code.simdSourceWidth op.outputs[0]?).val ≤ exec.slots.length)
    (f : frame) (argument : memarg) (moduleEq : f.MODULE = Store.decodeInstance store inst)
    (storeWf : wf_store (Store.decodeStore view interpretation store)) (frameWf : wf_frame f)
    (operationWf : wf_admininstr (admininstr_instr (op.instruction argument (.mk_uN imm.lane.val))))
    (offsetEq : proj_uN_0 argument.OFFSET = imm.offset.val)
    (valid : op.laneCount ≠ 0 → imm.lane.val < op.laneCount) :
    runtime.interp.execute_simd memory floats exec store instIndex function base opcode operand operand entry
      ⦃ out => MemoryMutation view store out.2.2 ma object ∧
        match out.1 with
        | .Ok () => ∃ value, SlotsEffect exec out.2.1 (simdResultSlots exec.slots.val (base.val+operand.val)
              (Code.simdSourceWidth op.outputs[0]?) value) ∧
            ValuesAt out.2.1.slots.val base.val (front ++ Spec.Simd.operandValues op.outputs value.bv 0 0) ∧
            StepH ⟨⟨Store.decodeStore view interpretation store,f⟩,
              values.map admininstr_val ++ [admininstr_instr (op.instruction argument (.mk_uN imm.lane.val))]⟩ []
              ⟨⟨Store.decodeStore view interpretation out.2.2,f⟩,
                (Spec.Simd.operandValues op.outputs value.bv 0 0).map admininstr_val⟩ ∧
            Abs.Simd.MemoryChange (Store.decodeStore view interpretation store) f (Store.decodeStore view interpretation out.2.2)
        | .Err error => error = .Trap .MemoryOutOfBounds ∧ out.2.1 = exec ∧
            Store.decodeStore view interpretation out.2.2 = Store.decodeStore view interpretation store ∧
            StepH ⟨⟨Store.decodeStore view interpretation store,f⟩,
              values.map admininstr_val ++ [admininstr_instr (op.instruction argument (.mk_uN imm.lane.val))]⟩ []
              ⟨⟨Store.decodeStore view interpretation store,f⟩,[.TRAP]⟩ ⦄ := by
  have numeric : ∀ value ∈ values, Code.valueType value ≠ .FUNCREF ∧ Code.valueType value ≠ .EXTERNREF := by
    intro value member
    have m : Code.valueType value ∈ op.inputs := by rw [←typed]; exact List.mem_map_of_mem member
    exact memory_inputs_numeric op _ m
  have arity : values.length ≤ 3 := by
    have length := congrArg List.length typed
    simp only [List.length_map] at length
    have bound : op.inputs.length ≤ 3 := by cases op <;> decide
    omega
  have inputs := represented.operands.simd_operands wellFormed numeric arity
  dsimp only at inputs
  rw [typed,←position] at inputs
  apply WP.spec_mono (execute_simd_memory_source memory floats interpretation view memoryLaws exec store instIndex function base
    opcode operand operand entry inst code imm
    (Code.simdSourceWidth op.inputs[0]?) (Code.simdSourceWidth op.inputs[1]?)
    (Code.simdSourceWidth op.inputs[2]?) (Code.simdSourceWidth op.outputs[0]?) op found compiled immediate
    (memory_source_shape opcode op meaning) meaning ma object mapped issued space lastSpace capacity
    f argument moduleEq storeWf frameWf operationWf offsetEq valid)
  rintro out ⟨mutation,effect⟩
  refine ⟨mutation,?_⟩
  cases status : out.1 with
  | Ok unit =>
    cases unit
    rw [status] at effect
    obtain ⟨value,slots,source,change⟩ := effect
    refine ⟨value,slots,?_,?_,change⟩
    · rw [slots.1,position]
      exact represented.locals.simd_memory_result op value (by simpa only [position] using capacity)
    · unfold Simd.memorySourceInput at source
      rw [inputs] at source
      exact source
  | Err error =>
    rw [status] at effect
    obtain ⟨errorEq,execEq,decoded,source⟩ := effect
    refine ⟨errorEq,execEq,decoded,?_⟩
    unfold Simd.memorySourceInput at source
    rw [inputs] at source
    exact source
end Exec.Interp
