import Itasca.Runtime.Interp.Simd.Relations.InputValues
import Itasca.Runtime.Interp.Simd.Relations.NumericResultSlots
import Itasca.Runtime.Interp.Simd.Lanes.LaneEntries
import Itasca.Runtime.Interp.Simd.Execution.ExecuteSource

/-!
Typed value correspondence for SIMD lane execution.

Main declarations: `ValuesAt.simd_lane_result` and `execute_simd_lane_values`. A direct consumer is `Interp.Machine.Simd.LaneFrame`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std Itasca.Wasm2.Simd

private theorem lane_inputs_numeric (op : LaneOperation) (ty : valtype) (member : ty ∈ op.inputs) :
    ty ≠ .FUNCREF ∧ ty ≠ .EXTERNREF := by
  cases ty <;> cases op <;> simp_all [LaneOperation.inputs,LaneOperation.replace,LaneOperation.scalar,valtype_numtype]

private theorem lane_source_shape (opcode : U32) (op : LaneOperation) (meaning : laneMeaning opcode.val = some op) :
    runtime.bytecode.simd_shape opcode = .ok (some (Compiler.simdSourceShape op.inputs op.outputs)) := by
  exact (Compiler.SimdImmediateMeaning.lane (C := default) opcode ⟨0#u32,0#u32,0#u128⟩ op meaning 0#u8 rfl).shape

theorem ValuesAt.simd_lane_result {words : List U64} {base : Nat} {front : List val}
    (represented : ValuesAt words base front) (op : LaneOperation) (value : U128)
    (bound : Simd.LaneResultBound op value)
    (capacity : base + Compiler.slots (front.map Compiler.valueType) +
      (Compiler.simdSourceWidth op.outputs[0]?).val ≤ words.length) :
    ValuesAt (simdResultSlots words (base+Compiler.slots (front.map Compiler.valueType))
      (Compiler.simdSourceWidth op.outputs[0]?) value) base (front ++ [Simd.laneResult op value.bv]) := by
  let ty := if op.replace then valtype.V128 else valtype_numtype op.scalar
  have outputs : op.outputs = [ty] := by cases op <;> rfl
  have numeric : ty ≠ .FUNCREF ∧ ty ≠ .EXTERNREF ∧ ty ≠ .BOT := by cases op <;> decide
  have small : ty = .I32 ∨ ty = .F32 → value.val < 2^32 := by
    intro small
    cases op <;> first | exact bound rfl | cases small <;> contradiction
  simpa only [outputs,List.getElem?_cons_zero,Simd.laneResult] using
    represented.simd_numeric_result ty value numeric small (by simpa only [outputs,List.getElem?_cons_zero] using capacity)

theorem execute_simd_lane_values {M F : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (interpretation : Store.CodeInterpretation) (view : M → Slice U8) (memoryLaws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instIndex function base : Usize) (opcode operand entry : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (imm : runtime.bytecode.SimdImmediate) (op : LaneOperation) (front values : List val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : inst.module.functions.val[function.val]? = some code)
    (immediate : code.simd.val[entry.val]? = some imm)
    (meaning : laneMeaning opcode.val = some op) (valid : imm.lane.val < op.count)
    (memories : ∀ ma, inst.memories.val[0]? = some ma → ∃ object, store.memories.val[ma.index.val]? = some object)
    (position : operand.val = Compiler.slots (front.map Compiler.valueType))
    (represented : ValuesAt exec.slots.val base.val (front ++ values))
    (wellFormed : Forall wf_val values) (typed : values.map Compiler.valueType = op.inputs)
    (space : base.val + operand.val + (Compiler.simdSourceWidth op.inputs[0]?).val +
      (Compiler.simdSourceWidth op.inputs[1]?).val ≤ Usize.max)
    (lastSpace : Compiler.simdSourceWidth op.inputs[2]? = 2#u32 → base.val + operand.val +
      (Compiler.simdSourceWidth op.inputs[0]?).val + (Compiler.simdSourceWidth op.inputs[1]?).val < Usize.max)
    (capacity : base.val + operand.val + (Compiler.simdSourceWidth op.outputs[0]?).val ≤ exec.slots.length) :
    runtime.interp.execute_simd memory floats exec store instIndex function base opcode operand operand entry
      ⦃ out => SimdStoreMutation view store out.2.2 ∧ ∃ value, Step_pure (values.map admininstr_val ++ [admininstr_instr (op.instruction (.mk_uN imm.lane.val))])
          [admininstr_val (Simd.laneResult op value.bv)] ∧
        out.1 = .Ok () ∧ Store.decodeStore view interpretation out.2.2 = Store.decodeStore view interpretation store ∧
        FrameStoreMetadata store out.2.2 ∧
        SlotsEffect exec out.2.1 (simdResultSlots exec.slots.val (base.val+operand.val)
          (Compiler.simdSourceWidth op.outputs[0]?) value) ∧
        ValuesAt out.2.1.slots.val base.val (front ++ [Simd.laneResult op value.bv]) ⦄ := by
  have numeric : ∀ value ∈ values, Compiler.valueType value ≠ .FUNCREF ∧ Compiler.valueType value ≠ .EXTERNREF := by
    intro value member
    have m : Compiler.valueType value ∈ op.inputs := by rw [←typed]; exact List.mem_map_of_mem member
    exact lane_inputs_numeric op _ m
  have arity : values.length ≤ 3 := by
    have length := congrArg List.length typed
    simp only [List.length_map] at length
    have bound : op.inputs.length ≤ 3 := by cases op <;> decide
    omega
  have inputs := represented.operands.simd_operands wellFormed numeric arity
  dsimp only at inputs
  rw [typed,←position] at inputs
  apply WP.spec_mono (execute_simd_source_mutation_bounded memory floats interpretation view memoryLaws exec store instIndex function base
    opcode operand operand entry inst code imm
    (Compiler.simdSourceWidth op.inputs[0]?) (Compiler.simdSourceWidth op.inputs[1]?)
    (Compiler.simdSourceWidth op.inputs[2]?) (Compiler.simdSourceWidth op.outputs[0]?)
    (fun value => Step_pure (values.map admininstr_val ++ [admininstr_instr (op.instruction (.mk_uN imm.lane.val))])
      [admininstr_val (Simd.laneResult op value.bv)] ∧ Simd.LaneResultBound op value)
    found compiled immediate (lane_source_shape opcode op meaning) memories space lastSpace capacity ?_)
  · rintro out ⟨mutation,value,⟨source,bounded⟩,ok,decoded,metadata,slots⟩
    refine ⟨mutation,value,source,ok,decoded,metadata,slots,?_⟩
    rw [slots.1,position]
    exact represented.locals.simd_lane_result op value bounded (by simpa only [position] using capacity)
  · intro bytes
    apply WP.spec_mono (Simd.lane_entry_sound floats opcode op meaning imm.offset imm.lane imm.bits
      (simdInput exec.slots.val (base.val+operand.val) (Compiler.simdSourceWidth op.inputs[0]?))
      (simdInput exec.slots.val (base.val+operand.val+(Compiler.simdSourceWidth op.inputs[0]?).val) (Compiler.simdSourceWidth op.inputs[1]?))
      (simdInput exec.slots.val (base.val+operand.val+(Compiler.simdSourceWidth op.inputs[0]?).val+
        (Compiler.simdSourceWidth op.inputs[1]?).val) (Compiler.simdSourceWidth op.inputs[2]?)) bytes valid)
    rintro result ⟨value,returned,source,bounded⟩
    refine ⟨value,returned,?_,bounded⟩
    unfold Simd.LaneSourceEffect at source
    rw [inputs] at source
    exact source
end Itasca.Runtime.Interp
