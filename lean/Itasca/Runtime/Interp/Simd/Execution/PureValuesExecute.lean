import Itasca.Runtime.Interp.Simd.Relations.InputValues
import Itasca.Runtime.Interp.Simd.Relations.PureResultSlots
import Itasca.Runtime.Interp.Simd.Execution.PureSound
import Itasca.Runtime.Interp.Simd.Execution.ExecuteSource

/-!
Bounded pure SIMD execution with typed result values.

Main declarations: `execute_simd_pure_values_mutation_bounded`. A direct consumer is `Interp.Machine.Simd.PureFrame`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std Itasca.Wasm2.Simd

private theorem signature_inputs_numeric (signature : Signature) (ty : valtype)
    (member : ty ∈ signature.inputs) : ty ≠ .FUNCREF ∧ ty ≠ .EXTERNREF := by
  cases ty <;> cases signature <;> simp_all [Signature.inputs]

theorem execute_simd_pure_values_mutation_bounded {M F : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (interpretation : Store.CodeInterpretation) (view : M → Slice U8)
    (memoryLaws : Platform.MemoryLaws memory view) (floatLaws : Platform.FloatOpsCorrect floats)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instIndex function base : Usize) (opcode operand entry : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (imm : runtime.bytecode.SimdImmediate) (op : Operation) (front values : List val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : inst.module.functions.val[function.val]? = some code)
    (immediate : code.simd.val[entry.val]? = some imm)
    (meaning : pureMeaning opcode.val = some op)
    (memories : ∀ ma, inst.memories.val[0]? = some ma →
      ∃ object, store.memories.val[ma.index.val]? = some object)
    (position : operand.val = Compiler.slots (front.map Compiler.valueType))
    (represented : ValuesAt exec.slots.val base.val (front ++ values))
    (wellFormed : Forall wf_val values)
    (typed : values.map Compiler.valueType = op.signature.inputs)
    (space : base.val + operand.val + (Compiler.simdSourceWidth op.signature.inputs[0]?).val +
      (Compiler.simdSourceWidth op.signature.inputs[1]?).val ≤ Usize.max)
    (lastSpace : Compiler.simdSourceWidth op.signature.inputs[2]? = 2#u32 →
      base.val + operand.val + (Compiler.simdSourceWidth op.signature.inputs[0]?).val +
      (Compiler.simdSourceWidth op.signature.inputs[1]?).val < Usize.max)
    (capacity : base.val + operand.val + (Compiler.simdSourceWidth op.signature.outputs[0]?).val ≤ exec.slots.length) :
    runtime.interp.execute_simd memory floats exec store instIndex function base opcode operand operand entry
      ⦃ out => SimdStoreMutation view store out.2.2 ∧ ∃ value,
        Step_pure (values.map admininstr_val ++ [admininstr_instr op.instruction])
          [admininstr_val (Simd.pureResult op.signature value.bv)] ∧
        out.1 = .Ok () ∧ Store.decodeStore view interpretation out.2.2 = Store.decodeStore view interpretation store ∧
        FrameStoreMetadata store out.2.2 ∧
        SlotsEffect exec out.2.1 (simdResultSlots exec.slots.val (base.val+operand.val)
          (Compiler.simdSourceWidth op.signature.outputs[0]?) value) ∧
        ValuesAt out.2.1.slots.val base.val (front ++ [Simd.pureResult op.signature value.bv]) ⦄ := by
  have numeric : ∀ value ∈ values, Compiler.valueType value ≠ .FUNCREF ∧ Compiler.valueType value ≠ .EXTERNREF := by
    intro value member
    have m : Compiler.valueType value ∈ op.signature.inputs := by rw [←typed]; exact List.mem_map_of_mem member
    exact signature_inputs_numeric op.signature _ m
  have arity : values.length ≤ 3 := by
    have length := congrArg List.length typed
    simp only [List.length_map] at length
    have bound : op.signature.inputs.length ≤ 3 := by cases op.signature <;> decide
    omega
  have inputs := represented.operands.simd_operands wellFormed numeric arity
  dsimp only at inputs
  rw [typed,←position] at inputs
  have shape := (Compiler.SimdImmediateMeaning.pure (C := default) opcode imm op meaning).shape
  apply WP.spec_mono (execute_simd_source_mutation_bounded memory floats interpretation view memoryLaws exec store instIndex function base
    opcode operand operand entry inst code imm
    (Compiler.simdSourceWidth op.signature.inputs[0]?) (Compiler.simdSourceWidth op.signature.inputs[1]?)
    (Compiler.simdSourceWidth op.signature.inputs[2]?) (Compiler.simdSourceWidth op.signature.outputs[0]?)
    (fun value => Step_pure (values.map admininstr_val ++ [admininstr_instr op.instruction])
      [admininstr_val (Simd.pureResult op.signature value.bv)])
    found compiled immediate shape memories space lastSpace capacity ?_)
  · rintro out ⟨mutation,value,source,ok,decoded,metadata,slots⟩
    refine ⟨mutation,value,source,ok,decoded,metadata,slots,?_⟩
    rw [slots.1,position]
    exact represented.locals.simd_pure_result op.signature value _ source (by simpa only [position] using capacity)
  · intro bytes
    apply WP.spec_mono (Simd.pure_dispatch_source floats floatLaws opcode op meaning imm.offset imm.lane imm.bits
      (simdInput exec.slots.val (base.val+operand.val) (Compiler.simdSourceWidth op.signature.inputs[0]?))
      (simdInput exec.slots.val (base.val+operand.val+(Compiler.simdSourceWidth op.signature.inputs[0]?).val)
        (Compiler.simdSourceWidth op.signature.inputs[1]?))
      (simdInput exec.slots.val (base.val+operand.val+(Compiler.simdSourceWidth op.signature.inputs[0]?).val+
        (Compiler.simdSourceWidth op.signature.inputs[1]?).val) (Compiler.simdSourceWidth op.signature.inputs[2]?)) bytes)
    rintro result ⟨value,eq,source⟩
    refine ⟨value,eq,?_⟩
    unfold Simd.PureSourceEffect at source
    rw [inputs] at source
    exact source

end Itasca.Runtime.Interp
