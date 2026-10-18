import Exec.Interp.Simd.Memory.SimdMemoryZeroSource
import Exec.Interp.Simd.Memory.SimdMemoryDispatch
import Exec.Interp.Simd.Common.SimdExecuteRead
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt

theorem execute_simd_zero_load {M F : Type}
    (op : Simd.PlainLoad) (zero : op ≠ .full)
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (interpretation : Exec.Store.CodeInterpretation) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instIndex function base : Usize) (dst a entry : U32)
    (inst : runtime.store.Instance) (code : runtime.bytecode.CompiledFunction)
    (imm : runtime.bytecode.SimdImmediate)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : inst.module.functions.val[function.val]? = some code)
    (immediate : code.simd.val[entry.val]? = some imm)
    (ma : runtime.MemoryAddr) (object : runtime.store.Memory M)
    (mapped : inst.memories.val[0]? = some ma)
    (issued : store.memories.val[ma.index.val]? = some object)
    (space : base.val + a.val + 2 ≤ Usize.max)
    (capacity : base.val + dst.val + 2 ≤ exec.slots.length)
    (s : _root_.store) (f : frame) (argument : memarg)
    (storeWf : wf_store s) (frameWf : wf_frame f)
    (operationWf : wf_admininstr (.VLOAD .V128 (some (.ZERO (.mk_sz (op.bytes.val*8)))) argument))
    (offsetEq : proj_uN_0 argument.OFFSET = imm.offset.val)
    (memoryEq : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES = Exec.Store.decodeBytes (view object.buf).val) :
    runtime.interp.execute_simd memory floats exec store instIndex function base op.opcode dst a entry
      ⦃ out => Exec.Store.decodeStore view interpretation out.2.2 = Exec.Store.decodeStore view interpretation store ∧
        FrameStoreMetadata store out.2.2 ∧
        match out.1 with
        | .Ok () => ∃ value,
          StepH ⟨⟨s,f⟩,[Spec.Segment.i32 (UScalar.cast .U32 (simdInput exec.slots.val (base.val+a.val) 1#u32)).val,
            .VLOAD .V128 (some (.ZERO (.mk_sz (op.bytes.val*8)))) argument]⟩ [] ⟨⟨s,f⟩,[.VCONST .V128 (.mk_uN value.val)]⟩ ∧
          SlotsEffect exec out.2.1 (simdResultSlots exec.slots.val (base.val+dst.val) 2#u32 value)
        | .Err error => (error = .Trap .MemoryOutOfBounds ∧
          StepH ⟨⟨s,f⟩,[Spec.Segment.i32 (UScalar.cast .U32 (simdInput exec.slots.val (base.val+a.val) 1#u32)).val,
            .VLOAD .V128 (some (.ZERO (.mk_sz (op.bytes.val*8)))) argument]⟩ [] ⟨⟨s,f⟩,[.TRAP]⟩) ∧ out.2.1 = exec ⦄ := by
  have shape : runtime.bytecode.simd_shape op.opcode = .ok (some (1#u32,0#u32,0#u32,2#u32)) := by
    cases op <;> unfold Simd.PlainLoad.opcode runtime.bytecode.simd_shape
    all_goals with_unfolding_all rfl
  apply execute_simd_read memory floats interpretation view laws exec store instIndex function base
    op.opcode dst a entry inst code imm 1#u32 0#u32 0#u32 2#u32 found compiled immediate shape
    ma object mapped issued (by scalar_tac) (by scalar_tac)
    (fun result => match result with
      | .Ok value => StepH ⟨⟨s,f⟩,[Spec.Segment.i32 (UScalar.cast .U32 (simdInput exec.slots.val (base.val+a.val) 1#u32)).val,
          .VLOAD .V128 (some (.ZERO (.mk_sz (op.bytes.val*8)))) argument]⟩ [] ⟨⟨s,f⟩,[.VCONST .V128 (.mk_uN value.val)]⟩
      | .Err error => error = .Trap .MemoryOutOfBounds ∧ StepH
          ⟨⟨s,f⟩,[Spec.Segment.i32 (UScalar.cast .U32 (simdInput exec.slots.val (base.val+a.val) 1#u32)).val,
          .VLOAD .V128 (some (.ZERO (.mk_sz (op.bytes.val*8)))) argument]⟩ [] ⟨⟨s,f⟩,[.TRAP]⟩)
  rw [Simd.memory_simd_eq _ _ _ _ _ _ _ _ _ (by cases op <;> decide)]
  step with Simd.zero_load_source op zero _ _ imm.offset imm.lane (view object.buf) s f argument
    storeWf frameWf operationWf offsetEq memoryEq as ⟨out,bytesEq,source⟩
  exact ⟨congrArg some bytesEq,source⟩
end Exec.Interp
