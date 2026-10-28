import Exec.Interp.Simd.Memory.SimdMemorySound
import Exec.Interp.Simd.Memory.SimdMemoryChangeDecode
import Exec.Interp.Simd.Memory.SimdMemoryTransition
import Exec.Interp.Simd.Memory.SimdExecuteMemoryEffect
import Exec.Interp.Simd.Memory.SimdExecuteMemoryError
import Exec.Interp.Memory.MemoryMutation
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt Itasca.Wasm2.Simd

/-- Execute any decoded vector memory instruction, retaining its exact source
    step, slot footprint and single-buffer mutation. -/
theorem execute_simd_memory_source {M F : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (interpretation : Store.CodeInterpretation) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instIndex function base : Usize) (opcode dst a entry : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (imm : runtime.bytecode.SimdImmediate) (wa wb wc wr : U32) (op : MemoryOperation)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : inst.module.functions.val[function.val]? = some code)
    (immediate : code.simd.val[entry.val]? = some imm)
    (shape : runtime.bytecode.simd_shape opcode = .ok (some (wa,wb,wc,wr)))
    (meaning : memoryMeaning opcode.val = some op)
    (ma : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (mapped : inst.memories.val[0]? = some ma)
    (issued : store.memories.val[ma.index.val]? = some object)
    (space : base.val + a.val + wa.val + wb.val ≤ Usize.max)
    (lastSpace : wc = 2#u32 → base.val + a.val + wa.val + wb.val < Usize.max)
    (capacity : base.val + dst.val + wr.val ≤ exec.slots.length)
    (f : frame) (argument : memarg)
    (moduleEq : f.MODULE = Store.decodeInstance store inst)
    (storeWf : wf_store (Store.decodeStore view interpretation store)) (frameWf : wf_frame f)
    (operationWf : wf_admininstr (admininstr_instr (op.instruction argument (.mk_uN imm.lane.val))))
    (offsetEq : proj_uN_0 argument.OFFSET = imm.offset.val)
    (valid : op.laneCount ≠ 0 → imm.lane.val < op.laneCount) :
    let x := simdInput exec.slots.val (base.val+a.val) wa
    let y := simdInput exec.slots.val (base.val+a.val+wa.val) wb
    let z := simdInput exec.slots.val (base.val+a.val+wa.val+wb.val) wc
    runtime.interp.execute_simd memory floats exec store instIndex function base opcode dst a entry
      ⦃ out => MemoryMutation view store out.2.2 ma object ∧
        match out.1 with
        | .Ok () => ∃ value, SlotsEffect exec out.2.1 (simdResultSlots exec.slots.val (base.val+dst.val) wr value) ∧
            StepH ⟨⟨Store.decodeStore view interpretation store,f⟩,
              Simd.memorySourceInput op argument imm.lane.val x.bv y.bv z.bv⟩ []
              ⟨⟨Store.decodeStore view interpretation out.2.2,f⟩,
                (Spec.Simd.operandValues op.outputs value.bv 0 0).map admininstr_val⟩ ∧
            Abs.Simd.MemoryChange (Store.decodeStore view interpretation store) f (Store.decodeStore view interpretation out.2.2)
        | .Err error => error = .Trap .MemoryOutOfBounds ∧ out.2.1 = exec ∧
            Store.decodeStore view interpretation out.2.2 = Store.decodeStore view interpretation store ∧
            StepH ⟨⟨Store.decodeStore view interpretation store,f⟩,
              Simd.memorySourceInput op argument imm.lane.val x.bv y.bv z.bv⟩ []
              ⟨⟨Store.decodeStore view interpretation store,f⟩,[.TRAP]⟩ ⦄ := by
  dsimp only
  let x := simdInput exec.slots.val (base.val+a.val) wa
  let y := simdInput exec.slots.val (base.val+a.val+wa.val) wb
  let z := simdInput exec.slots.val (base.val+a.val+wa.val+wb.val) wc
  have memoryEq := memory_lookup_decodes view interpretation store inst f ma object moduleEq mapped issued
  have sourceMap : 0 < f.MODULE.MEMS.length := by
    have bound := (List.getElem?_eq_some_iff.mp mapped).1
    simpa [moduleEq,Store.decodeInstance] using bound
  obtain ⟨⟨status,bytes⟩,returned,afterBytes,bytesEq,effect⟩ := WP.spec_imp_exists
    (Simd.memory_entry_sound floats opcode op meaning imm.offset imm.lane imm.bits x y z (view object.buf)
      (Store.decodeStore view interpretation store) f argument storeWf frameWf operationWf offsetEq
      (by rw [memoryEq]; rfl) sourceMap valid)
  dsimp only at bytesEq
  subst bytes
  cases status with
  | Ok value =>
    obtain ⟨sourceAfter,change,source⟩ := effect
    apply WP.spec_mono (execute_simd_memory_effect_bounded memory floats view laws exec store instIndex function base
      opcode dst a entry inst code imm wa wb wc wr value found compiled immediate shape ma object mapped issued
      afterBytes change.length space lastSpace capacity returned)
    rintro out ⟨status,⟨buffer,changed,bytesEq⟩,slots⟩
    have rawChange : Simd.MemoryBufferChange (Store.decodeStore view interpretation store) f
        (view object.buf) (view buffer) sourceAfter := by rw [bytesEq]; exact change
    refine ⟨⟨buffer,changed,rawChange.length⟩,?_⟩
    rw [status]
    refine ⟨value,slots,?_⟩
    rw [changed,rawChange.decoded view interpretation store inst f ma object buffer sourceAfter moduleEq mapped issued]
    exact ⟨source,change.source_change⟩
  | Err error =>
    obtain ⟨errorEq,bytesEq,source⟩ := effect
    subst afterBytes
    apply WP.spec_mono (execute_simd_memory_error_bounded memory floats view laws exec store instIndex function base
      opcode dst a entry inst code imm wa wb wc wr error found compiled immediate shape ma object mapped issued
      (view object.buf) rfl space lastSpace capacity returned)
    rintro out ⟨status,execEq,buffer,changed,bytesEq⟩
    refine ⟨⟨buffer,changed,by rw [bytesEq]⟩,?_⟩
    rw [status]
    refine ⟨errorEq,execEq,?_,source⟩
    rw [changed]
    exact memory_unchanged_decodes view interpretation store ma object buffer issued bytesEq
end Itasca.Runtime.Interp
