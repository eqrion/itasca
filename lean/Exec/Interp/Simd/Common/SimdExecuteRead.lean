import Exec.Interp.Simd.Memory.SimdExecuteMemoryEffect
import Exec.Interp.Simd.Memory.SimdExecuteMemoryError
import Exec.Interp.Simd.Common.SimdExecute
namespace Exec.Interp
open Aeneas Aeneas.Std
theorem execute_simd_read {M F : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (interpretation : Exec.Store.CodeInterpretation) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instIndex function base : Usize) (op dst a entry : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (imm : runtime.bytecode.SimdImmediate) (wa wb wc wr : U32)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : inst.module.functions.val[function.val]? = some code)
    (immediate : code.simd.val[entry.val]? = some imm)
    (shape : runtime.bytecode.simd_shape op = .ok (some (wa,wb,wc,wr)))
    (ma : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (mapped : inst.memories.val[0]? = some ma)
    (issued : store.memories.val[ma.index.val]? = some object)
    (space : base.val + a.val + wa.val + wb.val + 1 ≤ Usize.max)
    (capacity : base.val + dst.val + wr.val ≤ exec.slots.length)
    (P : core.result.Result U128 runtime.ExecError → Prop)
    (numeric : runtime.interp.simd.simd floats op imm.offset imm.lane imm.bits
      (simdInput exec.slots.val (base.val+a.val) wa)
      (simdInput exec.slots.val (base.val+a.val+wa.val) wb)
      (simdInput exec.slots.val (base.val+a.val+wa.val+wb.val) wc) (some (view object.buf))
        ⦃ out => out.2 = some (view object.buf) ∧ P out.1 ⦄) :
    runtime.interp.execute_simd memory floats exec store instIndex function base op dst a entry
      ⦃ out => Exec.Store.decodeStore view interpretation out.2.2 = Exec.Store.decodeStore view interpretation store ∧
        FrameStoreMetadata store out.2.2 ∧
        match out.1 with
        | .Ok () => ∃ value, P (.Ok value) ∧ SlotsEffect exec out.2.1
            (simdResultSlots exec.slots.val (base.val+dst.val) wr value)
        | .Err error => P (.Err error) ∧ out.2.1 = exec ⦄ := by
  obtain ⟨⟨status,bytes⟩,returned,bytesEq,post⟩ := WP.spec_imp_exists numeric
  dsimp only at bytesEq post
  subst bytes
  cases status with
  | Ok value =>
    apply WP.spec_mono (execute_simd_memory_effect memory floats view laws exec store instIndex function base
      op dst a entry inst code imm wa wb wc wr value found compiled immediate shape ma object mapped issued
      (view object.buf) rfl space capacity returned)
    rintro out ⟨ok,⟨buffer,changed,bytes⟩,slots⟩
    refine ⟨?_,?_,?_⟩
    · rw [changed]; exact memory_unchanged_decodes view interpretation store ma object buffer issued bytes
    · rw [changed]; exact ⟨rfl,rfl,rfl,rfl⟩
    · rw [ok]; exact ⟨value,post,slots⟩
  | Err error =>
    apply WP.spec_mono (execute_simd_memory_error memory floats view laws exec store instIndex function base
      op dst a entry inst code imm wa wb wc wr error found compiled immediate shape ma object mapped issued
      (view object.buf) rfl space capacity returned)
    rintro out ⟨err,execEq,buffer,changed,bytes⟩
    refine ⟨?_,?_,?_⟩
    · rw [changed]; exact memory_unchanged_decodes view interpretation store ma object buffer issued bytes
    · rw [changed]; exact ⟨rfl,rfl,rfl,rfl⟩
    · rw [err]; exact ⟨post,execEq⟩
end Exec.Interp
