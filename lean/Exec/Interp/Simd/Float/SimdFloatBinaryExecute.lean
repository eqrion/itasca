import Exec.Interp.Simd.Float.SimdFloatBinarySound
import Exec.Interp.Simd.Common.SimdExecute
namespace Exec.Interp
open Aeneas Aeneas.Std Platform

theorem execute_simd_float_binary {M F : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (floatLaws : FloatOpsCorrect floats)
    (interpretation : Exec.Store.CodeInterpretation) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instIndex function base : Usize) (ty : Fnn) (op : vbinop_Fnn_N) (dst a entry : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (imm : runtime.bytecode.SimdImmediate)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : inst.module.functions.val[function.val]? = some code)
    (immediate : code.simd.val[entry.val]? = some imm)
    (memories : ∀ ma, inst.memories.val[0]? = some ma →
      ∃ object, store.memories.val[ma.index.val]? = some object)
    (space : base.val + a.val + 5 ≤ Usize.max)
    (capacity : base.val + dst.val + 2 ≤ exec.slots.length) :
    runtime.interp.execute_simd memory floats exec store instIndex function base
      (Simd.floatBinaryOpcode ty op) dst a entry
      ⦃ out => ∃ value,
        out.1 = .Ok () ∧
        Exec.Store.decodeStore view interpretation out.2.2 = Exec.Store.decodeStore view interpretation store ∧
        FrameStoreMetadata store out.2.2 ∧
        SlotsEffect exec out.2.1 (simdResultSlots exec.slots.val (base.val+dst.val) 2#u32 value) ∧
        Step_pure [.VCONST .V128 (.mk_uN (simdInput exec.slots.val (base.val+a.val) 2#u32).val),
          .VCONST .V128 (.mk_uN (simdInput exec.slots.val (base.val+a.val+2) 2#u32).val),
          .VBINOP (Spec.Simd.shapeOf (lanetype_Fnn ty)) (Spec.Simd.floatBinarySource ty op)]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  let x := simdInput exec.slots.val (base.val+a.val) 2#u32
  let y := simdInput exec.slots.val (base.val+a.val+2) 2#u32
  obtain ⟨value,returned,source⟩ := WP.spec_imp_exists (Simd.float_binary_lanes_sound floats floatLaws ty op x y)
  have numeric (bytes : Option (Slice U8)) :
      runtime.interp.simd.simd floats (Simd.floatBinaryOpcode ty op) imm.offset imm.lane imm.bits
        x y (simdInput exec.slots.val (base.val+a.val+2+2) 0#u32) bytes = .ok (.Ok value,bytes) := by
    rw [Simd.float_binary_simd_eq,returned,bind_ok]
  have shape : runtime.bytecode.simd_shape (Simd.floatBinaryOpcode ty op) = .ok (some (2#u32,2#u32,0#u32,2#u32)) := by
    cases ty <;> cases op
    all_goals unfold Simd.floatBinaryOpcode runtime.bytecode.simd_shape
    all_goals with_unfolding_all rfl
  apply WP.spec_mono (execute_simd_pure memory floats interpretation view laws exec store instIndex function base
    (Simd.floatBinaryOpcode ty op) dst a entry inst code imm 2#u32 2#u32 0#u32 2#u32 value
    found compiled immediate shape memories (by scalar_tac) (by scalar_tac) numeric)
  rintro out ⟨ok,decoded,metadata,slots⟩
  exact ⟨value,ok,decoded,metadata,slots,source⟩
end Exec.Interp
