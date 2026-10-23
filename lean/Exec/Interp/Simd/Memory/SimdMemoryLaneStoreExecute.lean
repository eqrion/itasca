import Exec.Interp.Simd.Memory.SimdMemoryLaneStoreSource
import Exec.Interp.Simd.Memory.SimdMemoryDispatch
import Exec.Interp.Simd.Common.SimdExecuteRead
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt
theorem execute_simd_lane_store {M F : Type} (ty : Jnn)
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (interpretation : Exec.Store.CodeInterpretation) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instIndex function base : Usize) (dst a entry : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (imm : runtime.bytecode.SimdImmediate)
    (valid : imm.lane.val < 128/(Simd.shiftWidth ty).val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : inst.module.functions.val[function.val]? = some code)
    (immediate : code.simd.val[entry.val]? = some imm)
    (ma : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (mapped : inst.memories.val[0]? = some ma)
    (issued : store.memories.val[ma.index.val]? = some object)
    (space : base.val + a.val + 4 ≤ Usize.max)
    (capacity : base.val + dst.val + 0 ≤ exec.slots.length)
    (f : frame) (argument : memarg)
    (moduleEq : f.MODULE = Exec.Store.decodeInstance store inst)
    (storeWf : wf_store (Exec.Store.decodeStore view interpretation store)) (frameWf : wf_frame f)
    (operationWf : wf_admininstr (.VSTORE_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN imm.lane.val)))
    (offsetEq : proj_uN_0 argument.OFFSET = imm.offset.val) :
    runtime.interp.execute_simd memory floats exec store instIndex function base (Simd.memoryLaneOpcode ty true) dst a entry
      ⦃ out => FrameStoreMetadata store out.2.2 ∧ out.2.1 = exec ∧
        match out.1 with
        | .Ok () => StepH ⟨⟨Exec.Store.decodeStore view interpretation store,f⟩,
          [Spec.Segment.i32 (UScalar.cast .U32 (simdInput exec.slots.val (base.val+a.val) 1#u32)).val,
           .VCONST .V128 (.mk_uN (simdInput exec.slots.val (base.val+a.val+1) 2#u32).val),.VSTORE_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN imm.lane.val)]⟩ []
          ⟨⟨Exec.Store.decodeStore view interpretation out.2.2,f⟩,[]⟩
        | .Err error => error = .Trap .MemoryOutOfBounds ∧
          Exec.Store.decodeStore view interpretation out.2.2 = Exec.Store.decodeStore view interpretation store ∧
          StepH ⟨⟨Exec.Store.decodeStore view interpretation store,f⟩,
          [Spec.Segment.i32 (UScalar.cast .U32 (simdInput exec.slots.val (base.val+a.val) 1#u32)).val,
           .VCONST .V128 (.mk_uN (simdInput exec.slots.val (base.val+a.val+1) 2#u32).val),.VSTORE_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN imm.lane.val)]⟩ []
          ⟨⟨Exec.Store.decodeStore view interpretation store,f⟩,[.TRAP]⟩ ⦄ := by
  let x := simdInput exec.slots.val (base.val+a.val) 1#u32
  let y := simdInput exec.slots.val (base.val+a.val+1) 2#u32
  have memoryEq := memory_lookup_decodes view interpretation store inst f ma object moduleEq mapped issued
  have sourceMap : 0 < f.MODULE.MEMS.length := by
    have bound := (List.getElem?_eq_some_iff.mp mapped).1
    simpa [moduleEq,Exec.Store.decodeInstance] using bound
  obtain ⟨result,returned,effect⟩ := WP.spec_imp_exists (Simd.memory_lane_store_effect ty imm.offset imm.lane x y (view object.buf) valid)
  have source := Simd.lane_store_source ty x y imm.offset imm.lane (view object.buf) valid
    (Exec.Store.decodeStore view interpretation store) f argument storeWf frameWf operationWf offsetEq
    (by rw [memoryEq];rfl) sourceMap
  rw [returned,WP.spec_ok] at source
  have shape : runtime.bytecode.simd_shape (Simd.memoryLaneOpcode ty true) = .ok (some (1#u32,2#u32,0#u32,0#u32)) := by
    cases ty <;> unfold Simd.memoryLaneOpcode runtime.bytecode.simd_shape
    all_goals with_unfolding_all rfl
  have numeric := Simd.memory_simd_eq floats (Simd.memoryLaneOpcode ty true) imm.offset imm.lane imm.bits x y
    (simdInput exec.slots.val (base.val+a.val+1+2) 0#u32) (view object.buf) (by cases ty <;> decide)
  rw [returned,bind_ok] at numeric
  unfold Simd.LaneStoreEffect at effect
  by_cases fits : (UScalar.cast .U32 x).val + imm.offset.val + (Simd.memoryLaneBytes ty).val ≤ (view object.buf).length
  · rw [if_pos fits] at effect source
    obtain ⟨word,bits,ok,written⟩ := effect
    obtain ⟨_,decoded,source⟩ := source
    have lengthEq : result.2.length = (view object.buf).length := by
      have lengths := Simd.vectorStoreBytes_length (view object.buf).val
        ((UScalar.cast .U32 x).val+imm.offset.val) (UScalar.cast .U128 word) 0 (Simd.memoryLaneBytes ty).val
      simpa only [Slice.length,written] using lengths
    rw [ok] at numeric
    apply WP.spec_mono (execute_simd_memory_effect memory floats view laws exec store instIndex function base
      (Simd.memoryLaneOpcode ty true) dst a entry inst code imm 1#u32 2#u32 0#u32 0#u32 0#u128 found compiled immediate shape
      ma object mapped issued result.2 lengthEq (by scalar_tac) (by scalar_tac) numeric)
    rintro out ⟨ok,⟨buffer,changed,bytesEq⟩,slots⟩
    have execEq : out.2.1 = exec := by
      have sameSlots : out.2.1.slots = exec.slots := by
        apply alloc.vec.Vec.ext
        simpa [simdResultSlots] using slots.1
      simpa only [←sameSlots] using slots.2
    refine ⟨?_,execEq,?_⟩
    · rw [changed]; exact ⟨rfl,rfl,rfl,rfl⟩
    · rw [ok,changed]
      have dec := memory_write_decodes view interpretation store inst f ma object buffer
        ((UScalar.cast .U32 x).val+imm.offset.val) (SpecExt.Builtins.integerBytes (Simd.memoryLaneBytes ty).val
          (Simd.laneBits (lsize (lanetype_Jnn ty)) imm.lane.val y.bv).toNat) moduleEq mapped issued
        (by simpa [vbytes_,ibytes_,vsize,SpecExt.Builtins.integerBytes_length] using fits)
        (by rw [bytesEq];exact decoded)
      rw [dec]
      exact source
  · rw [if_neg fits] at effect source
    rw [effect] at numeric
    apply WP.spec_mono (execute_simd_memory_error memory floats view laws exec store instIndex function base
      (Simd.memoryLaneOpcode ty true) dst a entry inst code imm 1#u32 2#u32 0#u32 0#u32 (.Trap .MemoryOutOfBounds) found compiled immediate shape
      ma object mapped issued (view object.buf) rfl (by scalar_tac) (by scalar_tac) numeric)
    rintro out ⟨err,execEq,buffer,changed,bytesEq⟩
    refine ⟨?_,execEq,?_⟩
    · rw [changed]; exact ⟨rfl,rfl,rfl,rfl⟩
    · rw [err]
      refine ⟨rfl,?_,source.2⟩
      rw [changed]
      exact memory_unchanged_decodes view interpretation store ma object buffer issued bytesEq
end Exec.Interp
