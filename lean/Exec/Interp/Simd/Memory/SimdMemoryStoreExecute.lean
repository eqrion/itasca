import Exec.Interp.Simd.Memory.SimdMemoryStoreSource
import Exec.Interp.Simd.Memory.SimdMemoryDispatch
import Exec.Interp.Simd.Common.SimdExecuteRead
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt
theorem execute_simd_full_store {M F : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (interpretation : Exec.Store.CodeInterpretation) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instIndex function base : Usize) (dst a entry : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (imm : runtime.bytecode.SimdImmediate)
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
    (operationWf : wf_admininstr (.VSTORE .V128 argument))
    (offsetEq : proj_uN_0 argument.OFFSET = imm.offset.val) :
    runtime.interp.execute_simd memory floats exec store instIndex function base 11#u32 dst a entry
      ⦃ out => FrameStoreMetadata store out.2.2 ∧ out.2.1 = exec ∧
        match out.1 with
        | .Ok () => StepH ⟨⟨Exec.Store.decodeStore view interpretation store,f⟩,
          [Spec.Segment.i32 (UScalar.cast .U32 (simdInput exec.slots.val (base.val+a.val) 1#u32)).val,
           .VCONST .V128 (.mk_uN (simdInput exec.slots.val (base.val+a.val+1) 2#u32).val),.VSTORE .V128 argument]⟩ []
          ⟨⟨Exec.Store.decodeStore view interpretation out.2.2,f⟩,[]⟩
        | .Err error => error = .Trap .MemoryOutOfBounds ∧
          Exec.Store.decodeStore view interpretation out.2.2 = Exec.Store.decodeStore view interpretation store ∧
          StepH ⟨⟨Exec.Store.decodeStore view interpretation store,f⟩,
          [Spec.Segment.i32 (UScalar.cast .U32 (simdInput exec.slots.val (base.val+a.val) 1#u32)).val,
           .VCONST .V128 (.mk_uN (simdInput exec.slots.val (base.val+a.val+1) 2#u32).val),.VSTORE .V128 argument]⟩ []
          ⟨⟨Exec.Store.decodeStore view interpretation store,f⟩,[.TRAP]⟩ ⦄ := by
  let x := simdInput exec.slots.val (base.val+a.val) 1#u32
  let y := simdInput exec.slots.val (base.val+a.val+1) 2#u32
  have memoryEq := memory_lookup_decodes view interpretation store inst f ma object moduleEq mapped issued
  have sourceMap : 0 < f.MODULE.MEMS.length := by
    have bound := (List.getElem?_eq_some_iff.mp mapped).1
    simpa [moduleEq,Exec.Store.decodeInstance] using bound
  obtain ⟨result,returned,effect⟩ := WP.spec_imp_exists (Simd.full_store_effect imm.offset imm.lane x y (view object.buf))
  have source := Simd.full_store_source x y imm.offset imm.lane (view object.buf)
    (Exec.Store.decodeStore view interpretation store) f argument storeWf frameWf operationWf offsetEq
    (by rw [memoryEq];rfl) sourceMap
  rw [returned,WP.spec_ok] at source
  have shape : runtime.bytecode.simd_shape 11#u32 = .ok (some (1#u32,2#u32,0#u32,0#u32)) := by
    unfold runtime.bytecode.simd_shape
    with_unfolding_all rfl
  have numeric := Simd.memory_simd_eq floats 11#u32 imm.offset imm.lane imm.bits x y
    (simdInput exec.slots.val (base.val+a.val+1+2) 0#u32) (view object.buf) (by decide)
  rw [returned,bind_ok] at numeric
  unfold Simd.FullStoreEffect at effect
  by_cases fits : (UScalar.cast .U32 x).val + imm.offset.val + 16 ≤ (view object.buf).length
  · rw [if_pos fits] at effect source
    obtain ⟨ok,written⟩ := effect
    obtain ⟨_,decoded,source⟩ := source
    have lengthEq : result.2.length = (view object.buf).length := by
      have lengths := Simd.vectorStoreBytes_length (view object.buf).val
        ((UScalar.cast .U32 x).val+imm.offset.val) y 0 16
      simpa only [Slice.length,written] using lengths
    rw [ok] at numeric
    apply WP.spec_mono (execute_simd_memory_effect memory floats view laws exec store instIndex function base
      11#u32 dst a entry inst code imm 1#u32 2#u32 0#u32 0#u32 0#u128 found compiled immediate shape
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
        ((UScalar.cast .U32 x).val+imm.offset.val) (vbytes_ .V128 (.mk_uN y.val)) moduleEq mapped issued
        (by simpa [vbytes_,ibytes_,vsize,SpecExt.Builtins.integerBytes_length] using fits)
        (by rw [bytesEq];exact decoded)
      rw [dec]
      exact source
  · rw [if_neg fits] at effect source
    rw [effect] at numeric
    apply WP.spec_mono (execute_simd_memory_error memory floats view laws exec store instIndex function base
      11#u32 dst a entry inst code imm 1#u32 2#u32 0#u32 0#u32 (.Trap .MemoryOutOfBounds) found compiled immediate shape
      ma object mapped issued (view object.buf) rfl (by scalar_tac) (by scalar_tac) numeric)
    rintro out ⟨err,execEq,buffer,changed,bytesEq⟩
    refine ⟨?_,execEq,?_⟩
    · rw [changed]; exact ⟨rfl,rfl,rfl,rfl⟩
    · rw [err]
      refine ⟨rfl,?_,source.2⟩
      rw [changed]
      exact memory_unchanged_decodes view interpretation store ma object buffer issued bytesEq
end Exec.Interp
