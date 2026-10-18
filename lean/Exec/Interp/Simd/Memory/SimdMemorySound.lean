import Exec.Interp.Simd.Memory.SimdMemoryEntries
import Exec.Interp.Simd.Memory.SimdMemoryWriteEntries
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std SpecExt Itasca.Wasm2.Simd

theorem memory_operation_range {opcode : U32} {op : MemoryOperation}
    (meaning : memoryMeaning opcode.val = some op) : opcode.val ≤ 11 ∨ 84 ≤ opcode.val ∧ opcode.val ≤ 93 := by
  unfold memoryMeaning at meaning
  split at meaning <;> first | contradiction | omega

theorem memory_operation_sound (opcode : U32) : MemoryOperationSound opcode := by
  intro op meaning
  rcases memory_operation_range meaning with lower | ⟨lower,upper⟩
  · generalize h : opcode.val = n at lower
    interval_cases n
    · have eq : opcode = 0#u32 := by scalar_tac
      subst opcode
      exact memory_entry_0 op meaning
    · have eq : opcode = 1#u32 := by scalar_tac
      subst opcode
      exact memory_entry_1 op meaning
    · have eq : opcode = 2#u32 := by scalar_tac
      subst opcode
      exact memory_entry_2 op meaning
    · have eq : opcode = 3#u32 := by scalar_tac
      subst opcode
      exact memory_entry_3 op meaning
    · have eq : opcode = 4#u32 := by scalar_tac
      subst opcode
      exact memory_entry_4 op meaning
    · have eq : opcode = 5#u32 := by scalar_tac
      subst opcode
      exact memory_entry_5 op meaning
    · have eq : opcode = 6#u32 := by scalar_tac
      subst opcode
      exact memory_entry_6 op meaning
    · have eq : opcode = 7#u32 := by scalar_tac
      subst opcode
      exact memory_entry_7 op meaning
    · have eq : opcode = 8#u32 := by scalar_tac
      subst opcode
      exact memory_entry_8 op meaning
    · have eq : opcode = 9#u32 := by scalar_tac
      subst opcode
      exact memory_entry_9 op meaning
    · have eq : opcode = 10#u32 := by scalar_tac
      subst opcode
      exact memory_entry_10 op meaning
    · have eq : opcode = 11#u32 := by scalar_tac
      subst opcode
      exact memory_entry_11 op meaning
  · generalize h : opcode.val = n at lower upper
    interval_cases n
    · have eq : opcode = 84#u32 := by scalar_tac
      subst opcode
      exact memory_entry_84 op meaning
    · have eq : opcode = 85#u32 := by scalar_tac
      subst opcode
      exact memory_entry_85 op meaning
    · have eq : opcode = 86#u32 := by scalar_tac
      subst opcode
      exact memory_entry_86 op meaning
    · have eq : opcode = 87#u32 := by scalar_tac
      subst opcode
      exact memory_entry_87 op meaning
    · have eq : opcode = 88#u32 := by scalar_tac
      subst opcode
      exact memory_entry_88 op meaning
    · have eq : opcode = 89#u32 := by scalar_tac
      subst opcode
      exact memory_entry_89 op meaning
    · have eq : opcode = 90#u32 := by scalar_tac
      subst opcode
      exact memory_entry_90 op meaning
    · have eq : opcode = 91#u32 := by scalar_tac
      subst opcode
      exact memory_entry_91 op meaning
    · have eq : opcode = 92#u32 := by scalar_tac
      subst opcode
      exact memory_entry_92 op meaning
    · have eq : opcode = 93#u32 := by scalar_tac
      subst opcode
      exact memory_entry_93 op meaning

def MemoryEntrySound {F : Type} (floats : runtime.platform.FloatOps F) (opcode : U32) : Prop :=
  ∀ op, memoryMeaning opcode.val = some op →
    ∀ (offset laneIndex : U32) (bits x y z : U128) (bytes : Slice U8) (s : store) (f : frame) (argument : memarg),
    wf_store s → wf_frame f → wf_admininstr (admininstr_instr (op.instruction argument (.mk_uN laneIndex.val))) →
    proj_uN_0 argument.OFFSET = offset.val →
    (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES = Store.decodeBytes bytes.val →
    0 < f.MODULE.MEMS.length → (op.laneCount ≠ 0 → laneIndex.val < op.laneCount) →
    runtime.interp.simd.simd floats opcode offset laneIndex bits x y z (some bytes)
      ⦃ result => ∃ after, result.2 = some after ∧
        MemorySourceEffect op argument laneIndex.val x.bv y.bv z.bv s f bytes result.1 after ⦄

theorem memory_entry_sound {F : Type} (floats : runtime.platform.FloatOps F) (opcode : U32) :
    MemoryEntrySound floats opcode := by
  intro op meaning offset laneIndex bits x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  rw [memory_simd_eq _ _ _ _ _ _ _ _ _ (memory_operation_range meaning)]
  step with memory_operation_sound opcode op meaning offset laneIndex x y z bytes s f argument
    storeWf frameWf operationWf offsetEq memoryEq mapped valid as ⟨result,effect⟩
  exact ⟨result.2,rfl,effect⟩
end Exec.Interp.Simd
