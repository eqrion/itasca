import Exec.Interp.Simd.Memory.SimdMemoryRelation
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std SpecExt Itasca.Wasm2.Simd

theorem memory_entry_0 : MemoryOperationSound 0#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.load = some op at meaning
  cases meaning
  apply WP.spec_mono (full_load_source x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_1 : MemoryOperationSound 1#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.load8x8S = some op at meaning
  cases meaning
  apply WP.spec_mono (extend_load_source .i8 true x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_2 : MemoryOperationSound 2#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.load8x8U = some op at meaning
  cases meaning
  apply WP.spec_mono (extend_load_source .i8 false x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_3 : MemoryOperationSound 3#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.load16x4S = some op at meaning
  cases meaning
  apply WP.spec_mono (extend_load_source .i16 true x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_4 : MemoryOperationSound 4#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.load16x4U = some op at meaning
  cases meaning
  apply WP.spec_mono (extend_load_source .i16 false x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_5 : MemoryOperationSound 5#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.load32x2S = some op at meaning
  cases meaning
  apply WP.spec_mono (extend_load_source .i32 true x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_6 : MemoryOperationSound 6#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.load32x2U = some op at meaning
  cases meaning
  apply WP.spec_mono (extend_load_source .i32 false x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_7 : MemoryOperationSound 7#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.splat8 = some op at meaning
  cases meaning
  apply WP.spec_mono (splat_load_source .I8 x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_8 : MemoryOperationSound 8#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.splat16 = some op at meaning
  cases meaning
  apply WP.spec_mono (splat_load_source .I16 x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_9 : MemoryOperationSound 9#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.splat32 = some op at meaning
  cases meaning
  apply WP.spec_mono (splat_load_source .I32 x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_10 : MemoryOperationSound 10#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.splat64 = some op at meaning
  cases meaning
  apply WP.spec_mono (splat_load_source .I64 x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_84 : MemoryOperationSound 84#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.load8Lane = some op at meaning
  cases meaning
  apply WP.spec_mono (lane_load_source .I8 x y offset index bytes (valid (by decide)) s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_85 : MemoryOperationSound 85#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.load16Lane = some op at meaning
  cases meaning
  apply WP.spec_mono (lane_load_source .I16 x y offset index bytes (valid (by decide)) s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_86 : MemoryOperationSound 86#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.load32Lane = some op at meaning
  cases meaning
  apply WP.spec_mono (lane_load_source .I32 x y offset index bytes (valid (by decide)) s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_87 : MemoryOperationSound 87#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.load64Lane = some op at meaning
  cases meaning
  apply WP.spec_mono (lane_load_source .I64 x y offset index bytes (valid (by decide)) s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_92 : MemoryOperationSound 92#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.load32Zero = some op at meaning
  cases meaning
  apply WP.spec_mono (zero_load_source .zero32 (by intro h; cases h) x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_93 : MemoryOperationSound 93#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some MemoryOperation.load64Zero = some op at meaning
  cases meaning
  apply WP.spec_mono (zero_load_source .zero64 (by intro h; cases h) x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

end Exec.Interp.Simd
