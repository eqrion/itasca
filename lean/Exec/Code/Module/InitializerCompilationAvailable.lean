import Exec.Code.Module.SegmentCompilationAvailable
import Exec.Code.Module.InitializerElementsAvailable
import Exec.Code.Module.InitializerDataOffsetsAvailable
import Exec.Code.Module.InitializerTotal
import Itasca.Module.Env.Basic

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Independent constant-expression judgments for every source initializer. -/
structure InitializerSourceTyping (module : runtime.compiler.ExecutableModule) : Prop where
  globals : ∀ global ∈ module.module.env.globals.val,
    Itasca.ModuleConstants.Valid module.module.env global.init global.gtype.valtype
  elements : ∀ segment ∈ module.module.env.elements.val, ∀ expr ∈ segment.init.val,
    Itasca.ModuleConstants.Valid module.module.env expr (Itasca.ModuleConstants.referenceValueType segment.elem)
  elementOffsets : ∀ segment ∈ module.module.env.elements.val, ∀ table offset,
    segment.mode = .Active table offset → Itasca.ModuleConstants.Valid module.module.env offset .I32
  dataOffsets : ∀ segment ∈ module.module.tail.data.val, ∀ memory offset,
    segment.mode = .Active memory offset → Itasca.ModuleConstants.Valid module.module.env offset .I32

/-- The existing independent environment and data judgments discharge every
initializer typing premise; no emitted code or compiler observation is needed. -/
theorem InitializerSourceTyping.of_valid {module : runtime.compiler.ExecutableModule}
    {profile : Itasca.ValidationProfile} (valid : Itasca.ModuleEnv.Valid module.module.env profile)
    (dataValid : ∀ segment ∈ module.module.tail.data.val, Itasca.ModuleData.Valid module.module.env segment) :
    InitializerSourceTyping module := by
  refine ⟨valid.globals,?_,?_,?_⟩
  · intro segment member
    exact (valid.elements segment member).2
  · intro segment member table offset mode
    have active := (valid.elements segment member).1
    rw [mode] at active
    exact active.choose_spec.2
  · intro segment member memory offset mode
    have active := dataValid segment member
    unfold Itasca.ModuleData.Valid at active
    rw [mode] at active
    exact active.2

/-- Conservative complete-pass demand, computed from source initializer counts
and existing retained vectors. Temporary element indices are included. -/
structure InitializerCompilationDemand {A : Type} (module : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (bound : Nat) : Prop where
  instructions : budget.instructions.val + 2*initializerMappingCost module.module + segmentCompilationDemand module ≤
    budget.limits.max_instructions.val
  mappingCapacity : initializerSize module + initializerMappingCost module.module + 1 ≤ Usize.max
  mappingReserve : initializerSize module + initializerMappingCost module.module + 1 ≤ bound
  literalReserve : 2 ≤ bound
  codeCapacity : segmentCompilationDemand module ≤ Usize.max
  codeReserve : segmentCompilationDemand module ≤ bound
  elementCount : module.module.env.elements.length ≤ U32.max
  dataCount : module.module.tail.data.length ≤ U32.max
  elementLengths : ∀ segment ∈ module.module.env.elements.val, segment.init.length ≤ U32.max
  dataLengths : ∀ segment ∈ module.module.tail.data.val, segment.init.length ≤ U32.max

/-- The real complete initializer pass accepts from independent source typing
and bounded allocation demand. Its emitted code, checker acceptance, and normal
return are established internally, not assumed as a trace or certificate. -/
theorem initializer_compilation_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (source : InitializerSourceTyping module) (demand : InitializerCompilationDemand module budget bound) :
    runtime.compiler.initialize.lower ops module budget ⦃ out =>
      out.1 = .Ok () ∧ out.2.1.module = module.module ∧ out.2.2.limits = budget.limits ∧
      out.2.2.instructions.val ≤ budget.instructions.val + 2*initializerMappingCost module.module +
        segmentCompilationDemand module ⦄ := by
  have room := demand.instructions
  have capacity := demand.mappingCapacity
  have reserve := demand.mappingReserve
  unfold initializerMappingCost at room capacity reserve
  obtain ⟨⟨m1,b1,status⟩,call1,accepted,source1,size1,used1,limits1⟩ := WP.spec_imp_exists
    (initializer_globals_available ops bound available module budget 0#usize (by simp) source.globals
      (by simp; omega) demand.literalReserve (by simp; omega) (by simp; omega))
  dsimp only at accepted source1 size1 used1 limits1
  subst status
  simp only [show (0#usize).val = 0 from rfl,Nat.sub_zero] at size1 used1
  obtain ⟨⟨m2,b2,status⟩,call2,accepted,source2,limits2,size2,used2⟩ := WP.spec_imp_exists
    (initializer_elements_available ops bound available m1 b1 0#usize (by simp)
      (by simpa [source1] using source.elements) (by simpa [source1] using source.elementOffsets)
      (by rw [limits1]; simp [source1]; omega) demand.literalReserve
      (by simp [source1]; omega) (by simp [source1]; omega))
  dsimp only at accepted source2 limits2 size2 used2
  subst status
  have same2 : m2.module = module.module := source2.trans source1
  simp only [show (0#usize).val = 0 from rfl,List.drop_zero,source1] at size2 used2
  obtain ⟨⟨m3,b3,status⟩,call3,accepted,source3,size3,used3,limits3⟩ := WP.spec_imp_exists
    (initializer_data_offsets_available ops bound available m2 b2 0#usize (by simp)
      (by simpa [same2] using source.dataOffsets)
      (by rw [limits2,limits1]; simp [same2]; omega) demand.literalReserve
      (by simp [same2]; omega) (by simp [same2]; omega))
  dsimp only at accepted source3 size3 used3 limits3
  subst status
  have same3 : m3.module = module.module := source3.trans same2
  simp only [show (0#usize).val = 0 from rfl,Nat.sub_zero,same2] at size3 used3
  have functions : m3.functions.length ≤ initializerSize m3 := by
    simp only [initializerSize,alloc.vec.Vec.length]
    omega
  have suffixDemand : SegmentCompilationDemand m3 b3 bound := by
    constructor
    · rw [limits3,limits2,limits1]
      simp only [segmentCompilationDemand,same3] at *
      omega
    · simpa [segmentCompilationDemand,same3] using demand.codeCapacity
    · simpa [segmentCompilationDemand,same3] using demand.codeReserve
    · omega
    · omega
    · simpa [same3] using demand.elementCount
    · simpa [same3] using demand.dataCount
    · simpa [same3] using demand.elementLengths
    · simpa [same3] using demand.dataLengths
  unfold runtime.compiler.initialize.lower
  rw [call1]
  simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  rw [call2]
  simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  rw [call3]
  simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  change segmentCompilation ops m3 b3 ⦃ out => _ ⦄
  apply WP.spec_mono (segment_compilation_available ops law bound available m3 b3 suffixDemand
    (by simpa [same3] using source.elementOffsets) (by simpa [same3] using source.dataOffsets))
  intro out post
  refine ⟨post.1,post.2.1.trans same3,?_,?_⟩
  · exact post.2.2.1.trans (limits3.trans (limits2.trans limits1))
  · have suffixUsed := post.2.2.2
    simp only [segmentCompilationDemand,same3] at suffixUsed ⊢
    unfold initializerMappingCost
    omega

end Exec.Code
