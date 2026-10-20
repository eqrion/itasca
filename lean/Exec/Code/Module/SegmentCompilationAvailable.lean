import Exec.Code.Module.SegmentCompilation

namespace Exec.Code
open Aeneas Aeneas.Std

def segmentCompilationDemand (module : runtime.compiler.ExecutableModule) : Nat :=
  5*(module.module.env.elements.val.length+module.module.tail.data.val.length)+1

/-- Source-derived requests for the generated segment program. The existing
function vector and native per-request allocation bound are accounted separately. -/
structure SegmentCompilationDemand {A : Type} (module : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (bound : Nat) : Prop where
  instructions : budget.instructions.val + segmentCompilationDemand module ≤ budget.limits.max_instructions.val
  codeCapacity : segmentCompilationDemand module ≤ Usize.max
  codeReserve : segmentCompilationDemand module ≤ bound
  functionsCapacity : module.functions.length < Usize.max
  functionsReserve : module.functions.length+1 ≤ bound
  elementCount : module.module.env.elements.length ≤ U32.max
  dataCount : module.module.tail.data.length ≤ U32.max
  elementLengths : ∀ segment ∈ module.module.env.elements.val, segment.init.length ≤ U32.max
  dataLengths : ∀ segment ∈ module.module.tail.data.val, segment.init.length ≤ U32.max

/-- The complete extracted segment suffix accepts from source typing and
independent numerical demand. The program certificate and checker result are
constructed before publication, not supplied as compiler-success premises. -/
theorem segment_compilation_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (demand : SegmentCompilationDemand module budget bound)
    (elementsTyped : ∀ segment ∈ module.module.env.elements.val, ∀ table offset,
      segment.mode = .Active table offset → Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (datasTyped : ∀ segment ∈ module.module.tail.data.val, ∀ memory offset,
      segment.mode = .Active memory offset → Itasca.ModuleConstants.Valid module.module.env offset .I32) :
    segmentCompilation ops module budget ⦃ out =>
      out.1 = .Ok () ∧ out.2.1.module = module.module ∧ out.2.2.limits = budget.limits ∧
      out.2.2.instructions.val ≤ budget.instructions.val+segmentCompilationDemand module ⦄ := by
  let seed := {initializerSeed .I32 with slot_count := 0#u32}
  have seedEq : runtime.bytecode.CompiledFunction.synthetic (alloc.vec.Vec.new _) 0#u32 = .ok seed := rfl
  have instructionRoom := demand.instructions
  have codeCapacity := demand.codeCapacity
  have codeReserve := demand.codeReserve
  simp only [segmentCompilationDemand] at instructionRoom codeCapacity codeReserve
  obtain ⟨⟨b1,status,first⟩,firstCall,accepted,limits1,used1,code1,pairs1,pool1⟩ := WP.spec_imp_exists
    (initializer_emit_elements_available ops bound available module budget seed 0#usize (by simp)
      demand.elementCount demand.elementLengths elementsTyped
      (by simpa [seed,initializerSeed] using (show budget.instructions.val+
        5*module.module.env.elements.val.length ≤ budget.limits.max_instructions.val by omega))
      (by simp [seed,initializerSeed] <;> omega) (by simp [seed,initializerSeed] <;> omega)
      (by simp [seed,initializerSeed] <;> omega) (by simp [seed,initializerSeed] <;> omega)
      (by simpa [seed,initializerSeed] using demand.elementCount))
  dsimp only at accepted limits1 used1 code1 pairs1 pool1
  subst status
  simp [seed,initializerSeed] at used1 code1 pairs1
  obtain ⟨elements,elementPrefix⟩ := element_program_loop ops law module seed seed first budget b1 0#usize []
    (.empty module seed) (by simp) elementsTyped firstCall
  obtain ⟨⟨b2,status,second⟩,secondCall,accepted,limits2,used2,code2,pairs2,pool2⟩ := WP.spec_imp_exists
    (initializer_emit_datas_available ops bound available module b1 first 0#usize (by simp)
      demand.dataCount demand.dataLengths datasTyped (by rw [limits1]; simp <;> omega)
      (by simp <;> omega) (by simp <;> omega))
  dsimp only at accepted limits2 used2 code2 pairs2 pool2
  subst status
  simp at used2 code2
  obtain ⟨datas,dataPrefix⟩ := data_program_loop ops law module first first second b1 b2 0#usize []
    (.empty module first) (by simp) datasTyped secondCall
  obtain ⟨⟨status,b3,finalCode⟩,emitCall,accepted,used3,limits3,appended⟩ := WP.spec_imp_exists
    (initializer_emit_available ops bound available b2 second.code (.Return 0#u32 0#u32)
      (by rw [limits2,limits1]; omega)
      (by change second.code.val.length < Usize.max; omega)
      (by change second.code.val.length + 1 ≤ bound; omega))
  dsimp only at accepted used3 limits3 appended
  subst status
  have program := segment_program_finish module seed first second finalCode elements datas elementPrefix dataPrefix
    appended (by simp [seed,initializerSeed]) (by simp [seed,initializerSeed]) rfl rfl rfl
  have metadata : second.body_start = 0#usize ∧ second.body_end = 0#usize ∧
      second.source_offsets.val = [] ∧ second.jump_tables.val = [] ∧ second.controls.val = [] := by
    rw [dataPrefix.fields,elementPrefix.fields]
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  obtain ⟨valid,checkCall,rfl⟩ := WP.spec_imp_exists
    (segment_program_well_formed program elementsTyped datasTyped metadata.1 metadata.2.1
      metadata.2.2.1 metadata.2.2.2.1 metadata.2.2.2.2)
  unfold segmentCompilation
  rw [seedEq,bind_ok,firstCall]
  simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  rw [secondCall]
  simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  rw [emitCall]
  simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  rw [checkCall]
  simp only [bind_ok,↓reduceIte]
  step with budget_push_available ops bound available b3 module.functions {second with code := finalCode}
    demand.functionsCapacity demand.functionsReserve
    as ⟨status,afterBudget,functions,accepted,sameBudget,appendedFunctions⟩
  refine ⟨accepted,?_,?_⟩
  · simpa [sameBudget,limits3,limits2] using limits1
  · simp only [sameBudget]
    unfold segmentCompilationDemand
    omega

end Exec.Code
