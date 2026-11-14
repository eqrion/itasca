import Itasca.Runtime.Compiler.Local.Initializer.LowerContracts
import Itasca.Runtime.Compiler.Local.Initializer.SegmentLoopContracts
import Itasca.Runtime.Compiler.Local.Initializer.SegmentEmissionContracts
import Itasca.Runtime.Compiler.Module.CompileDriverFrame
import Itasca.Runtime.Compiler.Local.Capacity.UnreachableAvailability
import Itasca.Runtime.Compiler.Local.Relations.Segments.SegmentTranslation
import Itasca.Runtime.Compiler.Module.InitializerTotal
import Itasca.Module.Env.Basic
import Itasca.Runtime.Compiler.Local.Initializer

/-!
Sections, each formerly its own module: SegmentCompilationAvailable, InitializerCompilationAvailable.
-/

/-! ## SegmentCompilationAvailable -/

section

/-!
Successful data/element segment compilation from bounded segment demand. Per-segment emission and their folds establish the final segment compilation availability theorem.
-/

/-! ## Initializer Emit Data Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Data-segment bytecode emission accepts from source offset typing and a
conservative five-instruction demand. Source indices have independent u32 bounds. -/
theorem initializer_emit_data_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction) (index : Usize) (segment : Itasca.metadata.Data)
    (lookup : module.module.tail.data.val[index.val]? = some segment)
    (typed : ∀ memory offset, segment.mode = .Active memory offset →
      Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (instructions : budget.instructions.val + 5 ≤ budget.limits.max_instructions.val)
    (capacity : function.code.length + 5 ≤ Usize.max) (request : function.code.length + 5 ≤ bound)
    (indexBound : index.val ≤ U32.max) (lengthBound : segment.init.length ≤ U32.max) :
    runtime.compiler.initialize.emit_data ops module budget function index ⦃ out =>
      out.1 = .Ok () ∧ out.2.1.instructions.val ≤ budget.instructions.val + 5 ∧
      out.2.1.limits = budget.limits ∧ out.2.2.code.length ≤ function.code.length + 5 ∧
      out.2.2.v128_pool = function.v128_pool ∧ out.2.2.indirect = function.indirect ⦄ := by
  exact runtime.compiler.initialize.emit_data.available ops bound available module budget function index segment
    ⟨lookup, typed, instructions, capacity, request, indexBound, lengthBound⟩

end Itasca.Runtime.Compiler

end

/-! ## Initializer Emit Datas Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- The full source-ordered data bytecode loop accepts with five emitted
instructions per remaining source segment as conservative
demand. Offset literals require no pool allocation. -/
theorem initializer_emit_datas_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction) (index : Usize)
    (inside : index.val ≤ module.module.tail.data.val.length)
    (sourceCount : module.module.tail.data.length ≤ U32.max)
    (sourceLengths : ∀ segment ∈ module.module.tail.data.val, segment.init.length ≤ U32.max)
    (typed : ∀ segment ∈ module.module.tail.data.val, ∀ table offset,
      segment.mode = .Active table offset → Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (instructions : budget.instructions.val + 5*(module.module.tail.data.val.length-index.val) ≤
      budget.limits.max_instructions.val)
    (codeCapacity : function.code.length + 5*(module.module.tail.data.val.length-index.val) ≤ Usize.max)
    (codeReserve : function.code.length + 5*(module.module.tail.data.val.length-index.val) ≤ bound) :
    runtime.compiler.initialize.lower_loop4 ops module budget index (.Ok ()) function ⦃ out =>
      out.2.1 = .Ok () ∧ out.1.limits = budget.limits ∧
      out.1.instructions.val ≤ budget.instructions.val + 5*(module.module.tail.data.val.length-index.val) ∧
      out.2.2.code.length ≤ function.code.length + 5*(module.module.tail.data.val.length-index.val) ∧
      out.2.2.indirect = function.indirect ∧
      out.2.2.v128_pool = function.v128_pool ⦄ := by
  let P := fun (charged : runtime.compiler.Budget A) (current : runtime.bytecode.CompiledFunction) (cursor : Usize) =>
    charged.limits = budget.limits ∧
    charged.instructions.val + 5*(module.module.tail.data.val.length-cursor.val) ≤
      budget.instructions.val + 5*(module.module.tail.data.val.length-index.val) ∧
    current.code.length + 5*(module.module.tail.data.val.length-cursor.val) ≤
      function.code.length + 5*(module.module.tail.data.val.length-index.val) ∧
    current.indirect = function.indirect ∧ current.v128_pool = function.v128_pool
  change WP.spec (loop (initializerEmitDataLoop ops module).body (budget, index, .Ok (), function)) _
  apply InitializerSegmentLoop.available
    { rules := initializerEmitDataLoop ops module, budget := budget, function := function, index := index, bounded := inside,
      P := P, Q := fun charged after => charged.limits = budget.limits ∧
        charged.instructions.val ≤ budget.instructions.val + 5*(module.module.tail.data.val.length-index.val) ∧
        after.code.length ≤ function.code.length + 5*(module.module.tail.data.val.length-index.val) ∧
        after.indirect = function.indirect ∧ after.v128_pool = function.v128_pool,
      advance := ?_, finish := ?_, initial := ?_ }
  · intro charged current cursor position prior
    obtain ⟨limits, used, code, pairs, pool⟩ := prior
    change cursor.val < module.module.tail.data.val.length at position
    let segment := module.module.tail.data.val[cursor.val]'position
    have lookup : module.module.tail.data.val[cursor.val]? = some segment := List.getElem?_eq_getElem position
    apply WP.spec_mono (initializer_emit_data_available ops bound available module charged current cursor segment lookup
      (typed segment (List.getElem_mem position)) (by rw [limits]; omega) (by omega) (by omega)
      (by change module.module.tail.data.val.length ≤ U32.max at sourceCount; omega)
      (sourceLengths segment (List.getElem_mem position)))
    rintro ⟨result, nextBudget, next⟩ ⟨accepted, usedAgain, limitsAgain, codeAgain, poolAgain, pairsAgain⟩
    dsimp only at accepted usedAgain limitsAgain codeAgain poolAgain pairsAgain
    refine ⟨accepted, ?_⟩
    intro nextIndex increment
    exact ⟨limitsAgain.trans limits, by omega, by omega,
      pairsAgain.trans pairs, poolAgain.trans pool⟩
  · intro charged current cursor last prior
    obtain ⟨limits, used, code, pairs, pool⟩ := prior
    change cursor.val = module.module.tail.data.val.length at last
    exact ⟨limits, by omega, by omega, pairs, pool⟩
  · exact ⟨rfl, Nat.le_refl _, Nat.le_refl _, rfl, rfl⟩

end Itasca.Runtime.Compiler

end

/-! ## Initializer Emit Element Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Element-segment bytecode emission accepts from source offset typing and a
conservative five-instruction demand. Source indices have independent u32 bounds. -/
theorem initializer_emit_element_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction) (index : Usize) (segment : Itasca.metadata.Element)
    (lookup : module.module.env.elements.val[index.val]? = some segment)
    (typed : ∀ table offset, segment.mode = .Active table offset →
      Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (instructions : budget.instructions.val + 5 ≤ budget.limits.max_instructions.val)
    (capacity : function.code.length + 5 ≤ Usize.max) (request : function.code.length + 5 ≤ bound)
    (indexBound : index.val ≤ U32.max) (lengthBound : segment.init.length ≤ U32.max)
    (pairIndex : function.indirect.length ≤ U32.max)
    (pairCapacity : function.indirect.length < Usize.max)
    (pairReserve : function.indirect.length + 1 ≤ bound) :
    runtime.compiler.initialize.emit_element ops module budget function index ⦃ out =>
      out.1 = .Ok () ∧ out.2.1.instructions.val ≤ budget.instructions.val + 5 ∧
      out.2.1.limits = budget.limits ∧ out.2.2.code.length ≤ function.code.length + 5 ∧
      out.2.2.v128_pool = function.v128_pool ∧ out.2.2.indirect.length ≤ function.indirect.length + 1 ⦄ := by
  exact runtime.compiler.initialize.emit_element.available ops bound available module budget function index segment
    ⟨lookup, typed, instructions, capacity, request, indexBound, lengthBound, pairIndex, pairCapacity, pairReserve⟩

end Itasca.Runtime.Compiler

end

/-! ## Initializer Emit Elements Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- The full source-ordered element bytecode loop accepts with five emitted
instructions and one descriptor per remaining source segment as conservative
demand. Offset literals require no pool allocation. -/
theorem initializer_emit_elements_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction) (index : Usize)
    (inside : index.val ≤ module.module.env.elements.val.length)
    (sourceCount : module.module.env.elements.length ≤ U32.max)
    (sourceLengths : ∀ segment ∈ module.module.env.elements.val, segment.init.length ≤ U32.max)
    (typed : ∀ segment ∈ module.module.env.elements.val, ∀ table offset,
      segment.mode = .Active table offset → Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (instructions : budget.instructions.val + 5*(module.module.env.elements.val.length-index.val) ≤
      budget.limits.max_instructions.val)
    (codeCapacity : function.code.length + 5*(module.module.env.elements.val.length-index.val) ≤ Usize.max)
    (codeReserve : function.code.length + 5*(module.module.env.elements.val.length-index.val) ≤ bound)
    (pairCapacity : function.indirect.length + (module.module.env.elements.val.length-index.val) ≤ Usize.max)
    (pairReserve : function.indirect.length + (module.module.env.elements.val.length-index.val) ≤ bound)
    (pairWord : function.indirect.length + (module.module.env.elements.val.length-index.val) ≤ U32.max) :
    runtime.compiler.initialize.lower_loop3 ops module budget index (.Ok ()) function ⦃ out =>
      out.2.1 = .Ok () ∧ out.1.limits = budget.limits ∧
      out.1.instructions.val ≤ budget.instructions.val + 5*(module.module.env.elements.val.length-index.val) ∧
      out.2.2.code.length ≤ function.code.length + 5*(module.module.env.elements.val.length-index.val) ∧
      out.2.2.indirect.length ≤ function.indirect.length + (module.module.env.elements.val.length-index.val) ∧
      out.2.2.v128_pool = function.v128_pool ⦄ := by
  let P := fun (charged : runtime.compiler.Budget A) (current : runtime.bytecode.CompiledFunction) (cursor : Usize) =>
    charged.limits = budget.limits ∧
    charged.instructions.val + 5*(module.module.env.elements.val.length-cursor.val) ≤
      budget.instructions.val + 5*(module.module.env.elements.val.length-index.val) ∧
    current.code.length + 5*(module.module.env.elements.val.length-cursor.val) ≤
      function.code.length + 5*(module.module.env.elements.val.length-index.val) ∧
    current.indirect.length + (module.module.env.elements.val.length-cursor.val) ≤
      function.indirect.length + (module.module.env.elements.val.length-index.val) ∧ current.v128_pool = function.v128_pool
  change WP.spec (loop (initializerEmitElementLoop ops module).body (budget, index, .Ok (), function)) _
  apply InitializerSegmentLoop.available
    { rules := initializerEmitElementLoop ops module, budget := budget, function := function, index := index, bounded := inside,
      P := P, Q := fun charged after => charged.limits = budget.limits ∧
        charged.instructions.val ≤ budget.instructions.val + 5*(module.module.env.elements.val.length-index.val) ∧
        after.code.length ≤ function.code.length + 5*(module.module.env.elements.val.length-index.val) ∧
        after.indirect.length ≤ function.indirect.length + (module.module.env.elements.val.length-index.val) ∧ after.v128_pool = function.v128_pool,
      advance := ?_, finish := ?_, initial := ?_ }
  · intro charged current cursor position prior
    obtain ⟨limits, used, code, pairs, pool⟩ := prior
    change cursor.val < module.module.env.elements.val.length at position
    let segment := module.module.env.elements.val[cursor.val]'position
    have lookup : module.module.env.elements.val[cursor.val]? = some segment := List.getElem?_eq_getElem position
    apply WP.spec_mono (initializer_emit_element_available ops bound available module charged current cursor segment lookup
      (typed segment (List.getElem_mem position)) (by rw [limits]; omega) (by omega) (by omega)
      (by change module.module.env.elements.val.length ≤ U32.max at sourceCount; omega)
      (sourceLengths segment (List.getElem_mem position)) (by omega) (by omega) (by omega))
    rintro ⟨result, nextBudget, next⟩ ⟨accepted, usedAgain, limitsAgain, codeAgain, poolAgain, pairsAgain⟩
    dsimp only at accepted usedAgain limitsAgain codeAgain poolAgain pairsAgain
    refine ⟨accepted, ?_⟩
    intro nextIndex increment
    exact ⟨limitsAgain.trans limits, by omega, by omega,
      by omega, poolAgain.trans pool⟩
  · intro charged current cursor last prior
    obtain ⟨limits, used, code, pairs, pool⟩ := prior
    change cursor.val = module.module.env.elements.val.length at last
    exact ⟨limits, by omega, by omega, by omega, pool⟩
  · exact ⟨rfl, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, rfl⟩

end Itasca.Runtime.Compiler

end

/-! ## Segment Compilation -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std


end Itasca.Runtime.Compiler

end

/-! ## Segment Compilation Available -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

end

/-! ## InitializerCompilationAvailable -/

section

namespace Itasca.Runtime.Compiler
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
     (valid : Itasca.ModuleEnv.Valid module.module.env)
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
  refine WP.spec_mono (runtime.compiler.initialize.lower.available ops module budget
    ⟨m1, m2, m3, b1, b2, b3, call1, call2, call3⟩
    (fun status after afterBudget => status = .Ok () ∧ after.module = module.module ∧ afterBudget.limits = budget.limits ∧
      afterBudget.instructions.val ≤ budget.instructions.val + 2*initializerMappingCost module.module + segmentCompilationDemand module)
    ?_) ?_
  · change segmentCompilation ops m3 b3 ⦃ out => _ ⦄
    apply WP.spec_mono (segment_compilation_available ops law bound available m3 b3 suffixDemand
      (by simpa [same3] using source.elementOffsets) (by simpa [same3] using source.dataOffsets))
    rintro ⟨status, after, afterBudget⟩ post
    dsimp only at post ⊢
    refine ⟨post.1,post.2.1.trans same3,?_,?_⟩
    · exact post.2.2.1.trans (limits3.trans (limits2.trans limits1))
    · have suffixUsed := post.2.2.2
      simp only [segmentCompilationDemand,same3] at suffixUsed ⊢
      unfold initializerMappingCost
      omega


  · rintro ⟨status, after, afterBudget⟩ post
    exact post

end Itasca.Runtime.Compiler

end
