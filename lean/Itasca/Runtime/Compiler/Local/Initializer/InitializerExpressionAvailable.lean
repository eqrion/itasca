import Itasca.Runtime.Compiler.Local.Initializer.LowerContracts
import Itasca.Runtime.Compiler.Local.Initializer.SegmentEmissionContracts
import Itasca.Runtime.Compiler.Local.Initializer.ModuleLoopContracts
import Itasca.Runtime.Compiler.Local.Initializer.ExpressionContracts
import Itasca.Runtime.Compiler.Local.Initializer.ConstantContracts
import Itasca.Runtime.Compiler.Local.Initializer.InitializerElementAppend
import Itasca.Runtime.Compiler.Local.Relations.Instructions.WellFormedAcceptance
import Itasca.Runtime.Compiler.Local.Capacity.BudgetAvailability
import Itasca.Runtime.Compiler.Local.Initializer

/-!
Sections, each formerly its own module: InitializerElementLoop, InitializerComplete, InitializerAcceptance, InitializerExpressionAvailable.
-/

/-! ## InitializerElementLoop -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

def ElementValueMappings (functions : List runtime.bytecode.CompiledFunction)
    (segments : List Itasca.metadata.Element) (rows : List (alloc.vec.Vec Usize)) : Prop :=
  List.Forall₂ (fun segment indices => InitializerEntries functions segment.init.val
    (Itasca.ModuleConstants.referenceValueType segment.elem) indices.val) segments rows

def ElementOffsetMappings (functions : List runtime.bytecode.CompiledFunction)
    (segments : List Itasca.metadata.Element) (offsets : List (Option Usize)) : Prop :=
  List.Forall₂ (fun segment offset => OffsetInitializer functions (sourceElementOffset segment) offset)
    segments offsets

theorem ElementValueMappings.extend {before after : List runtime.bytecode.CompiledFunction}
    (prefixEq : after.take before.length = before) {segments rows}
    (entries : ElementValueMappings before segments rows) :
    ElementValueMappings after segments rows := by
  induction entries with
  | nil => exact .nil
  | cons cert rest ih => exact .cons (cert.extend prefixEq) ih

theorem ElementOffsetMappings.extend {before after : List runtime.bytecode.CompiledFunction}
    (prefixEq : after.take before.length = before) {segments offsets}
    (entries : ElementOffsetMappings before segments offsets) :
    ElementOffsetMappings after segments offsets := by
  induction entries with
  | nil => exact .nil
  | cons cert rest ih => exact .cons (cert.extend prefixEq) ih

def ElementModulePrefix (before current : runtime.compiler.ExecutableModule) (count : Nat) : Prop :=
  current = { before with functions := current.functions, element_initializers := current.element_initializers, element_offsets := current.element_offsets } ∧
  current.functions.val.take before.functions.length = before.functions.val ∧
  ElementValueMappings current.functions.val (before.module.env.elements.val.take count) current.element_initializers.val ∧
  ElementOffsetMappings current.functions.val (before.module.env.elements.val.take count) current.element_offsets.val

theorem initializer_prefix_trans {T : Type} {before middle after : List T}
    (first : middle.take before.length = before) (second : after.take middle.length = middle) :
    after.take before.length = before := by
  have length := congrArg List.length first
  simp only [List.length_take] at length
  have bound : before.length ≤ middle.length := by omega
  rw [← second, List.take_take, Nat.min_eq_left bound] at first
  exact first

theorem element_module_append {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (prefixInv : ElementModulePrefix before current index.val)
    (bound : index.val < before.module.env.elements.val.length)
    (success : runtime.compiler.initialize.lower_element ops current budget index =
      .ok (.Ok (), after, budgetAfter)) : ElementModulePrefix before after (index.val + 1) := by
  obtain ⟨unchanged, prefixEq, entries, offsets⟩ := prefixInv
  have source := congrArg runtime.compiler.ExecutableModule.module unchanged
  dsimp only at source
  let segment := before.module.env.elements.val[index.val]
  have found : current.module.env.elements.val[index.val]? = some segment := by
    rw [source]
    exact List.getElem?_eq_getElem bound
  obtain ⟨row, offset, changed, functions, rows, offsetList, valuesCert, offsetCert⟩ :=
    initializer_lower_element ops law current after budget budgetAfter index segment found success
  have extended := entries.extend functions
  have extendedOffsets := offsets.extend functions
  refine ⟨?_, initializer_prefix_trans prefixEq functions, ?_, ?_⟩
  · rw [changed]
    conv_lhs => rw [unchanged]
  · unfold ElementValueMappings at extended ⊢
    rw [List.take_add_one, rows]
    simpa [List.getElem?_eq_getElem bound, segment] using
      List.rel_append extended (.cons valuesCert .nil)
  · unfold ElementOffsetMappings at extendedOffsets ⊢
    rw [List.take_add_one, offsetList]
    simpa [List.getElem?_eq_getElem bound, segment] using
      List.rel_append extendedOffsets (.cons offsetCert .nil)

theorem initializer_elements_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (prefixInv : ElementModulePrefix before current index.val)
    (bound : index.val ≤ before.module.env.elements.val.length)
    (success : runtime.compiler.initialize.lower_loop1 ops current budget index (.Ok ()) =
      .ok (after, budgetAfter, .Ok ())) :
    ElementModulePrefix before after before.module.env.elements.val.length := by
  have source := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) prefixInv.1
  let P := fun next (_ : runtime.compiler.Budget A) (cursor : Usize) (result : core.result.Result Unit Itasca.error.VisitError) =>
    result = .Ok () → cursor.val ≤ before.module.env.elements.val.length ∧ ElementModulePrefix before next cursor.val
  let Q := fun next (_ : runtime.compiler.Budget A) (result : core.result.Result Unit Itasca.error.VisitError) =>
    result = .Ok () → ElementModulePrefix before next before.module.env.elements.val.length
  have preserved := InitializerModuleLoop.inv
    { rules := initializerElementLoop ops, before := current, budget := budget, j := index, status := .Ok (),
      length := alloc.vec.Vec.len before.module.env.elements,
      lengthEq := by simpa only [initializerElementLoop, source], P := P, Q := Q,
      advance := (by
      intro next charged cursor same inside prior result later laterBudget nextIndex called increment accepted
      subst result
      obtain ⟨position, mapped⟩ := prior rfl
      change cursor.val < before.module.env.elements.val.length at inside
      have appended := element_module_append ops law before next later charged laterBudget cursor mapped inside called
      exact ⟨by omega, by simpa only [increment] using appended⟩),
      finish := (by
      intro next charged cursor result same prior stopped accepted
      obtain ⟨position, mapped⟩ := prior accepted
      have last := stopped.resolve_right (by intro rejected; exact rejected accepted)
      have equal : cursor.val = before.module.env.elements.val.length := by
        change before.module.env.elements.val.length ≤ cursor.val at last
        omega
      simpa only [equal] using mapped), initial := fun _ => ⟨bound, prefixInv⟩ }
    after budgetAfter (.Ok ()) success
  exact preserved rfl

end Itasca.Runtime.Compiler

end

/-! ## InitializerComplete -/

section

/-!
Data offset mappings and complete initializer lowering. The mapping evidence connects source data declarations to the initializer module certificate.
-/

/-! ## Initializer Data Mappings -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

def sourceDataOffset (segment : Itasca.metadata.Data) : Option Itasca.wasm_types.ConstExpr :=
  match segment.mode with
  | .Active _ expr => some expr
  | .Passive => none

theorem initializer_lower_data {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (segment : Itasca.metadata.Data)
    (found : module.module.tail.data.val[index.val]? = some segment)
    (success : runtime.compiler.initialize.lower_data_offset ops module budget index =
      .ok (.Ok (), after, budgetAfter)) :
    ∃ offset,
      after = { module with functions := after.functions, data_offsets := after.data_offsets } ∧
      after.functions.val.take module.functions.length = module.functions.val ∧
      after.data_offsets.val = module.data_offsets.val ++ [offset] ∧
      OffsetInitializer after.functions.val (sourceDataOffset segment) offset := by
  cases mode : segment.mode with
  | Passive =>
    obtain ⟨changed, offsets⟩ := initializer_lower_data_passive ops law module after budget budgetAfter index
      segment found mode success
    have functions := congrArg runtime.compiler.ExecutableModule.functions changed
    dsimp only at functions
    refine ⟨none, ?_, ?_, offsets, ?_⟩
    · rw [changed]
    · simp [functions]
    · simp [OffsetInitializer, sourceDataOffset, mode]
  | Active memory expr =>
    obtain ⟨function, fnIndex, certificate, position, changed, functions, offsets⟩ :=
      initializer_lower_data_active ops law module after budget budgetAfter index segment memory expr found mode success
    refine ⟨some fnIndex, changed, ?_, offsets, ?_⟩
    · simp [functions]
    · simp only [OffsetInitializer, sourceDataOffset, mode]
      refine ⟨function, ?_, certificate⟩
      rw [functions, position]
      simp

def DataOffsetMappings (functions : List runtime.bytecode.CompiledFunction)
    (segments : List Itasca.metadata.Data) (offsets : List (Option Usize)) : Prop :=
  List.Forall₂ (fun segment offset => OffsetInitializer functions (sourceDataOffset segment) offset)
    segments offsets

theorem DataOffsetMappings.extend {before after : List runtime.bytecode.CompiledFunction}
    (prefixEq : after.take before.length = before) {segments offsets}
    (entries : DataOffsetMappings before segments offsets) :
    DataOffsetMappings after segments offsets := by
  induction entries with
  | nil => exact .nil
  | cons cert rest ih => exact .cons (cert.extend prefixEq) ih

def DataMappingPrefix (before current : runtime.compiler.ExecutableModule) (count : Nat) : Prop :=
  current = { before with functions := current.functions, data_offsets := current.data_offsets } ∧
  current.functions.val.take before.functions.length = before.functions.val ∧
  DataOffsetMappings current.functions.val (before.module.tail.data.val.take count) current.data_offsets.val

theorem data_mapping_append {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (prefixInv : DataMappingPrefix before current index.val)
    (bound : index.val < before.module.tail.data.val.length)
    (success : runtime.compiler.initialize.lower_data_offset ops current budget index =
      .ok (.Ok (), after, budgetAfter)) : DataMappingPrefix before after (index.val + 1) := by
  obtain ⟨unchanged, prefixEq, offsets⟩ := prefixInv
  have source := congrArg runtime.compiler.ExecutableModule.module unchanged
  dsimp only at source
  let segment := before.module.tail.data.val[index.val]
  have found : current.module.tail.data.val[index.val]? = some segment := by
    rw [source]
    exact List.getElem?_eq_getElem bound
  obtain ⟨offset, changed, functions, offsetList, offsetCert⟩ :=
    initializer_lower_data ops law current after budget budgetAfter index segment found success
  have extendedOffsets := offsets.extend functions
  refine ⟨?_, initializer_prefix_trans prefixEq functions, ?_⟩
  · rw [changed]
    conv_lhs => rw [unchanged]
  · unfold DataOffsetMappings at extendedOffsets ⊢
    rw [List.take_add_one, offsetList]
    simpa [List.getElem?_eq_getElem bound, segment] using
      List.rel_append extendedOffsets (.cons offsetCert .nil)

theorem initializer_data_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (prefixInv : DataMappingPrefix before current index.val)
    (bound : index.val ≤ before.module.tail.data.val.length)
    (success : runtime.compiler.initialize.lower_loop2 ops current budget index (.Ok ()) =
      .ok (after, budgetAfter, .Ok ())) :
    DataMappingPrefix before after before.module.tail.data.val.length := by
  have source := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) prefixInv.1
  let P := fun next (_ : runtime.compiler.Budget A) (cursor : Usize) (result : core.result.Result Unit Itasca.error.VisitError) =>
    result = .Ok () → cursor.val ≤ before.module.tail.data.val.length ∧ DataMappingPrefix before next cursor.val
  let Q := fun next (_ : runtime.compiler.Budget A) (result : core.result.Result Unit Itasca.error.VisitError) =>
    result = .Ok () → DataMappingPrefix before next before.module.tail.data.val.length
  have preserved := InitializerModuleLoop.inv
    { rules := initializerDataOffsetLoop ops, before := current, budget := budget, j := index, status := .Ok (),
      length := alloc.vec.Vec.len before.module.tail.data,
      lengthEq := by simpa only [initializerDataOffsetLoop, source], P := P, Q := Q,
      advance := (by
      intro next charged cursor same inside prior result later laterBudget nextIndex called increment accepted
      subst result
      obtain ⟨position, mapped⟩ := prior rfl
      change cursor.val < before.module.tail.data.val.length at inside
      have appended := data_mapping_append ops law before next later charged laterBudget cursor mapped inside called
      exact ⟨by omega, by simpa only [increment] using appended⟩),
      finish := (by
      intro next charged cursor result same prior stopped accepted
      obtain ⟨position, mapped⟩ := prior accepted
      have last := stopped.resolve_right (by intro rejected; exact rejected accepted)
      have equal : cursor.val = before.module.tail.data.val.length := by
        change before.module.tail.data.val.length ≤ cursor.val at last
        omega
      simpa only [equal] using mapped), initial := fun _ => ⟨bound, prefixInv⟩ }
    after budgetAfter (.Ok ()) success
  exact preserved rfl

end Itasca.Runtime.Compiler

end

/-! ## Initializer Complete -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Source-indexed certificates for every retained read-only initializer. The
separate segment-writing initialization function is not covered by this record. -/
structure InitializerMappings (module : runtime.compiler.ExecutableModule) : Prop where
  globals : GlobalInitializerEntries module.functions.val module.module.env.globals.val module.global_initializers.val
  elementValues : ElementValueMappings module.functions.val module.module.env.elements.val module.element_initializers.val
  elementOffsets : ElementOffsetMappings module.functions.val module.module.env.elements.val module.element_offsets.val
  dataOffsets : DataOffsetMappings module.functions.val module.module.tail.data.val module.data_offsets.val

/-- The three actual mapping passes establish all read-only initializer maps.
Both semantic consumers share this argument before inspecting publication. -/
theorem InitializerMappingTrace.mappings {A : Type} {ops : runtime.platform.Alloc A}
    {module : runtime.compiler.ExecutableModule} {budget : runtime.compiler.Budget A}
    (stages : InitializerMappingTrace ops module budget) (law : Platform.AllocCorrect ops)
    (emptyGlobals : module.global_initializers.val = [])
    (emptyElements : module.element_initializers.val = [])
    (emptyElementOffsets : module.element_offsets.val = [])
    (emptyDataOffsets : module.data_offsets.val = []) :
    stages.data.module = module.module ∧
      stages.data.functions.val.take module.functions.length = module.functions.val ∧ InitializerMappings stages.data := by
  rcases stages with ⟨globalsModule, elementsModule, dataModule, b1, b2, b3, globalsCall, elementsCall, dataCall⟩
  have initialGlobals : GlobalMappingPrefix module module 0 := by
    refine ⟨rfl, by simp, ?_⟩
    simp only [GlobalInitializerEntries, List.take_zero, emptyGlobals]
    exact .nil
  obtain ⟨globalsChanged, globalsPrefix, globalsCert⟩ := initializer_global_loop ops law module module globalsModule
    budget b1 0#usize initialGlobals (by simp) globalsCall
  simp only [List.take_length] at globalsCert
  have globalSource := congrArg runtime.compiler.ExecutableModule.module globalsChanged
  have globalRows := congrArg runtime.compiler.ExecutableModule.element_initializers globalsChanged
  have globalOffsets := congrArg runtime.compiler.ExecutableModule.element_offsets globalsChanged
  have globalData := congrArg runtime.compiler.ExecutableModule.data_offsets globalsChanged
  dsimp only at globalSource globalRows globalOffsets globalData
  have initialElements : ElementModulePrefix globalsModule globalsModule 0 := by
    refine ⟨rfl, by simp, ?_, ?_⟩
    · simp only [ElementValueMappings, List.take_zero, globalRows, emptyElements]
      exact .nil
    · simp only [ElementOffsetMappings, List.take_zero, globalOffsets, emptyElementOffsets]
      exact .nil
  obtain ⟨elementsChanged, elementsPrefix, elementsCert, elementOffsetsCert⟩ :=
    initializer_elements_loop ops law globalsModule globalsModule elementsModule b1 b2 0#usize initialElements (by simp) elementsCall
  simp only [List.take_length] at elementsCert elementOffsetsCert
  have elementSource := congrArg runtime.compiler.ExecutableModule.module elementsChanged
  have elementGlobals := congrArg runtime.compiler.ExecutableModule.global_initializers elementsChanged
  have elementData := congrArg runtime.compiler.ExecutableModule.data_offsets elementsChanged
  dsimp only at elementSource elementGlobals elementData
  have initialData : DataMappingPrefix elementsModule elementsModule 0 := by
    refine ⟨rfl, by simp, ?_⟩
    simp only [DataOffsetMappings, List.take_zero, elementData, globalData, emptyDataOffsets]
    exact .nil
  obtain ⟨dataChanged, dataPrefix, dataCert⟩ := initializer_data_loop ops law elementsModule elementsModule dataModule
    b2 b3 0#usize initialData (by simp) dataCall
  simp only [List.take_length] at dataCert
  have dataSource := congrArg runtime.compiler.ExecutableModule.module dataChanged
  have dataGlobals := congrArg runtime.compiler.ExecutableModule.global_initializers dataChanged
  have dataRows := congrArg runtime.compiler.ExecutableModule.element_initializers dataChanged
  have dataOffsets := congrArg runtime.compiler.ExecutableModule.element_offsets dataChanged
  dsimp only at dataSource dataGlobals dataRows dataOffsets
  have allPrefix := initializer_prefix_trans (initializer_prefix_trans globalsPrefix elementsPrefix) dataPrefix
  have allGlobals := globalsCert.extend (initializer_prefix_trans elementsPrefix dataPrefix)
  have allElements := elementsCert.extend dataPrefix
  have allOffsets := elementOffsetsCert.extend dataPrefix
  have mapped : InitializerMappings dataModule := by
    constructor
    · simpa only [dataSource, elementSource, globalSource, dataGlobals, elementGlobals] using allGlobals
    · simpa only [dataSource, elementSource, dataRows] using allElements
    · simpa only [dataSource, elementSource, dataOffsets] using allOffsets
    · simpa only [dataSource] using dataCert
  exact ⟨dataSource.trans (elementSource.trans globalSource), allPrefix, mapped⟩

/-- The actual complete initializer-lowering pass establishes all retained
read-only initializer maps. It starts from empty maps, as the compiler does.
This successful-result theorem neither assumes nor proves termination of the
independent segment-writing bytecode checker. -/
theorem initializer_lower {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A)
    (emptyGlobals : module.global_initializers.val = [])
    (emptyElements : module.element_initializers.val = [])
    (emptyElementOffsets : module.element_offsets.val = [])
    (emptyDataOffsets : module.data_offsets.val = [])
    (success : runtime.compiler.initialize.lower ops module budget = .ok (.Ok (), after, budgetAfter)) :
    after.module = module.module ∧
      after.functions.val.take module.functions.length = module.functions.val ∧ InitializerMappings after := by
  obtain ⟨stages, ⟨publication⟩⟩ := runtime.compiler.initialize.lower.success ops module after budget budgetAfter success
  have mapping := stages.mappings law emptyGlobals emptyElements emptyElementOffsets emptyDataOffsets
  rcases stages with ⟨globalsModule, elementsModule, dataModule, b1, b2, b3, globalsCall, elementsCall, dataCall⟩
  rcases publication with ⟨function, function1, function2, b4, b5, b6, code, functions,
    seed, emitElements, emitData, emitReturn, check, pushed, frame⟩
  obtain ⟨sourceAll, allPrefix, mapped⟩ := mapping
  change dataModule.module = module.module at sourceAll
  subst after
  obtain ⟨_, functionsEq⟩ := budget_push_success ops law b6 budgetAfter dataModule.functions functions
    { function2 with code := code } pushed
  have prefixFinal : functions.val.take dataModule.functions.length = dataModule.functions.val := by
    simp [functionsEq]
  refine ⟨sourceAll,

    initializer_prefix_trans allPrefix prefixFinal, ?_⟩
  exact ⟨mapped.globals.extend prefixFinal, mapped.elementValues.extend prefixFinal,
    mapped.elementOffsets.extend prefixFinal, mapped.dataOffsets.extend prefixFinal⟩

end Itasca.Runtime.Compiler

end

end

/-! ## InitializerAcceptance -/

section

/-! Acceptance of synthetic initializers from source shape and available
resources, rather than an assumed successful publication check. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

end Itasca.Runtime.Compiler

end

/-! ## InitializerExpressionAvailable -/

section

/-!
Availability of constant initializer instructions and complete initializer expressions. The expression proof composes actual constant callback success under allocator availability.
-/

/-! ## Initializer Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

end Itasca.Runtime.Compiler

end

/-! ## Initializer Expression Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Source-shaped constant initializers compile and publish successfully with
two remaining instructions and independently bounded reserve availability.
This covers every constant-expression form, including SIMD and references. -/
theorem initializer_expression_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType)
    (vector : ∀ lo hi, expr = .V128 lo hi → ty = .V128)
    (instructions : budget.instructions.val + 2 ≤ budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound) (functionsRequest : module.functions.length + 1 ≤ bound)
    (functionsFit : module.functions.length < Usize.max) :
    runtime.compiler.initialize.expression ops module budget expr ty ⦃ out =>
      out.1 = .Ok (alloc.vec.Vec.len module.functions) ∧
      out.2.2.instructions.val = budget.instructions.val + 2 ∧
      out.2.2.limits = budget.limits ∧
      ∃ function, InitializerCode function expr ty ∧
        out.2.1.functions.val = module.functions.val ++ [function] ∧
        out.2.1 = {module with functions := out.2.1.functions} ⦄ := by
  apply WP.spec_mono (runtime.compiler.initialize.expression.available ops bound available module budget expr ty
    vector instructions codeRequest functionsRequest functionsFit)
  rintro ⟨status, after, afterBudget⟩ post
  exact post

end Itasca.Runtime.Compiler

end

end
