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
  classical
  let measure := fun p : runtime.compiler.ExecutableModule × runtime.compiler.Budget A × Usize ×
      core.result.Result Unit Itasca.error.VisitError =>
    if p.2.2.2 = .Ok () then before.module.env.elements.val.length - p.2.2.1.val + 1 else 0
  let inv := fun p : runtime.compiler.ExecutableModule × runtime.compiler.Budget A × Usize ×
      core.result.Result Unit Itasca.error.VisitError =>
    p.2.2.2 = .Ok () → p.2.2.1.val ≤ before.module.env.elements.val.length ∧
      ElementModulePrefix before p.1 p.2.2.1.val
  let post := fun p : runtime.compiler.ExecutableModule × runtime.compiler.Budget A ×
      core.result.Result Unit Itasca.error.VisitError =>
    p.2.2 = .Ok () → ElementModulePrefix before p.1 before.module.env.elements.val.length
  have sound : ∀ state, inv state → ∀ flow,
      runtime.compiler.initialize.lower_loop1.body ops state.1 state.2.1 state.2.2.1 state.2.2.2 = .ok flow →
      match flow with
      | .cont next => inv next ∧ measure next < measure state
      | .done out => post out := by
    rintro ⟨module, b, i, status⟩ hinv flow body
    dsimp only [inv] at hinv
    unfold runtime.compiler.initialize.lower_loop1.body at body
    simp only [runtime.compiler.ExecutableModule.env.eq,
      Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.elements, bind_ok] at body
    cases status with
    | Err error =>
      simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte] at body
      split at body <;> (have hf := Result.ok_injective body; subst flow; simp [post])
    | Ok unit =>
      cases unit
      obtain ⟨hi, prefixInv⟩ := hinv rfl
      have source := congrArg runtime.compiler.ExecutableModule.module prefixInv.1
      dsimp only at source
      rw [source] at body
      simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte] at body
      split at body
      · rename_i more
        have hmore : i.val < before.module.env.elements.val.length := by
          simpa [alloc.vec.Vec.deref] using more
        obtain ⟨⟨result, nextModule, nextBudget⟩, lowered, rest⟩ := initializer_bind_success body
        obtain ⟨nextIndex, added, rest⟩ := initializer_bind_success rest
        have output := Result.ok_injective rest
        subst flow
        have addSpec : i + 1#usize ⦃ next => next.val = i.val + 1 ⦄ := by
          have size := before.module.env.elements.property
          step as ⟨next, hnext⟩
          scalar_tac
        rw [added] at addSpec
        simp only [WP.spec_ok] at addSpec
        cases result with
        | Err error => simp [inv, measure]
        | Ok unit =>
          cases unit
          have nextPrefix := element_module_append ops law before module nextModule b nextBudget i prefixInv hmore lowered
          refine ⟨?_, ?_⟩
          · dsimp only [inv]
            intro _
            exact ⟨by omega, by simpa [addSpec] using nextPrefix⟩
          · simp only [measure, ↓reduceIte]
            omega
      · rename_i stopped
        have stop : i.val = before.module.env.elements.val.length := by
          simp [alloc.vec.Vec.deref] at stopped
          omega
        have output := Result.ok_injective body
        subst flow
        dsimp only [post]
        intro _
        simpa [stop] using prefixInv
  have result := initializer_loop_success
    (fun p => runtime.compiler.initialize.lower_loop1.body ops p.1 p.2.1 p.2.2.1 p.2.2.2)
    measure inv post (by
      intro state hstate flow hflow
      cases flow <;> exact sound state hstate _ hflow) (current, budget, index, .Ok ()) (by exact fun _ => ⟨bound, prefixInv⟩)
    (after, budgetAfter, .Ok ()) success
  exact result rfl

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
  classical
  let measure := fun p : runtime.compiler.ExecutableModule × runtime.compiler.Budget A × Usize ×
      core.result.Result Unit Itasca.error.VisitError =>
    if p.2.2.2 = .Ok () then before.module.tail.data.val.length - p.2.2.1.val + 1 else 0
  let inv := fun p : runtime.compiler.ExecutableModule × runtime.compiler.Budget A × Usize ×
      core.result.Result Unit Itasca.error.VisitError =>
    p.2.2.2 = .Ok () → p.2.2.1.val ≤ before.module.tail.data.val.length ∧
      DataMappingPrefix before p.1 p.2.2.1.val
  let post := fun p : runtime.compiler.ExecutableModule × runtime.compiler.Budget A ×
      core.result.Result Unit Itasca.error.VisitError =>
    p.2.2 = .Ok () → DataMappingPrefix before p.1 before.module.tail.data.val.length
  have sound : ∀ state, inv state → ∀ flow,
      runtime.compiler.initialize.lower_loop2.body ops state.1 state.2.1 state.2.2.1 state.2.2.2 = .ok flow →
      match flow with
      | .cont next => inv next ∧ measure next < measure state
      | .done out => post out := by
    rintro ⟨module, b, i, status⟩ hinv flow body
    dsimp only [inv] at hinv
    unfold runtime.compiler.initialize.lower_loop2.body at body
    simp only [runtime.compiler.ExecutableModule.tail.eq,
      Itasca.metadata.Module.impl.tail, bind_ok] at body
    cases status with
    | Err error =>
      simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte] at body
      split at body <;> (have hf := Result.ok_injective body; subst flow; simp [post])
    | Ok unit =>
      cases unit
      obtain ⟨hi, prefixInv⟩ := hinv rfl
      have source := congrArg runtime.compiler.ExecutableModule.module prefixInv.1
      dsimp only at source
      rw [source] at body
      simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte] at body
      split at body
      · rename_i more
        have hmore : i.val < before.module.tail.data.val.length := by
          simpa [alloc.vec.Vec.deref] using more
        obtain ⟨⟨result, nextModule, nextBudget⟩, lowered, rest⟩ := initializer_bind_success body
        obtain ⟨nextIndex, added, rest⟩ := initializer_bind_success rest
        have output := Result.ok_injective rest
        subst flow
        have addSpec : i + 1#usize ⦃ next => next.val = i.val + 1 ⦄ := by
          have size := before.module.tail.data.property
          step as ⟨next, hnext⟩
          scalar_tac
        rw [added] at addSpec
        simp only [WP.spec_ok] at addSpec
        cases result with
        | Err error => simp [inv, measure]
        | Ok unit =>
          cases unit
          have nextPrefix := data_mapping_append ops law before module nextModule b nextBudget i prefixInv hmore lowered
          refine ⟨?_, ?_⟩
          · dsimp only [inv]
            intro _
            exact ⟨by omega, by simpa [addSpec] using nextPrefix⟩
          · simp only [measure, ↓reduceIte]
            omega
      · rename_i stopped
        have stop : i.val = before.module.tail.data.val.length := by
          simp [alloc.vec.Vec.deref] at stopped
          omega
        have output := Result.ok_injective body
        subst flow
        dsimp only [post]
        intro _
        simpa [stop] using prefixInv
  have result := initializer_loop_success
    (fun p => runtime.compiler.initialize.lower_loop2.body ops p.1 p.2.1 p.2.2.1 p.2.2.2)
    measure inv post (by
      intro state hstate flow hflow
      cases flow <;> exact sound state hstate _ hflow) (current, budget, index, .Ok ()) (by exact fun _ => ⟨bound, prefixInv⟩)
    (after, budgetAfter, .Ok ()) success
  exact result rfl

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
  unfold runtime.compiler.initialize.lower at success
  obtain ⟨⟨globalsModule, b1, result⟩, globalsCall, rest⟩ := initializer_bind_success success
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok unit =>
    cases unit
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
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair] at rest
    obtain ⟨⟨elementsModule, b2, result⟩, elementsCall, rest⟩ := initializer_bind_success rest
    cases result with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok unit =>
      cases unit
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
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair] at rest
      obtain ⟨⟨dataModule, b3, result⟩, dataCall, rest⟩ := initializer_bind_success rest
      cases result with
      | Err error =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | Ok unit =>
        cases unit
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
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair] at rest
        obtain ⟨function, seed, rest⟩ := initializer_bind_success rest
        obtain ⟨⟨b4, result, function1⟩, emitElements, rest⟩ := initializer_bind_success rest
        cases result with
        | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
        | Ok unit =>
          cases unit
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair] at rest
          obtain ⟨⟨b5, result, function2⟩, emitData, rest⟩ := initializer_bind_success rest
          cases result with
          | Err error =>
            simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
          | Ok unit =>
            cases unit
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair] at rest
            obtain ⟨⟨result, b6, code⟩, emitReturn, rest⟩ := initializer_bind_success rest
            cases result with
            | Err error =>
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
            | Ok unit =>
              cases unit
              simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair] at rest
              obtain ⟨checked, check, rest⟩ := initializer_bind_success rest
              cases checked with
              | false => simp at rest
              | true =>
                simp only [↓reduceIte] at rest
                obtain ⟨⟨result, b7, functions⟩, pushed, rest⟩ := initializer_bind_success rest
                have output := Result.ok_injective rest
                have sameResult := congrArg Prod.fst output
                dsimp only at sameResult
                subst result
                have fields := congrArg (fun out => out.2.1) output
                dsimp only at fields
                subst after
                obtain ⟨_, functionsEq⟩ := budget_push_success ops law b6 b7 dataModule.functions functions
                  { function2 with code := code } pushed
                have prefixFinal : functions.val.take dataModule.functions.length = dataModule.functions.val := by
                  simp [functionsEq]
                refine ⟨dataSource.trans (elementSource.trans globalSource),

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

private theorem slots_fit_zero (function : runtime.bytecode.CompiledFunction) (count : U32)
    (bounded : count.val ≤ function.slot_count.val) :
    runtime.bytecode.CompiledFunction.slots_fit function 0#u32 count = .ok true := by
  have below : 0#u32 ≤ function.slot_count := by scalar_tac
  simp only [runtime.bytecode.CompiledFunction.slots_fit,if_pos below]
  have check : runtime.bytecode.CompiledFunction.slots_fit function 0#u32 count
      ⦃ result => result = true ⦄ := by
    unfold runtime.bytecode.CompiledFunction.slots_fit
    simp only [if_pos below]
    step as ⟨left,equal⟩
    have fits : count ≤ left := by scalar_tac
    simp [fits]
  obtain ⟨result,actual,rfl⟩ := WP.spec_imp_exists check
  exact actual

/-- The only extra width condition is independently visible in the source:
a vector literal requires a vector result slot. Other constant-expression
forms fit the width selected from their result type. -/
theorem initial_instruction_accepts (function : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) (instruction : runtime.bytecode.Instr)
    (lowered : InitialInstruction function expr ty instruction)
    (capacity : function.slot_count = initializerWidth ty)
    (vector : ∀ lo hi, expr = .V128 lo hi → ty = .V128) :
    runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true := by
  have scalar : runtime.bytecode.CompiledFunction.slots_fit function 0#u32 1#u32 = .ok true := by
    apply slots_fit_zero
    rw [capacity]
    cases ty <;> decide
  have wide (same : ty = .V128) :
      runtime.bytecode.CompiledFunction.slots_fit function 0#u32 2#u32 = .ok true := by
    apply slots_fit_zero
    simp [capacity,same,initializerWidth]
  cases lowered <;>
    simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.Instr.scalar,
      runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,
      runtime.bytecode.CompiledFunction.other_valid,bind_ok]
  all_goals first | exact scalar | exact wide rfl | skip
  rename_i lo hi pool embedded
  rw [wide (vector lo hi rfl),bind_ok]
  have inside := (List.getElem?_eq_some_iff.mp embedded).1
  have poolBound : UScalar.cast .Usize pool < alloc.vec.Vec.len function.v128_pool := by scalar_tac
  simpa [lift] using inside

/-- Exact initializer code and source metadata imply the actual publication
checker accepts. Component checker success is derived here, not assumed. -/
theorem initializer_well_formed (function : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType)
    (shape : InitializerCode function expr ty)
    (start : function.body_start = 0#usize) (finish : function.body_end = 0#usize)
    (offsets : function.source_offsets.val = []) (jumps : function.jump_tables.val = [])
    (controls : function.controls.val = [])
    (vector : ∀ lo hi, expr = .V128 lo hi → ty = .V128) :
    runtime.bytecode.CompiledFunction.well_formed function ⦃ result => result = true ⦄ := by
  obtain ⟨instruction,lowered,code⟩ := shape.code
  have length : function.code.length = 2 := by simp [alloc.vec.Vec.length,code]
  apply well_formed_synthetic_accepts function start finish (by omega) offsets
    (by rw [shape.localSlots,shape.capacity]; cases ty <;> decide)
    (by rw [shape.paramSlots,shape.localSlots]) 0#u32 (initializerWidth ty)
  · simp [length,code]
  · intro j bounded
    rw [length] at bounded
    have first := initial_instruction_accepts function expr ty instruction lowered shape.capacity vector
    have returned : runtime.bytecode.CompiledFunction.instruction_valid function
        (.Return 0#u32 (initializerWidth ty)) = .ok true := by
      simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.Instr.scalar,
        runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,
      runtime.bytecode.CompiledFunction.other_valid,bind_ok]
      exact slots_fit_zero function (initializerWidth ty) (by rw [shape.capacity])
    interval_cases j <;> simpa [code] using (by assumption)
  · simp [jumps]
  · simp [controls]

/-- One available instruction emission consumes one unit of instruction budget
and appends its instruction. Bounds are on actual reserve demand. -/
theorem initializer_emit_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (code : alloc.vec.Vec runtime.bytecode.Instr)
    (instruction : runtime.bytecode.Instr)
    (room : budget.instructions.val < budget.limits.max_instructions.val)
    (fits : code.length < Usize.max) (request : code.length + 1 ≤ bound) :
    runtime.compiler.initialize.emit ops budget code instruction ⦃ out =>
      out.1 = .Ok () ∧ out.2.1.instructions.val = budget.instructions.val + 1 ∧
      out.2.1.limits = budget.limits ∧ out.2.2.val = code.val ++ [instruction] ⦄ := by
  unfold runtime.compiler.initialize.emit
  step with charge_instruction_available ops budget room as ⟨status,charged,success,used,limits,error⟩
  rw [success]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  apply WP.spec_mono (budget_push_available ops bound available charged code instruction fits request)
  rintro ⟨status,after,values⟩ ⟨rfl,rfl,appended⟩
  exact ⟨rfl,used,limits,appended⟩

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

/-- All constant-expression forms lower successfully with one remaining
instruction and independently available code/pool reserves. -/
theorem initializer_constant_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (function : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) (dst : U32)
    (room : budget.instructions.val < budget.limits.max_instructions.val)
    (codeFits : function.code.length < Usize.max) (codeRequest : function.code.length + 1 ≤ bound)
    (poolFits : function.v128_pool.length < Usize.max)
    (poolIndex : function.v128_pool.length ≤ U32.max)
    (poolRequest : function.v128_pool.length + 1 ≤ bound) :
    runtime.compiler.initialize.constant ops budget function expr ty dst ⦃ out =>
      out.1 = .Ok () ∧ out.2.1.instructions.val = budget.instructions.val + 1 ∧
      out.2.1.limits = budget.limits ∧ ConstantLowered function out.2.2 expr ty dst ⦄ := by
  cases expr with
  | I32 value =>
    unfold runtime.compiler.initialize.constant
    step as ⟨bits,equal⟩
    subst bits
    step with initializer_emit_available ops bound available budget function.code _ room codeFits codeRequest
      as ⟨status,after,code,accepted,used,limits,appended⟩
    exact ⟨accepted,used,limits,code,function.v128_pool,_,rfl,appended,.i32 value ty⟩
  | I64 value =>
    unfold runtime.compiler.initialize.constant
    step as ⟨bits,equal⟩
    subst bits
    step with initializer_emit_available ops bound available budget function.code _ room codeFits codeRequest
      as ⟨status,after,code,accepted,used,limits,appended⟩
    exact ⟨accepted,used,limits,code,function.v128_pool,_,rfl,appended,.i64 value ty⟩
  | F32 value =>
    unfold runtime.compiler.initialize.constant
    step with initializer_emit_available ops bound available budget function.code _ room codeFits codeRequest
      as ⟨status,after,code,accepted,used,limits,appended⟩
    exact ⟨accepted,used,limits,code,function.v128_pool,_,rfl,appended,.f32 value ty⟩
  | F64 value =>
    unfold runtime.compiler.initialize.constant
    step with initializer_emit_available ops bound available budget function.code _ room codeFits codeRequest
      as ⟨status,after,code,accepted,used,limits,appended⟩
    exact ⟨accepted,used,limits,code,function.v128_pool,_,rfl,appended,.f64 value ty⟩
  | RefNull element =>
    unfold runtime.compiler.initialize.constant
    step with initializer_emit_available ops bound available budget function.code _ room codeFits codeRequest
      as ⟨status,after,code,accepted,used,limits,appended⟩
    exact ⟨accepted,used,limits,code,function.v128_pool,_,rfl,appended,.refNull ty element⟩
  | RefFunc index =>
    unfold runtime.compiler.initialize.constant
    step with initializer_emit_available ops bound available budget function.code _ room codeFits codeRequest
      as ⟨status,after,code,accepted,used,limits,appended⟩
    exact ⟨accepted,used,limits,code,function.v128_pool,_,rfl,appended,.refFunc ty index⟩
  | GlobalGet index =>
    cases ty <;> unfold runtime.compiler.initialize.constant <;> simp only [bind_ok]
    all_goals
      step with initializer_emit_available ops bound available budget function.code _ room codeFits codeRequest
        as ⟨status,after,code,accepted,used,limits,appended⟩
      refine ⟨accepted,used,limits,code,function.v128_pool,_,rfl,appended,?_⟩
      first | exact .globalVector index | exact .global _ index (by intro h; cases h)
  | V128 lo hi =>
    unfold runtime.compiler.initialize.constant runtime.compiler.bounded_index
    step as ⟨maximum,maximumEq⟩
    have bounded : ¬ alloc.vec.Vec.len function.v128_pool > maximum := by
      simp_all [core.num.U32.MAX, U32.rMax]
      scalar_tac
    simp only [if_neg bounded]
    step as ⟨pool,poolEq⟩
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step as ⟨low,lowEq⟩
    subst low
    step as ⟨high,highEq⟩
    subst high
    step as ⟨shifted,shiftEq,shiftBits⟩
    step as ⟨word,wordEq,wordBits⟩
    step with budget_push_available ops bound available budget function.v128_pool word poolFits poolRequest
      as ⟨status,after,values,accepted,same,appended⟩
    subst status after
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with initializer_emit_available ops bound available budget function.code _ room codeFits codeRequest
      as ⟨status,after,code,accepted,used,limits,emitted⟩
    refine ⟨accepted,used,limits,code,values,_,rfl,emitted,.v128 lo hi ty pool ?_⟩
    have packed : word = initializerBits lo hi := by
      apply U128.bv_eq_imp_eq
      exact wordBits.trans (congrArg (fun bits => (UScalar.cast .U128 lo).bv ||| bits) shiftBits)
    have poolValue : pool.val = function.v128_pool.length := by
      simp_all [UScalar.cast_val_eq]
      scalar_tac
    simp [appended,poolValue,packed]

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
  unfold runtime.compiler.initialize.expression
  rw [compiler_width_eq,bind_ok,initializer_synthetic,bind_ok]
  step with initializer_constant_available ops bound available budget (initializerSeed ty) expr ty 0#u32
    (by omega) (by simp [initializerSeed]; scalar_tac)
    (by simpa [initializerSeed] using (show 1 ≤ bound by omega))
    (by simp [initializerSeed]; scalar_tac) (by simp [initializerSeed])
    (by simpa [initializerSeed] using (show 1 ≤ bound by omega))
    as ⟨status,charged,function,accepted,used,limits,lowered⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  obtain ⟨code,pool,instruction,same,emitted,constant⟩ := lowered
  have firstCode : function.code.val = [instruction] := by simp [same,emitted,initializerSeed]
  have firstLength : function.code.length = 1 := by simp [alloc.vec.Vec.length,firstCode]
  step with initializer_emit_available ops bound available charged function.code
    (.Return 0#u32 (initializerWidth ty)) (by rw [limits]; omega)
    (by rw [firstLength]; scalar_tac) (by omega)
    as ⟨status,chargedAgain,finalCode,accepted,usedAgain,limitsAgain,returned⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  have shape : InitializerCode {function with code := finalCode} expr ty := by
    refine ⟨⟨instruction,constant.change_code rfl,?_⟩,?_,?_,?_,?_⟩
    · simp [returned,firstCode]
    all_goals simp [same,initializerSeed]
  have checked := initializer_well_formed {function with code := finalCode} expr ty shape
    (by simp [same,initializerSeed]) (by simp [same,initializerSeed])
    (by simp [same,initializerSeed]) (by simp [same,initializerSeed])
    (by simp [same,initializerSeed]) vector
  step with checked as ⟨valid,validEq⟩
  rw [validEq]
  simp only [↓reduceIte]
  step with budget_push_available ops bound available chargedAgain module.functions
    {function with code := finalCode} functionsFit functionsRequest
    as ⟨status,afterBudget,functions,accepted,sameBudget,appended⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  simp only [WP.spec_ok]
  exact ⟨trivial,by rw [sameBudget]; omega,by rw [sameBudget,limitsAgain,limits],
    _,shape,appended,trivial⟩

end Itasca.Runtime.Compiler

end

end
