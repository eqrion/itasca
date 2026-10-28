import Itasca.Runtime.Code.Local.Initializer.InitializerDataMappings

namespace Itasca.Runtime.Code
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
    after.module = module.module ∧ after.profile = module.profile ∧
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
    have globalProfile := congrArg runtime.compiler.ExecutableModule.profile globalsChanged
    have globalRows := congrArg runtime.compiler.ExecutableModule.element_initializers globalsChanged
    have globalOffsets := congrArg runtime.compiler.ExecutableModule.element_offsets globalsChanged
    have globalData := congrArg runtime.compiler.ExecutableModule.data_offsets globalsChanged
    dsimp only at globalSource globalProfile globalRows globalOffsets globalData
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
      have elementProfile := congrArg runtime.compiler.ExecutableModule.profile elementsChanged
      have elementGlobals := congrArg runtime.compiler.ExecutableModule.global_initializers elementsChanged
      have elementData := congrArg runtime.compiler.ExecutableModule.data_offsets elementsChanged
      dsimp only at elementSource elementProfile elementGlobals elementData
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
        have dataProfile := congrArg runtime.compiler.ExecutableModule.profile dataChanged
        have dataGlobals := congrArg runtime.compiler.ExecutableModule.global_initializers dataChanged
        have dataRows := congrArg runtime.compiler.ExecutableModule.element_initializers dataChanged
        have dataOffsets := congrArg runtime.compiler.ExecutableModule.element_offsets dataChanged
        dsimp only at dataSource dataProfile dataGlobals dataRows dataOffsets
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
                  dataProfile.trans (elementProfile.trans globalProfile),
                  initializer_prefix_trans allPrefix prefixFinal, ?_⟩
                exact ⟨mapped.globals.extend prefixFinal, mapped.elementValues.extend prefixFinal,
                  mapped.elementOffsets.extend prefixFinal, mapped.dataOffsets.extend prefixFinal⟩

end Itasca.Runtime.Code
