import Exec.Code.Local.Initializer.InitializerComplete
import Exec.Code.Local.Relations.Common.SegmentFinish

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Actual successful initializer lowering supplies both the read-only maps and
the exact retained segment-writing program, from canonical source offset typing.
The bytecode checker's successful Boolean is eliminated from the actual call. -/
theorem initializer_lower_segments {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A)
    (emptyGlobals : module.global_initializers.val = [])
    (emptyElements : module.element_initializers.val = [])
    (emptyElementOffsets : module.element_offsets.val = [])
    (emptyDataOffsets : module.data_offsets.val = [])
    (validElements : ∀ segment ∈ module.module.env.elements.val, ∀ table offset,
      segment.mode = .Active table offset → Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (validDatas : ∀ segment ∈ module.module.tail.data.val, ∀ memory offset,
      segment.mode = .Active memory offset → Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (success : runtime.compiler.initialize.lower ops module budget = .ok (.Ok (), after, budgetAfter)) :
    after.module = module.module ∧ after.profile = module.profile ∧
      after.functions.val.take module.functions.length = module.functions.val ∧ InitializerMappings after ∧
      ∃ function, after.functions.val[after.initialization.val]? = some function ∧ SegmentProgram after function := by
  unfold runtime.compiler.initialize.lower at success
  obtain ⟨⟨globalsModule, b1, result⟩, globalsCall, rest⟩ := initializer_bind_success success
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok unitValue =>
    cases unitValue
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
    | Ok unitValue =>
      cases unitValue
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
      | Ok unitValue =>
        cases unitValue
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
        have sourceAll : dataModule.module = module.module := dataSource.trans (elementSource.trans globalSource)
        have seedEq : function = {initializerSeed .I32 with slot_count := 0#u32} := by
          change Result.ok {initializerSeed .I32 with slot_count := 0#u32} = Result.ok function at seed
          exact (Result.ok_injective seed).symm
        obtain ⟨⟨b4, result, function1⟩, emitElements, rest⟩ := initializer_bind_success rest
        cases result with
        | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
        | Ok unitValue =>
          cases unitValue
          obtain ⟨elementPrograms, elementCertificate⟩ := element_program_loop ops law dataModule function function function1
            b3 b4 0#usize [] (.empty _ _) (by simp) (by simpa only [sourceAll] using validElements) emitElements
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair] at rest
          obtain ⟨⟨b5, result, function2⟩, emitData, rest⟩ := initializer_bind_success rest
          cases result with
          | Err error =>
            simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
          | Ok unitValue =>
            cases unitValue
            obtain ⟨dataPrograms, dataCertificate⟩ := data_program_loop ops law dataModule function1 function1 function2
              b4 b5 0#usize [] (.empty _ _) (by simp) (by simpa only [sourceAll] using validDatas) emitData
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair] at rest
            obtain ⟨⟨result, b6, code⟩, emitReturn, rest⟩ := initializer_bind_success rest
            cases result with
            | Err error =>
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
            | Ok unitValue =>
              cases unitValue
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
                  initializer_prefix_trans allPrefix prefixFinal, ?_, ?_⟩
                · exact ⟨mapped.globals.extend prefixFinal, mapped.elementValues.extend prefixFinal,
                    mapped.elementOffsets.extend prefixFinal, mapped.dataOffsets.extend prefixFinal⟩
                · refine ⟨{function2 with code := code}, ?_, ?_⟩
                  · simp [functionsEq]
                  · have appended := initializer_emit_success ops law b5 b6 function2.code code _ emitReturn
                    have program := segment_program_finish dataModule function function1 function2 code
                      elementPrograms dataPrograms elementCertificate dataCertificate appended
                      (by simp [seedEq, initializerSeed]) (by simp [seedEq, initializerSeed])
                      (by simp [seedEq, initializerSeed]) (by simp [seedEq, initializerSeed])
                      (by simp [seedEq, initializerSeed])
                    exact program.change_module rfl

end Exec.Code
