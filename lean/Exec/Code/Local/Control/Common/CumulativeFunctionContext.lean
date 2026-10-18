import Exec.Code.Local.Lowering.Float.FloatCoreFunctionContext
import Exec.Code.Local.Control.Common.CumulativeFunction
namespace Exec.Abs.Stateful

theorem Signature.context {C D op input output}
    (functions : D.FUNCS = C.FUNCS) (tables : D.TABLES = C.TABLES)
    (memories : D.MEMS = C.MEMS) (elements : D.ELEMS = C.ELEMS)
    (datas : ∀ index : Nat, C.DATAS[index]? = some datatype.OK → D.DATAS[index]? = some datatype.OK)
    (signature : Signature C op input output) : Signature D op input output := by
  cases signature with
  | refNull type => exact .refNull type
  | refFunc index type found => exact .refFunc index type (by simpa only [functions] using found)
  | refIsNull type => exact .refIsNull type
  | tableGet index type bounds found => exact .tableGet index type bounds (by simpa only [tables] using found)
  | tableSet index type bounds found => exact .tableSet index type bounds (by simpa only [tables] using found)
  | tableSize index type found => exact .tableSize index type (by simpa only [tables] using found)
  | tableGrow index type bounds found => exact .tableGrow index type bounds (by simpa only [tables] using found)
  | tableFill index type bounds found => exact .tableFill index type bounds (by simpa only [tables] using found)
  | tableCopy destination source type destinationBounds sourceBounds destinationFound sourceFound =>
    exact .tableCopy destination source type destinationBounds sourceBounds
      (by simpa only [tables] using destinationFound) (by simpa only [tables] using sourceFound)
  | tableInit table element type bounds tableFound elementFound =>
    exact .tableInit table element type bounds (by simpa only [tables] using tableFound)
      (by simpa only [elements] using elementFound)
  | elemDrop index type found => exact .elemDrop index type (by simpa only [elements] using found)
  | memorySize type found => exact .memorySize type (by simpa only [memories] using found)
  | memoryGrow type found => exact .memoryGrow type (by simpa only [memories] using found)
  | memoryFill type found => exact .memoryFill type (by simpa only [memories] using found)
  | memoryCopy type found => exact .memoryCopy type (by simpa only [memories] using found)
  | memoryInit index type found dataFound =>
    exact .memoryInit index type (by simpa only [memories] using found) (datas index dataFound)
  | dataDrop index found => exact .dataDrop index (datas index found)
end Exec.Abs.Stateful

namespace Exec.Code
open Aeneas.Std

theorem CumulativeEmission.context {pairs C D before instruction emitted after}
    (types : D.TYPES = C.TYPES) (functions : D.FUNCS = C.FUNCS) (locals : D.LOCALS = C.LOCALS)
    (globals : D.GLOBALS = C.GLOBALS) (tables : D.TABLES = C.TABLES)
    (memories : D.MEMS = C.MEMS) (elements : D.ELEMS = C.ELEMS)
    (datas : ∀ index : Nat, C.DATAS[index]? = some datatype.OK → D.DATAS[index]? = some datatype.OK)
    (emission : CumulativeEmission pairs C before instruction emitted after) :
    CumulativeEmission pairs D before instruction emitted after := by
  cases emission with
  | indirect head => exact .indirect (head.context types locals tables)
  | left head => exact .left (head.context locals globals memories)
  | right head =>
    cases head with
    | instruction stack input output op signature first second a b entry firstSlot secondSlot arguments pair =>
      exact .right (.instruction stack input output op (signature.context functions tables memories elements datas)
        first second a b entry (by simpa only [locals] using firstSlot) secondSlot arguments pair)

theorem CumulativeFunctionCode.context {C D params declared results body compiled epilogue}
    (certificate : CumulativeFunctionCode C params declared results body compiled epilogue)
    (types : D.TYPES = C.TYPES) (functions : D.FUNCS = C.FUNCS)
    (locals : D.LOCALS = C.LOCALS) (globals : D.GLOBALS = C.GLOBALS)
    (tables : D.TABLES = C.TABLES) (memories : D.MEMS = C.MEMS) (elements : D.ELEMS = C.ELEMS)
    (datas : ∀ index : Nat, C.DATAS[index]? = some datatype.OK → D.DATAS[index]? = some datatype.OK) :
    CumulativeFunctionCode D params declared results body compiled epilogue := by
  obtain ⟨localTypes, certificate⟩ := certificate
  refine ⟨locals.trans localTypes, ?_⟩
  rw [types, functions]
  exact ⟨certificate.signature, certificate.locals, certificate.parameterSlots, certificate.localSlots,
    certificate.capacity, certificate.fetchBound, certificate.checked,
    certificate.bodyCode.map_emission (fun _ _ _ _ h => h.context types functions locals globals tables memories elements datas),
    certificate.returnCode, certificate.endPosition⟩

/-- The completed module retains each data index available during body validation.
An omitted data-count section contributes no earlier data indices. -/
theorem CumulativeFunctionCode.complete_module {module params declared results body compiled epilogue}
    (certificate : CumulativeFunctionCode
      (sourceFunctionContext module.module.env (params ++ declared) results)
      params declared results body compiled epilogue)
    (count : ∀ declared, module.module.env.data_count = some declared →
      declared.val = module.module.tail.data.val.length) :
    CumulativeFunctionCode (moduleFunctionContext module (params ++ declared) results)
      params declared results body compiled epilogue := by
  apply certificate.context (D := moduleFunctionContext module (params ++ declared) results) rfl rfl rfl rfl rfl rfl rfl
  intro index found
  change (List.replicate module.module.tail.data.val.length datatype.OK)[index]? = some _
  change (Itasca.EnvTranslation.dataTypes module.module.env)[index]? = some _ at found
  cases declaredCount : module.module.env.data_count with
  | none => simp [Itasca.EnvTranslation.dataTypes, declaredCount] at found
  | some n => simpa only [Itasca.EnvTranslation.dataTypes, declaredCount, Option.map_some,
      Option.getD_some, count n declaredCount] using found
end Exec.Code
