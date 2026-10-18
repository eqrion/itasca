import Exec.Code.Body.Relations.Common.ExecutableFunction
import Exec.Code.Local.Control.Common.CumulativeFunctionContext
namespace Exec.Code
open Aeneas.Std

theorem ExecutableEmission.context {tables C D before instruction emitted after}
    (types : D.TYPES=C.TYPES) (functions : D.FUNCS=C.FUNCS) (locals : D.LOCALS=C.LOCALS)
    (globals : D.GLOBALS=C.GLOBALS) (tableTypes : D.TABLES=C.TABLES)
    (memories : D.MEMS=C.MEMS) (elements : D.ELEMS=C.ELEMS)
    (datas : ∀ index : Nat, C.DATAS[index]?=some datatype.OK → D.DATAS[index]?=some datatype.OK)
    (emission : ExecutableEmission tables C before instruction emitted after) :
    ExecutableEmission tables D before instruction emitted after := by
  cases emission with
  | base head =>
    cases head with
    | left head => exact .base (.left (head.context types functions locals globals tableTypes memories elements datas))
    | right head => exact .base (.right (head.context memories.symm locals.symm))
  | typedSelect head =>
    cases head with
    | select front ty left right condition leftPos rightPos conditionPos =>
      exact .typedSelect (.select front ty left right condition (by simpa only [locals] using leftPos) rightPos conditionPos)
  | branchTable => exact .branchTable _ _ _ _ _ _

theorem ExecutableFunctionCode.context {C D params declared results body compiled epilogue}
    (certificate : ExecutableFunctionCode C params declared results body compiled epilogue)
    (types : D.TYPES=C.TYPES) (functions : D.FUNCS=C.FUNCS) (locals : D.LOCALS=C.LOCALS)
    (globals : D.GLOBALS=C.GLOBALS) (tableTypes : D.TABLES=C.TABLES)
    (memories : D.MEMS=C.MEMS) (elements : D.ELEMS=C.ELEMS)
    (datas : ∀ index : Nat, C.DATAS[index]?=some datatype.OK → D.DATAS[index]?=some datatype.OK) :
    ExecutableFunctionCode D params declared results body compiled epilogue := by
  obtain ⟨localTypes,certificate⟩ := certificate
  refine ⟨locals.trans localTypes,?_⟩
  rw [types,functions]
  exact ⟨certificate.signature,certificate.locals,certificate.parameterSlots,certificate.localSlots,
    certificate.capacity,certificate.fetchBound,certificate.checked,
    certificate.bodyCode.map_emission (fun _ _ _ _ h => h.context types functions locals globals tableTypes memories elements datas),
    certificate.returnCode,certificate.endPosition⟩

theorem ExecutableFunctionCode.complete_module {module params declared results body compiled epilogue}
    (certificate : ExecutableFunctionCode
      (sourceFunctionContext module.module.env (params++declared) results)
      params declared results body compiled epilogue)
    (count : ∀ declared, module.module.env.data_count=some declared →
      declared.val=module.module.tail.data.val.length) :
    ExecutableFunctionCode (moduleFunctionContext module (params++declared) results)
      params declared results body compiled epilogue := by
  apply certificate.context (D:=moduleFunctionContext module (params++declared) results) rfl rfl rfl rfl rfl rfl rfl
  intro index found
  change (List.replicate module.module.tail.data.val.length datatype.OK)[index]?=some _
  change (Itasca.EnvTranslation.dataTypes module.module.env)[index]?=some _ at found
  cases declaredCount : module.module.env.data_count with
  | none => simp [Itasca.EnvTranslation.dataTypes,declaredCount] at found
  | some n => simpa only [Itasca.EnvTranslation.dataTypes,declaredCount,Option.map_some,
      Option.getD_some,count n declaredCount] using found
end Exec.Code
