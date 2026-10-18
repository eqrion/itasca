import Exec.Code.Local.Relations.Common.CoreFunction
namespace Exec.Code
open Aeneas.Std

/-- Emission depends exactly on the local/global/memory namespaces used by
this instruction grammar. Other source namespaces may be completed by parsing
the module tail without changing any emitted instruction. -/
theorem CoreEmission.context {C D before instruction emitted after}
    (locals : D.LOCALS = C.LOCALS) (globals : D.GLOBALS = C.GLOBALS)
    (memories : D.MEMS = C.MEMS)
    (emission : CoreEmission C before instruction emitted after) :
    CoreEmission D before instruction emitted after := by
  cases emission with
  | pure h => exact .pure (by simpa only [locals] using h)
  | float32 stack dst bits slot => exact .float32 _ dst bits (by simpa only [locals] using slot)
  | float64 stack dst bits slot => exact .float64 _ dst bits (by simpa only [locals] using slot)
  | select stack ty left right condition leftSlot rightSlot conditionSlot =>
    exact .select _ ty left right condition (by simpa only [locals] using leftSlot) rightSlot conditionSlot
  | globalGet stack mutability ty index dst found slot =>
    exact .globalGet _ mutability ty index dst (by simpa only [globals] using found) (by simpa only [locals] using slot)
  | globalSet stack ty index src found slot =>
    exact .globalSet _ ty index src (by simpa only [globals] using found) (by simpa only [locals] using slot)
  | load stack op arg address offset memory found source slot =>
    exact .load _ op arg address offset memory (by simpa only [memories] using found) source (by simpa only [locals] using slot)
  | store stack op arg address value offset memory found source addressSlot valueSlot =>
    exact .store _ op arg address value offset memory (by simpa only [memories] using found) source
      (by simpa only [locals] using addressSlot) valueSlot

theorem CoreFunctionCode.context {C D params declared results body compiled epilogue}
    (certificate : CoreFunctionCode C params declared results body compiled epilogue)
    (types : D.TYPES = C.TYPES) (functions : D.FUNCS = C.FUNCS)
    (locals : D.LOCALS = C.LOCALS) (globals : D.GLOBALS = C.GLOBALS) (memories : D.MEMS = C.MEMS) :
    CoreFunctionCode D params declared results body compiled epilogue := by
  obtain ⟨localTypes, certificate⟩ := certificate
  refine ⟨locals.trans localTypes, ?_⟩
  rw [types, functions]
  exact ⟨certificate.signature, certificate.locals, certificate.parameterSlots, certificate.localSlots,
    certificate.capacity, certificate.fetchBound, certificate.checked,
    certificate.bodyCode.map_emission (fun _ _ _ _ h => h.context locals globals memories),
    certificate.returnCode, certificate.endPosition⟩

/-- At module publication the complete data namespace comes from the parsed
tail. Code validation may have run before that tail, without a data-count
section; the supported scalar emission has no data-segment instruction. -/
def moduleFunctionContext (module : runtime.compiler.ExecutableModule)
    (locals results : List valtype) : context :=
  {sourceFunctionContext module.module.env locals results with
    DATAS := List.replicate module.module.tail.data.length datatype.OK}

theorem CoreFunctionCode.complete_module {module params declared results body compiled epilogue}
    (certificate : CoreFunctionCode
      (sourceFunctionContext module.module.env (params ++ declared) results)
      params declared results body compiled epilogue) :
    CoreFunctionCode (moduleFunctionContext module (params ++ declared) results)
      params declared results body compiled epilogue :=
  certificate.context rfl rfl rfl rfl rfl
end Exec.Code
