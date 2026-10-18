import Exec.Code.Local.Relations.Common.CoreFunctionContext
import Exec.Code.Local.Lowering.Float.FloatCoreFunction
namespace Exec.Code
open Aeneas.Std

theorem FloatCoreEmission.context {C D before instruction emitted after}
    (locals : D.LOCALS = C.LOCALS) (globals : D.GLOBALS = C.GLOBALS)
    (memories : D.MEMS = C.MEMS)
    (emission : FloatCoreEmission C before instruction emitted after) :
    FloatCoreEmission D before instruction emitted after := by
  cases emission with
  | core h => exact .core (h.context locals globals memories)
  | scalar stack op left right leftSlot rightSlot =>
    exact .scalar stack op left right (by simpa only [locals] using leftSlot) rightSlot

theorem FloatCoreFunctionCode.context {C D params declared results body compiled epilogue}
    (certificate : FloatCoreFunctionCode C params declared results body compiled epilogue)
    (types : D.TYPES = C.TYPES) (functions : D.FUNCS = C.FUNCS)
    (locals : D.LOCALS = C.LOCALS) (globals : D.GLOBALS = C.GLOBALS) (memories : D.MEMS = C.MEMS) :
    FloatCoreFunctionCode D params declared results body compiled epilogue := by
  obtain ⟨localTypes, certificate⟩ := certificate
  refine ⟨locals.trans localTypes, ?_⟩
  rw [types, functions]
  exact ⟨certificate.signature, certificate.locals, certificate.parameterSlots, certificate.localSlots,
    certificate.capacity, certificate.fetchBound, certificate.checked,
    certificate.bodyCode.map_emission (fun _ _ _ _ h => h.context locals globals memories),
    certificate.returnCode, certificate.endPosition⟩

theorem FloatCoreFunctionCode.complete_module {module params declared results body compiled epilogue}
    (certificate : FloatCoreFunctionCode
      (sourceFunctionContext module.module.env (params ++ declared) results)
      params declared results body compiled epilogue) :
    FloatCoreFunctionCode (moduleFunctionContext module (params ++ declared) results)
      params declared results body compiled epilogue :=
  certificate.context rfl rfl rfl rfl rfl
end Exec.Code
