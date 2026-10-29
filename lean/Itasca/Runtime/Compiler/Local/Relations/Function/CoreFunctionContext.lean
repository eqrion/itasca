import Itasca.Runtime.Compiler.Local.Relations.Function.CoreFunction

/-!
At module publication the complete data namespace comes from the parsed tail. Code validation may have run before that tail, without a data-count section; the supported scalar emission has no data-segment instruction.

Main declarations: `moduleFunctionContext`. A direct consumer is `Integration.Instantiation.InstantiateExecutableEventfulOrigin`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- Emission depends exactly on the local/global/memory namespaces used by
this instruction grammar. Other source namespaces may be completed by parsing
the module tail without changing any emitted instruction. -/
theorem ScalarEmission.context {C D before instruction emitted after}
    (locals : D.LOCALS = C.LOCALS) (globals : D.GLOBALS = C.GLOBALS)
    (memories : D.MEMS = C.MEMS)
    (emission : ScalarEmission C before instruction emitted after) :
    ScalarEmission D before instruction emitted after := by
  cases emission with
  | linear h => exact .linear (by simpa only [locals] using h)
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
  | float stack op left right leftSlot rightSlot =>
    exact .float stack op left right (by simpa only [locals] using leftSlot) rightSlot

/-- At module publication the complete data namespace comes from the parsed
tail. Code validation may have run before that tail, without a data-count
section; the supported scalar emission has no data-segment instruction. -/
def moduleFunctionContext (module : runtime.compiler.ExecutableModule)
    (locals results : List valtype) : context :=
  {sourceFunctionContext module.module.env locals results with
    DATAS := List.replicate module.module.tail.data.length datatype.OK}

end Itasca.Runtime.Compiler
