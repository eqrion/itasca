import Itasca.Runtime.Code.Local.Control.Common.StructuredLabels
import Itasca.Runtime.Code.Local.Relations.Common.LayoutProofs
import Itasca.Support.TypeTranslation
namespace Itasca.Runtime.Code
open Aeneas.Std

/-- The actual epilogue determines whether the implicit root exit carries
its declared results. Dead nonvoid bodies may retain a zero-width epilogue. -/
def functionRootLabel (results : List valtype) (compiled : runtime.bytecode.CompiledFunction)
    (epilogue : U32) : LabelTarget :=
  let live := match compiled.code.val[epilogue.val]? with
    | some (.Return _ count) => decide (count.val = slots results)
    | _ => false
  ⟨[], results, results, epilogue, epilogue.val, [], [], live, live⟩

theorem functionRootLabel_live {results compiled epilogue src count}
    (found : compiled.code.val[epilogue.val]? = some (.Return src count))
    (live : (functionRootLabel results compiled epilogue).branchLive = true) :
    count.val = slots results := by
  simpa only [functionRootLabel, found, decide_eq_true_eq] using live

end Itasca.Runtime.Code
