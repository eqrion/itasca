import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Compiler.Local.Relations.Layout.LayoutProofs
import Itasca.Support.TypeTranslation

/-!
The actual epilogue determines whether the implicit root exit carries its declared results. Dead nonvoid bodies may retain a zero-width epilogue.

Main declarations: `functionRootLabel`. A direct consumer is `Compiler.Local.Relations.Function.CoreFunction`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- The actual epilogue determines whether the implicit root exit carries
its declared results. Dead nonvoid bodies may retain a zero-width epilogue. -/
def functionRootLabel (results : List valtype) (compiled : runtime.bytecode.CompiledFunction)
    (epilogue : U32) : LabelTarget :=
  let live := match compiled.code.val[epilogue.val]? with
    | some (.Return _ count) => decide (count.val = slots results)
    | _ => false
  ⟨[], results, results, epilogue, epilogue.val, [], [], live, live⟩

theorem function_root_label_live {results compiled epilogue src count}
    (found : compiled.code.val[epilogue.val]? = some (.Return src count))
    (live : (functionRootLabel results compiled epilogue).branchLive = true) :
    count.val = slots results := by
  simpa only [functionRootLabel, found, decide_eq_true_eq] using live

end Itasca.Runtime.Compiler
