import Itasca.Runtime.Compiler.Local.Definitions
import Itasca.Runtime.Compiler.Local.Control.CodeSegmentsAndPositions
import Itasca.Runtime.Compiler.Local.Relations.Layout.LayoutProofs
import Itasca.Support.Translation

open Itasca.Representation

/-!
# Function root-label relation

The function root-label certificate connects the source result signature to compiler
control state. Body-level constructions use this narrow local fact without introducing a
dependency on body replay.
-/

namespace Itasca.Compiler
open Aeneas.Std

theorem function_root_label_live {results compiled epilogue src count}
    (found : compiled.code.val[epilogue.val]? = some (.Return src count))
    (live : (functionRootLabel results compiled epilogue).branchLive = true) :
    count.val = slots results := by
  simpa only [functionRootLabel, found, decide_eq_true_eq] using live

end Itasca.Compiler
