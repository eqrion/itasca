import Exec.Interp.Relations.StackRelation
import Exec.Abs.Results

namespace Exec.Interp
open Aeneas Aeneas.Std

theorem FrameProgram.reposition {M : Type} {store : runtime.store.Store M}
    {raw : runtime.interp.Frame} {compiled : runtime.bytecode.CompiledFunction}
    {before after : Abs.AFrame} {functions : List functype}
    (program : FrameProgram store raw compiled (before.locals.map Code.valueType) before.resultTypes functions)
    (pc : U32) (metadata : FrameMetadata before after) :
    FrameProgram store { raw with pc := pc } compiled (after.locals.map Code.valueType) after.resultTypes functions := by
  exact ⟨program.lookup, program.checked, program.fetchBound,
    program.localSlots.trans (congrArg Code.slots metadata.locals).symm,
    by simpa only [metadata.results] using program.epilogue⟩

end Exec.Interp
