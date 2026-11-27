import Itasca.Runtime.Interp.Relations.ReadbackAndBindings
import Itasca.Runtime.SourceMachine.EntryAndBranchTables

open WebAssembly

/-!
Repositioning a frame program certificate.

Main declarations: `FrameProgram.reposition`.
-/

namespace Itasca.Interp
open Aeneas Aeneas.Std

theorem FrameProgram.reposition {M : Type} {store : runtime.store.Store M}
    {raw : runtime.interp.Frame} {compiled : runtime.bytecode.CompiledFunction}
    {before after : SourceMachine.AFrame} {functions : List functype}
    (program : FrameProgram store raw compiled (before.locals.map Representation.valueType) before.resultTypes functions)
    (pc : U32) (metadata : FrameMetadata before after) :
    FrameProgram store { raw with pc := pc } compiled (after.locals.map Representation.valueType) after.resultTypes functions := by
  exact ⟨program.lookup, program.checked, program.fetchBound,
    program.localSlots.trans (congrArg Representation.slots metadata.locals).symm,
    by simpa only [metadata.results] using program.epilogue⟩

end Itasca.Interp
