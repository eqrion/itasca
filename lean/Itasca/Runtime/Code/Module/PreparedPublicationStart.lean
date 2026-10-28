import Itasca.Runtime.Code.Module.PreparedExecutableSafety
import Itasca.Runtime.Code.Local.Coordinates.SourceCoordinateCallbacks
import Itasca.Runtime.Code.Local.Publication.StartMapPublication
import Itasca.Runtime.Code.Local.Source.StartJumpTableBounds

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Actual fresh entry setup establishes all initial publication invariants
and the declared body extent from independent preparation and signature data. -/
theorem prepared_start_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial started : runtime.compiler.FunctionCompiler A} {data env index start profile}
    (w : CodeEntry.Prepared data env index start profile)
    (signaturesMatch : SignatureSequence signatures.val env.types.val)
    (batchBound : batchStart.val+data.length ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (begun : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial w.ctx w.typeIdx w.bodyStart w.finish = .ok (.Ok (),started)) :
    SourceCoordinates started ∧ ControlMapPublication started ∧ JumpTableBounds started ∧
      started.function.body_end.val = started.function.body_start.val+w.body.length := by
  have signature : env.types.val[w.typeIdx.val]? = some w.ft := by
    simp only [List.getElem?_eq_getElem w.type_lt,w.function_type]
  obtain ⟨sig,lookup,_⟩ := signaturesMatch.lookup_source signature
  have endFits : batchStart.val+w.finish.val ≤ Usize.max := by
    have bound := w.body_bytes.bound
    omega
  have beginFits : batchStart.val+w.bodyStart.val ≤ Usize.max := by
    have length := w.body_bytes.length
    omega
  obtain ⟨_,_,_,_,_,bodyStart,bodyEnd,_⟩ := compiler_function_start_facts ops law signatures functionSlots budget batchStart
    initial started w.ctx w.typeIdx sig w.bodyStart w.finish lookup beginFits endFits created begun
  refine ⟨compiler_start_source_coordinates ops law signatures functionSlots budget batchStart initial started w.ctx
      w.typeIdx w.bodyStart w.finish created begun,
    compiler_start_map_publication ops law signatures functionSlots budget batchStart initial started w.ctx w.typeIdx
      sig w.bodyStart w.finish lookup beginFits endFits created begun,
    compiler_start_jump_table_bounds ops law signatures functionSlots budget batchStart initial started w.ctx w.typeIdx
      sig w.bodyStart w.finish lookup beginFits endFits created begun,?_⟩
  have length := w.body_bytes.length
  change w.finish.val = w.bodyStart.val+w.body.length at length
  omega

end Itasca.Runtime.Code
