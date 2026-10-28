import Exec.Code.Body.Relations.Common.EntryCompilerExecutable
import Exec.Code.Module.CompileEntryBounds
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- The scheduler's actual entry construction, issued batch validation, and
finish establish the source-indexed function certificate. All compiler-state
premises are supplied by the checked entry proof. -/
theorem CompileEntryWitness.compile_executable {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.CodeBatch}
    (w : CompileEntryWitness ops before after batch finalBatch)
    (law : Platform.AllocCorrect ops)
    {issued : StreamBatch.Issued} (reachable : StreamBatch.Reachable issued batch)
    (bounded : issued.Bounded) (origin : before.code_start.val ≤ limits.MAX_MODULE_BYTES.val)
    (signatureTable : SignatureSequence before.signatures.val batch.env.types.val)
    (functionTable : before.func_param_slots.val.map (fun word => word.val) =
      batch.env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType)))
    {finish : Usize}
    (entry : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      w.dispatched.code w.dispatched.env w.entry.index w.dispatched.validated_end finish
      w.initial w.final w.dispatched.profile)
    {source : List instr} (encoded : Profile.BodyEncoding w.dispatched.profile entry.body source) :
    DefinedExecutableFunctionCode batch.env entry.typeIdx
      (.FUNC (.mk_uN entry.typeIdx.val)
        ((ModuleLocals.declared entry.groups).map Translate.valueType |>.map local.LOCAL) source) w.final.function := by
  have certificate := witness_compile_executable ops law entry
    (signatures := before.signatures.deref) (functionSlots := before.func_param_slots.deref)
    (by simpa [alloc.vec.Vec.deref, w.metadata.1] using signatureTable)
    (by simpa [alloc.vec.Vec.deref, w.metadata.1] using functionTable)
    (w.end_fits reachable bounded origin entry) w.created encoded
    w.final.function w.final.budget w.finished
  simpa only [w.metadata.1] using certificate
end Itasca.Runtime.Code
