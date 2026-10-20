import Exec.Code.Module.SourceEntryPrepared
import Exec.Code.Module.PreparedEntryReplay
import Exec.Code.Module.PreparedFunctionAvailable

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Independent numerical resource eligibility over decoded source entry
metadata. This mentions no target callback, emitted function, or target run. -/
def EntryResourceDemand {A : Type} (budget : runtime.compiler.Budget A)
    (data : Slice U8) (env : module.Env) (index start : Usize)
    (profile : ValidationProfile) (bound : Nat) : Prop :=
  ∀ w : CodeEntry.Prepared data env index start profile,
    PreparedFunctionDemand budget w.ctx w.body.length
      (independentBodyDemand profile w.body env w.ctx w.typeIdx).operands bound

/-- The actual entry parser, function-start callback, and complete body accept
an independently encoded and typed source function. Every compiler resource
premise is numerical and computed over source preparation; no successful target
trace, target certificate, or universal callback-acceptance premise is required. -/
theorem compiler_entry_validation_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (data : Slice U8) (env : module.Env) (index start finish : Usize) (profile : ValidationProfile)
    (entry : ModuleBinary.Code) (indexBound : index.val < env.func_type_indices.val.length)
    (typed : Profile.EntryTyped profile env env.func_type_indices.val[index.val] entry)
    (bounds : CodeEntry.Bounds env) (environment : Profile.Environment profile env)
    (limits : Profile.EnvironmentWithinLimits profile env)
    (encoded : ModuleBinary.At (Profile.CodeEncodingWithinLimits profile) data start entry finish)
    (signatures : Slice runtime.compiler.Signature) (functionSlots : Slice U32)
    (budget : runtime.compiler.Budget A) (batchStart : Usize) (initial : runtime.compiler.FunctionCompiler A)
    (signaturesMatch : SignatureSequence signatures.val env.types.val)
    (slotsMatch : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ty => signatureSlots ty.params.val))
    (batchBound : batchStart.val+data.length ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (demand : EntryResourceDemand budget data env index start profile bound) :
    module.validate_code_entry_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data start env index profile initial ⦃ result => result.1 = .Ok finish ∧
        ∃ w : CodeEntry.Prepared data env index start profile, w.finish = finish ∧
          CompilationBudgetEffect budget result.2.budget (preparedFunctionAllowance w.ctx w.body.length) ⦄ := by
  obtain ⟨w,ending,body⟩ := source_entry_prepared data env index start finish profile entry indexBound typed bounds
    environment limits encoded
  obtain ⟨started,begun,bodyAvailable⟩ := prepared_function_available ops law bound allocation w environment limits body
    signaturesMatch slotsMatch batchBound created (demand w)
  obtain ⟨⟨reply,after⟩,bodyCalled,accepted,effect⟩ := WP.spec_imp_exists bodyAvailable
  dsimp only at accepted effect
  subst reply
  apply WP.spec_mono (prepared_entry_replay _ w initial started after begun bodyCalled)
  intro result same
  subst result
  exact ⟨congrArg core.result.Result.Ok ending,w,ending,effect⟩

end Exec.Code
