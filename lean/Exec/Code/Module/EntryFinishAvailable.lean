import Exec.Code.Module.EntryCheckedAvailable
import Exec.Code.Module.EntryHeaderPublication

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Independent complete-profile source validity and numerical demand construct
actual entry success, all publication header/range checks, and empty fixup
frames. The final checker and actual compiler finish both succeed. -/
theorem compiler_entry_finish_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (data : Slice U8) (env : module.Env) (index start finish : Usize) (profile : ValidationProfile)
    (entry : ModuleBinary.Code) (indexBound : index.val < env.func_type_indices.val.length)
    (typed : Profile.EntryTyped profile env env.func_type_indices.val[index.val] entry)
    (bounds : CodeEntry.Bounds env) (environment : Profile.Environment profile env)
    (limits : Profile.EnvironmentWithinLimits env)
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
        FunctionPublicationRanges result.2.function ∧ FunctionPublicationHeader result.2.function ∧
        result.2.frames.val = [] ∧ result.2.function.code.length ≤ U32.max ∧
        runtime.compiler.FunctionCompiler.finish ops result.2 (.Ok ()) = .ok (.Ok result.2.function,result.2.budget) ∧
        ∃ w : CodeEntry.Prepared data env index start profile, w.finish = finish ∧
          CompilationBudgetEffect budget result.2.budget (preparedFunctionAllowance w.ctx w.body.length) ⦄ := by
  obtain ⟨⟨reply,after⟩,called,accepted,ranges,instructions,effect⟩ := WP.spec_imp_exists
    (compiler_entry_checked_available ops law bound allocation data env index start finish profile entry indexBound typed
      bounds environment limits encoded signatures functionSlots budget batchStart initial signaturesMatch slotsMatch batchBound created demand)
  dsimp only at accepted ranges instructions effect
  subst reply
  obtain ⟨w⟩ := module.validate_code_entry_with.witness_profile _ data start env index finish initial after bounds profile called
  have signature : env.types.val[w.typeIdx.val]? = some w.ft := by
    simp only [List.getElem?_eq_getElem w.type_lt,w.function_type]
  have valid := code.validate_body_with.profile_sound _ w.body env w.ctx w.typeIdx profile w.ft w.startedState after signature
    (environment.1 w.ft (by rw [← w.function_type]; exact List.getElem_mem _)) w.body_accepted
  obtain ⟨_,source,_,_,bodyEncoding,_⟩ := valid
  have endFits : batchStart.val+finish.val ≤ Usize.max := by
    have last := w.body_bytes.bound
    omega
  have functionTable : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType)) := slotsMatch
  obtain ⟨header,closed,codeBound⟩ := witness_header_publication ops law w signaturesMatch functionTable endFits created bodyEncoding
  rw [called,WP.spec_ok]
  exact ⟨rfl,ranges,header,closed,codeBound,compiler_finish_publication ops after closed header ranges instructions.indexed,effect⟩

end Exec.Code
