import Itasca.Runtime.Compiler.Body.Relations.Entry.EntryBodyExecutable
import Itasca.Runtime.Compiler.Local.Publication.FunctionPublicationHeader
import Itasca.Runtime.Compiler.Module.PreparedExecutableSafety
import Itasca.Runtime.Compiler.Local.Coordinates.SourceCoordinateCallbacks
import Itasca.Runtime.Compiler.Local.Publication.StartMapPublication
import Itasca.Runtime.Compiler.Local.Source.StartJumpTableBounds
import Itasca.Runtime.Compiler.Body.Relations.Checking.BodyCheckedWasm2
import Itasca.Runtime.Compiler.Local.Checking.FunctionStartExitSlots
import Itasca.Runtime.Compiler.Module.PreparedFunctionAvailable
import Itasca.Runtime.Compiler.Module.EntryAvailable

/-!
Successful checked-entry finishing from prepared source and publication bounds. Body instruction checks, header publication and final finish establish the entry availability theorem.
-/

/-! ## Entry Header Publication -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Complete-profile source encoding and the actual unfinished body establish
all header checks, including the final return. No successful finish or completed
function certificate is needed. -/
theorem witness_header_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish profile}
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final profile)
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (functionTable : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType)))
    (endFits : batchStart.val+finish.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    {source : List instr} (encoded : Profile.BodyEncoding profile w.body source) :
    FunctionPublicationHeader final.function ∧ final.frames.val = [] ∧ final.function.code.length ≤ U32.max := by
  have bodyFacts : CompilerEntryFacts w.startedState env w.ctx w.typeIdx w.ft w.body ∧
      StructuredCompiledBody final.function.jump_tables.val
        (ExecutableEmission (CompilerTables.ofFunction final.function) (EnvTranslation.context env w.ctx))
        w.startedState final (env.types.val.map EnvTranslation.funcType)
        (env.func_types.val.map EnvTranslation.funcType) (w.ft.results.val.map Translate.valueType)
        (w.ctx.locals.val.map Translate.valueType) source :=
    witness_body_executable ops law w signatureTable functionTable endFits created encoded
  obtain ⟨facts,target,stable,closed,_,⟨returnStart,returnCount,_,last⟩,length,codeBound⟩ := bodyFacts
  obtain ⟨_,_,_,_,_,paramsEq,localsEq,bodyStartEq,_,_⟩ := stable.fields
  have signature : env.types.val[w.typeIdx.val]? = some w.ft := by
    simp only [List.getElem?_eq_getElem w.type_lt,w.function_type]
  obtain ⟨sig,lookup,_⟩ := signatureTable.lookup_source signature
  have beginFits : batchStart.val+w.bodyStart.val ≤ Usize.max := by
    have span := w.body_bytes.length
    omega
  obtain ⟨_,_,_,_,_,bodyStart,_,_⟩ := compiler_function_start_facts ops law signatures functionSlots budget batchStart
    initial w.startedState w.ctx w.typeIdx sig w.bodyStart finish lookup beginFits endFits created w.function_start
  refine ⟨⟨?_,by change 0 < final.function.code.val.length; omega,?_,?_,?_⟩,closed,codeBound⟩
  · intro synthetic
    have zero := congrArg UScalar.val synthetic.1
    have headerSpan := w.header.span
    have localsSpan := w.locals_bytes.span
    rw [bodyStartEq] at zero
    change w.startedState.function.body_start.val = 0 at zero
    omega
  · rw [localsEq,← facts.capacity]
    exact stable.capacity
  · rw [paramsEq,localsEq,facts.parameterSlots,facts.localLayout.slots]
    simp only [compilerLocals,facts.locals,w.context_locals,List.map_append,slots_append]
    omega
  · refine ⟨returnStart,returnCount,?_⟩
    simpa only [show final.function.code.length-1 = target.val by change final.function.code.val.length-1 = target.val; omega] using last

end Itasca.Runtime.Code

end

/-! ## Prepared Publication Start -/

section

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

end

/-! ## Prepared Body Checked -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Independent validity and source-only allocation/resource room establish
actual body success and every final source/control-target range check. Initial
publication bounds are constructed from actual fresh function-start internally. -/
theorem prepared_body_checked_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial started : runtime.compiler.FunctionCompiler A} {data env index start profile}
    (w : CodeEntry.Prepared data env index start profile)
    (limits : Profile.EnvironmentWithinLimits env)
    (body : Profile.Body profile w.body env w.ctx.locals w.typeIdx)
    (signaturesMatch : SignatureSequence signatures.val env.types.val)
    (slotsMatch : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ty => signatureSlots ty.params.val))
    (batchBound : batchStart.val+data.length ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (begun : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial w.ctx w.typeIdx w.bodyStart w.finish = .ok (.Ok (),started))
    (room : BodyResourceRoom started w.body.length
      (independentBodyDemand w.body env w.ctx w.typeIdx).operands bound) :
    code.validate_body_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) w.body env w.ctx
      w.typeIdx profile started ⦃ result => result.1 = .Ok () ∧
        SourceCompilationBudget started.budget result.2.budget bodyResourceRate w.body.length ∧
        FunctionPublicationRanges result.2.function ∧ CheckedInstructionPrefix result.2.function ⦄ := by
  have signature : env.types.val[w.typeIdx.val]? = some w.ft := by
    simp only [List.getElem?_eq_getElem w.type_lt,w.function_type]
  obtain ⟨coordinates,maps,targets,extent⟩ := prepared_start_publication ops law w signaturesMatch batchBound created begun
  obtain ⟨sig,lookup,_⟩ := signaturesMatch.lookup_source signature
  have endFits : batchStart.val+w.finish.val ≤ Usize.max := by
    have bound := w.body_bytes.bound
    omega
  have beginFits : batchStart.val+w.bodyStart.val ≤ Usize.max := by
    have length := w.body_bytes.length
    omega
  have instructions := compiler_start_instruction_prefix ops law signatures functionSlots budget batchStart initial started w.ctx
    w.typeIdx sig w.bodyStart w.finish lookup beginFits endFits created begun
  have exits := compiler_start_exit_slots ops law signatures functionSlots budget batchStart initial started w.ctx
    w.typeIdx sig w.bodyStart w.finish lookup beginFits endFits created begun
  obtain ⟨facts,matched,point,observed,indirect,simd,pool,fixups⟩ :=
    prepared_executable_safety_wasm2 ops law w room.size signaturesMatch slotsMatch batchBound created begun
  have contextEq : w.ctx = ⟨w.ctx.locals,w.ft.results⟩ := by
    have results : w.ctx.results = w.ft.results := alloc.vec.Vec.ext _ _ w.context_results
    cases h : w.ctx
    simp_all
  have accepted := compiler_body_wasm2_checked_available ops law bound allocation started (EnvTranslation.context env w.ctx)
    (w.ctx.locals.val.map Translate.valueType) w.body env w.ctx.locals w.typeIdx w.ft point facts.localLayout
    facts.locals facts.functionSlots matched rfl facts.signatures ⟨observed,indirect,simd,pool,fixups⟩
    limits body.to_wasm2 (by simpa only [← contextEq] using room) coordinates maps targets
    (by simp only [compilerLocals,facts.locals]) (by rw [facts.capacity]) instructions exits extent
  rw [← contextEq] at accepted
  have checked : code.validate_body_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) w.body
      env w.ctx w.typeIdx .Wasm2 started ⦃ result => result.1 = .Ok () ∧
        SourceCompilationBudget started.budget result.2.budget bodyResourceRate w.body.length ∧
        FunctionPublicationRanges result.2.function ∧ CheckedInstructionPrefix result.2.function ⦄ := by
    apply WP.spec_mono accepted
    intro result held
    obtain ⟨closed,reached,closedState,finished⟩ := held.2
    refine ⟨held.1,?_,reached.1.final_ranges closedState,reached.2.2.2 closedState⟩
    simpa [finished,Slice.len] using reached.1.1.2
  cases profile with
  | Wasm2 => exact checked
  | Wasm1 =>
    obtain ⟨result,run,post⟩ := WP.spec_imp_exists checked
    rw [code.validate_body_with.wasm1_of_body _ _ _ _ _ _ result limits room.size body run, WP.spec_ok]
    exact post

end Itasca.Runtime.Code

end

/-! ## Prepared Function Checked -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Actual function-start and body compilation accept from independent source
validity and numerical demand. Initial prefix certificates and callback success
are constructed internally. The budget effect is relative to the entry budget,
so successive functions can share one module-wide bound. -/
theorem prepared_function_checked_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial : runtime.compiler.FunctionCompiler A} {data env index start profile}
    (w : CodeEntry.Prepared data env index start profile)
    (limits : Profile.EnvironmentWithinLimits env)
    (body : Profile.Body profile w.body env w.ctx.locals w.typeIdx)
    (signaturesMatch : SignatureSequence signatures.val env.types.val)
    (slotsMatch : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ty => signatureSlots ty.params.val))
    (batchBound : batchStart.val+data.length ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (demand : PreparedFunctionDemand budget w.ctx w.body.length
      (independentBodyDemand w.body env w.ctx w.typeIdx).operands bound) :
    ∃ started,
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
        ops initial w.ctx w.typeIdx w.bodyStart w.finish = .ok (.Ok (),started) ∧
      code.validate_body_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) w.body env w.ctx
        w.typeIdx profile started ⦃ result => result.1 = .Ok () ∧
          CompilationBudgetEffect budget result.2.budget (preparedFunctionAllowance w.ctx w.body.length) ∧
          FunctionPublicationRanges result.2.function ∧ CheckedInstructionPrefix result.2.function ⦄ := by
  have signature : env.types.val[w.typeIdx.val]? = some w.ft := by
    simp only [List.getElem?_eq_getElem w.type_lt,w.function_type]
  obtain ⟨sig,lookup,signatureMatch⟩ := signaturesMatch.lookup_source signature
  have fresh := compiler_new ops signatures functionSlots budget batchStart
  rw [created,WP.spec_ok] at fresh
  obtain ⟨localLayout,locals,operands,controls,frames,code,reachable,sigs,slots,batch⟩ := fresh
  have budgetEq : initial.budget = budget := by
    simp only [runtime.compiler.FunctionCompiler.new,Result.ok.injEq] at created
    subst initial
    rfl
  have endFits : batchStart.val+w.finish.val ≤ Usize.max := by
    have last := w.body_bytes.bound
    omega
  have beginFits : batchStart.val+w.bodyStart.val ≤ Usize.max := by
    have length := w.body_bytes.length
    omega
  obtain ⟨⟨status,started⟩,begun,accepted,usedLocals,usedControls,budgetFrame,localsUsed,controlsUsed⟩ := WP.spec_imp_exists
    (compiler_function_start_available ops bound allocation initial w.ctx w.typeIdx sig w.bodyStart w.finish
      (by simpa only [sigs] using lookup) (by simpa only [batch] using beginFits)
      (by simpa only [batch] using endFits) (demand.start ops signatures functionSlots batchStart initial created))
  dsimp only at accepted budgetFrame localsUsed controlsUsed
  subst status
  rw [budgetEq] at budgetFrame localsUsed controlsUsed
  obtain ⟨layout,localsMatch,_,_,_,bodyStart,_⟩ := compiler_function_start_facts ops law signatures functionSlots budget batchStart
    initial started w.ctx w.typeIdx sig w.bodyStart w.finish lookup beginFits endFits created begun
  have room := demand.body started usedLocals usedControls budgetFrame localsUsed controlsUsed layout localsMatch
    (function_body_coordinate_bound w.body_bytes bodyStart endFits)
  refine ⟨started,begun,?_⟩
  apply WP.spec_mono (prepared_body_checked_available ops law bound allocation w limits body signaturesMatch slotsMatch
    batchBound created begun room)
  intro result held
  refine ⟨held.1,?_,held.2.2⟩
  have startEffect : CompilationBudgetEffect budget started.budget
      (fun counter => match counter with | .locals => w.ctx.locals.val.length | .controls => 1 | _ => 0) := by
    rw [budgetFrame]
    refine ⟨rfl,rfl,?_⟩
    intro counter
    cases counter <;> simp [ChargeCounter.used,localsUsed,controlsUsed]
  exact (startEffect.trans held.2.1).weaken (by intro counter; cases counter <;> simp [bodyResourceRate,preparedFunctionAllowance])

end Itasca.Runtime.Code

end

/-! ## Entry Checked Available -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- The actual entry parser, function-start callback, and complete body accept
an independently encoded and typed source function. Every compiler resource
premise is numerical and computed over source preparation; no successful target
trace, target certificate, or universal callback-acceptance premise is required. -/
theorem compiler_entry_checked_available {A : Type} (ops : runtime.platform.Alloc A)
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
        FunctionPublicationRanges result.2.function ∧ CheckedInstructionPrefix result.2.function ∧
        ∃ w : CodeEntry.Prepared data env index start profile, w.finish = finish ∧
          CompilationBudgetEffect budget result.2.budget (preparedFunctionAllowance w.ctx w.body.length) ⦄ := by
  obtain ⟨w,ending,body⟩ := source_entry_prepared data env index start finish profile entry indexBound typed bounds
    environment limits encoded
  obtain ⟨started,begun,bodyAvailable⟩ := prepared_function_checked_available ops law bound allocation w limits body
    signaturesMatch slotsMatch batchBound created (demand w)
  obtain ⟨⟨reply,after⟩,bodyCalled,accepted,effect,ranges,instructions⟩ := WP.spec_imp_exists bodyAvailable
  dsimp only at accepted effect ranges instructions
  subst reply
  apply WP.spec_mono (prepared_entry_replay _ w initial started after begun bodyCalled)
  intro result same
  subst result
  exact ⟨congrArg core.result.Result.Ok ending,ranges,instructions,w,ending,effect⟩

end Itasca.Runtime.Code

end

/-! ## Entry Finish Available -/

section

namespace Itasca.Runtime.Code
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

end Itasca.Runtime.Code

end
