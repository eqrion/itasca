import Itasca.Runtime.Compiler.Local.Initializer
import Itasca.Runtime.Compiler.Body.Relations.Entry.EntryBodyExecutable
import Itasca.Runtime.Compiler.Local.Publication.StartMapPublication
import Itasca.Runtime.Compiler.Module.CompileTotal
import Itasca.Runtime.Compiler.Local.Coordinates.ControlSourceCoordinates
import Itasca.Runtime.Compiler.Local.Source.StartJumpTableBounds
import Itasca.Runtime.Compiler.Body.Relations.Checking.BodyCheckedWasm2
import Itasca.Runtime.Compiler.Local.Checking.FunctionStartExitSlots
import Itasca.Runtime.Compiler.Module.InitializerGlobalsAvailable
import Itasca.Stream.Source
import Itasca.Runtime.Compiler.Module.CompileSubmit
import Itasca.Runtime.Compiler.Module.PreparedFunctionDemand
import Itasca.Binary.Wasm1.EncodingUnique
import Itasca.Module.Code.Framing
import Itasca.Module.Code.LocalsComplete
import Itasca.Stream.Header

/-!
Sections, each formerly its own module: EntryFinishAvailable, CompileEntryAvailable, PreparedBatchSource, BatchLoopAvailable.
-/

/-! ## EntryFinishAvailable -/

section

/-!
Successful checked-entry finishing from prepared source and publication bounds. Body instruction checks, header publication and final finish establish the entry availability theorem.
-/

/-! ## Entry Header Publication -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Source encoding and the actual unfinished body establish
all header checks, including the final return. No successful finish or completed
function certificate is needed. -/
theorem witness_header_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish}
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final)
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (functionTable : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType)))
    (endFits : batchStart.val+finish.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    {source : List instr} (encoded : Profile.BodyEncoding w.body source) :
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

end Itasca.Runtime.Compiler

end

/-! ## Prepared Publication Start -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual fresh entry setup establishes all initial publication invariants
and the declared body extent from independent preparation and signature data. -/
theorem prepared_start_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial started : runtime.compiler.FunctionCompiler A} {data env index start}
    (w : CodeEntry.Prepared data env index start)
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

end Itasca.Runtime.Compiler

end

/-! ## Prepared Body Checked -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Independent validity and source-only allocation/resource room establish
actual body success and every final source/control-target range check. Initial
publication bounds are constructed from actual fresh function-start internally. -/
theorem prepared_body_checked_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial started : runtime.compiler.FunctionCompiler A} {data env index start}
    (w : CodeEntry.Prepared data env index start)
    (limits : Profile.EnvironmentWithinLimits env)
    (body : Wasm2.Validated w.body env w.ctx.locals w.typeIdx)
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
      w.typeIdx started ⦃ result => result.1 = .Ok () ∧
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
    limits body (by simpa only [← contextEq] using room) coordinates maps targets
    (by simp only [compilerLocals,facts.locals]) (by rw [facts.capacity]) instructions exits extent
  rw [← contextEq] at accepted
  have checked : code.validate_body_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) w.body
      env w.ctx w.typeIdx started ⦃ result => result.1 = .Ok () ∧
        SourceCompilationBudget started.budget result.2.budget bodyResourceRate w.body.length ∧
        FunctionPublicationRanges result.2.function ∧ CheckedInstructionPrefix result.2.function ⦄ := by
    apply WP.spec_mono accepted
    intro result held
    obtain ⟨closed,reached,closedState,finished⟩ := held.2
    refine ⟨held.1,?_,reached.1.final_ranges closedState,reached.2.2.2 closedState⟩
    simpa [finished,Slice.len] using reached.1.1.2
  exact checked
end Itasca.Runtime.Compiler

end

/-! ## Prepared Function Checked -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Actual function-start and body compilation accept from independent source
validity and numerical demand. Initial prefix certificates and callback success
are constructed internally. The budget effect is relative to the entry budget,
so successive functions can share one module-wide bound. -/
theorem prepared_function_checked_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial : runtime.compiler.FunctionCompiler A} {data env index start}
    (w : CodeEntry.Prepared data env index start)
    (limits : Profile.EnvironmentWithinLimits env)
    (body : Wasm2.Validated w.body env w.ctx.locals w.typeIdx)
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
        w.typeIdx started ⦃ result => result.1 = .Ok () ∧
          CompilationBudgetEffect budget result.2.budget (preparedFunctionAllowance w.ctx w.body.length) ∧
          FunctionPublicationRanges result.2.function ∧ CheckedInstructionPrefix result.2.function ⦄ := by
  have signature : env.types.val[w.typeIdx.val]? = some w.ft := by
    simp only [List.getElem?_eq_getElem w.type_lt,w.function_type]
  obtain ⟨sig,lookup,signatureMatch⟩ := signaturesMatch.lookup_source signature
  have fresh := compiler_new ops signatures functionSlots budget batchStart
  rw [created,WP.spec_ok] at fresh
  obtain ⟨localLayout,locals,operands,controls,frames,code,reachable,sigs,slots,batch⟩ := fresh
  have budgetEq : initial.budget = budget := by
    simp only [runtime.compiler.FunctionCompiler.new.eq,Result.ok.injEq] at created
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

end Itasca.Runtime.Compiler

end

/-! ## Entry Checked Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- The actual entry parser, function-start callback, and complete body accept
an independently encoded and typed source function. Every compiler resource
premise is numerical and computed over source preparation; no successful target
trace, target certificate, or universal callback-acceptance premise is required. -/
theorem compiler_entry_checked_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (data : Slice U8) (env : metadata.Env) (index start finish : Usize)
    (entry : ModuleBinary.Code) (indexBound : index.val < env.func_type_indices.val.length)
    (typed : Profile.EntryTyped env env.func_type_indices.val[index.val] entry)
    (bounds : CodeEntry.Bounds env)
    (limits : Profile.EnvironmentWithinLimits env)
    (encoded : ModuleBinary.At (Profile.CodeEncodingWithinLimits) data start entry finish)
    (signatures : Slice runtime.compiler.Signature) (functionSlots : Slice U32)
    (budget : runtime.compiler.Budget A) (batchStart : Usize) (initial : runtime.compiler.FunctionCompiler A)
    (signaturesMatch : SignatureSequence signatures.val env.types.val)
    (slotsMatch : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ty => signatureSlots ty.params.val))
    (batchBound : batchStart.val+data.length ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (demand : EntryResourceDemand budget data env index start bound) :
    metadata.validate_code_entry_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data start env index initial ⦃ result => result.1 = .Ok finish ∧
        FunctionPublicationRanges result.2.function ∧ CheckedInstructionPrefix result.2.function ∧
        ∃ w : CodeEntry.Prepared data env index start, w.finish = finish ∧
          CompilationBudgetEffect budget result.2.budget (preparedFunctionAllowance w.ctx w.body.length) ⦄ := by
  obtain ⟨w,ending,body⟩ := source_entry_prepared data env index start finish entry indexBound typed bounds
    limits encoded
  obtain ⟨started,begun,bodyAvailable⟩ := prepared_function_checked_available ops law bound allocation w limits body
    signaturesMatch slotsMatch batchBound created (demand w)
  obtain ⟨⟨reply,after⟩,bodyCalled,accepted,effect,ranges,instructions⟩ := WP.spec_imp_exists bodyAvailable
  dsimp only at accepted effect ranges instructions
  subst reply
  apply WP.spec_mono (prepared_entry_replay _ w initial started after begun bodyCalled)
  intro result same
  subst result
  exact ⟨congrArg core.result.Result.Ok ending,ranges,instructions,w,ending,effect⟩

end Itasca.Runtime.Compiler

end

/-! ## Entry Finish Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Independent source validity and numerical demand construct
actual entry success, all publication header/range checks, and empty fixup
frames. The final checker and actual compiler finish both succeed. -/
theorem compiler_entry_finish_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (data : Slice U8) (env : metadata.Env) (index start finish : Usize)
    (entry : ModuleBinary.Code) (indexBound : index.val < env.func_type_indices.val.length)
    (typed : Profile.EntryTyped env env.func_type_indices.val[index.val] entry)
    (bounds : CodeEntry.Bounds env)
    (limits : Profile.EnvironmentWithinLimits env)
    (encoded : ModuleBinary.At (Profile.CodeEncodingWithinLimits) data start entry finish)
    (signatures : Slice runtime.compiler.Signature) (functionSlots : Slice U32)
    (budget : runtime.compiler.Budget A) (batchStart : Usize) (initial : runtime.compiler.FunctionCompiler A)
    (signaturesMatch : SignatureSequence signatures.val env.types.val)
    (slotsMatch : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ty => signatureSlots ty.params.val))
    (batchBound : batchStart.val+data.length ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (demand : EntryResourceDemand budget data env index start bound) :
    metadata.validate_code_entry_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data start env index initial ⦃ result => result.1 = .Ok finish ∧
        FunctionPublicationRanges result.2.function ∧ FunctionPublicationHeader result.2.function ∧
        result.2.frames.val = [] ∧ result.2.function.code.length ≤ U32.max ∧
        runtime.compiler.FunctionCompiler.finish ops result.2 (.Ok ()) = .ok (.Ok result.2.function,result.2.budget) ∧
        ∃ w : CodeEntry.Prepared data env index start, w.finish = finish ∧
          CompilationBudgetEffect budget result.2.budget (preparedFunctionAllowance w.ctx w.body.length) ⦄ := by
  obtain ⟨⟨reply,after⟩,called,accepted,ranges,instructions,effect⟩ := WP.spec_imp_exists
    (compiler_entry_checked_available ops law bound allocation data env index start finish entry indexBound typed
      bounds limits encoded signatures functionSlots budget batchStart initial signaturesMatch slotsMatch batchBound created demand)
  dsimp only at accepted ranges instructions effect
  subst reply
  obtain ⟨w⟩ := metadata.validate_code_entry_with.witness_profile _ data start env index finish initial after bounds called
  have signature : env.types.val[w.typeIdx.val]? = some w.ft := by
    simp only [List.getElem?_eq_getElem w.type_lt,w.function_type]
  have valid := code.validate_body_with.profile_sound _ w.body env w.ctx w.typeIdx w.startedState after
    w.body_accepted
  obtain ⟨_,source,_,bodyEncoding,_,_⟩ := valid
  have endFits : batchStart.val+finish.val ≤ Usize.max := by
    have last := w.body_bytes.bound
    omega
  have functionTable : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType)) := slotsMatch
  obtain ⟨header,closed,codeBound⟩ := witness_header_publication ops law w signaturesMatch functionTable endFits created bodyEncoding
  rw [called,WP.spec_ok]
  exact ⟨rfl,ranges,header,closed,codeBound,compiler_finish_publication ops after closed header ranges instructions.indexed,effect⟩

end Itasca.Runtime.Compiler

end

end

/-! ## CompileEntryAvailable -/

section

/-!
Successful scheduled entry compilation from batch entry availability.
-/

/-! ## Batch Entry Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- A valid worker entry compiles and finishes successfully, with actual worker
bookkeeping and source-paid budget charges. Only source and numerical demand
premises are supplied; no accepting visitor contract is required. -/
theorem compiler_batch_entry_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (batch : stream.CodeBatch) (index finish : Usize) (entry : ModuleBinary.Code)
    (noError : batch.error = none) (remaining : batch.num_validated.val < batch.num_funcs.val)
    (position : index.val = batch.first_func.val+batch.num_validated.val)
    (indexBound : index.val < batch.env.func_type_indices.val.length)
    (typed : Profile.EntryTyped batch.env batch.env.func_type_indices.val[index.val] entry)
    (bounds : CodeEntry.Bounds batch.env)
    (limits : Profile.EnvironmentWithinLimits batch.env)
    (encoded : ModuleBinary.At (Profile.CodeEncodingWithinLimits) batch.code batch.validated_end entry finish)
    (signatures : Slice runtime.compiler.Signature) (functionSlots : Slice U32)
    (budget : runtime.compiler.Budget A) (batchStart : Usize) (initial : runtime.compiler.FunctionCompiler A)
    (signaturesMatch : SignatureSequence signatures.val batch.env.types.val)
    (slotsMatch : functionSlots.val.map (fun word => word.val) =
      batch.env.func_types.val.map (fun ty => signatureSlots ty.params.val))
    (batchBound : batchStart.val+batch.code.length ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (demand : EntryResourceDemand budget batch.code batch.env index batch.validated_end bound) :
    ∃ count after, count.val = batch.num_validated.val+1 ∧
      stream.CodeBatch.validate_func (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        batch index initial = .ok (.Ok (),{batch with num_validated := count,validated_end := finish},after) ∧
      runtime.compiler.FunctionCompiler.finish ops after (.Ok ()) = .ok (.Ok after.function,after.budget) ∧
      ∃ w : CodeEntry.Prepared batch.code batch.env index batch.validated_end,
        w.finish = finish ∧ CompilationBudgetEffect budget after.budget (preparedFunctionAllowance w.ctx w.body.length) := by
  obtain ⟨⟨reply,after⟩,called,accepted,ranges,header,closed,codeBound,finished,effect⟩ := WP.spec_imp_exists
    (compiler_entry_finish_available ops law bound allocation batch.code batch.env index batch.validated_end finish
      entry indexBound typed bounds limits encoded signatures functionSlots budget batchStart initial
      signaturesMatch slotsMatch batchBound created demand)
  dsimp only at accepted ranges header closed codeBound finished effect
  subst reply
  obtain ⟨expected,added,expectedValue⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x := batch.first_func) (y := batch.num_validated) (by scalar_tac))
  have same : expected = index := UScalar.eq_of_val_eq (by omega)
  subst expected
  have more : ¬ batch.num_validated ≥ batch.num_funcs := by scalar_tac
  have next : stream.CodeBatch.validate_next (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      batch index initial = .ok (.Ok finish,after) := by
    simp [stream.CodeBatch.validate_next,more,added,called]
  obtain ⟨count,increment,countValue⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x := batch.num_validated) (y := 1#usize) (by scalar_tac))
  refine ⟨count,after,by simpa using countValue,?_,finished,effect⟩
  simp [Itasca.stream.CodeBatch.validate_func,noError,core.option.Option.is_none,next,increment]

end Itasca.Runtime.Compiler

end

/-! ## Compile Entry Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The scheduler compiles and publishes an independently valid dispatched
entry into its vacant source-indexed slot. All compiler calls, including finish,
are constructed from source-only demand and bounded allocation availability. -/
theorem compiler_scheduled_entry_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (before : runtime.compiler.CompileScheduler A) (batch dispatched : stream.CodeBatch)
    (frame : stream.CodeEntry) (finish : Usize) (entry : ModuleBinary.Code)
    (dispatch : stream.CodeBatch.next_entry batch = .ok (.Ok frame,dispatched))
    (noError : dispatched.error = none) (remaining : dispatched.num_validated.val < dispatched.num_funcs.val)
    (position : frame.index.val = dispatched.first_func.val+dispatched.num_validated.val)
    (indexBound : frame.index.val < dispatched.env.func_type_indices.val.length)
    (typed : Profile.EntryTyped dispatched.env dispatched.env.func_type_indices.val[frame.index.val] entry)
    (bounds : CodeEntry.Bounds dispatched.env)
    (limits : Profile.EnvironmentWithinLimits dispatched.env)
    (encoded : ModuleBinary.At (Profile.CodeEncodingWithinLimits)
      dispatched.code dispatched.validated_end entry finish)
    (signaturesMatch : SignatureSequence before.signatures.val dispatched.env.types.val)
    (slotsMatch : before.func_param_slots.val.map (fun word => word.val) =
      dispatched.env.func_types.val.map (fun ty => signatureSlots ty.params.val))
    (batchBound : before.code_start.val+dispatched.code_offset.val+dispatched.code.length ≤ Usize.max)
    (slotBound : frame.index.val < before.functions.val.length)
    (vacant : before.functions.val[frame.index.val]? = some none)
    (demand : EntryResourceDemand (A := A) {before.budget with marker := ()} dispatched.code dispatched.env
      frame.index dispatched.validated_end bound) :
    ∃ (count : Usize) (final : runtime.compiler.FunctionCompiler A),
      count.val = dispatched.num_validated.val+1 ∧
      runtime.compiler.CompileScheduler.compile_entry ops before batch = .ok (.Ok (),
        {before with functions := before.functions.set frame.index (some final.function),budget := final.budget},
        {dispatched with num_validated := count,validated_end := finish}) ∧
      ∃ w : CodeEntry.Prepared dispatched.code dispatched.env frame.index dispatched.validated_end,
        w.finish = finish ∧ CompilationBudgetEffect before.budget final.budget (preparedFunctionAllowance w.ctx w.body.length) := by
  obtain ⟨batchStart,added,startValue⟩ := WP.spec_imp_exists
    (Usize.add_spec (x := before.code_start) (y := dispatched.code_offset) (by omega))
  obtain ⟨initial,created,_⟩ := WP.spec_imp_exists (compiler_new ops
    (alloc.vec.Vec.deref before.signatures) (alloc.vec.Vec.deref before.func_param_slots)
    {before.budget with marker := ()} batchStart)
  obtain ⟨count,final,countValue,validated,finished,w,ending,effect⟩ := compiler_batch_entry_available ops law bound allocation
    dispatched frame.index finish entry noError remaining position indexBound typed bounds limits encoded
    (alloc.vec.Vec.deref before.signatures) (alloc.vec.Vec.deref before.func_param_slots)
    {before.budget with marker := ()} batchStart initial (by simpa [alloc.vec.Vec.deref] using signaturesMatch)
    (by simpa [alloc.vec.Vec.deref] using slotsMatch) (by omega) created demand
  let finalBatch := {dispatched with num_validated := count,validated_end := finish}
  let after := {before with functions := before.functions.set frame.index (some final.function),budget := final.budget}
  refine ⟨count,final,countValue,?_,w,ending,?_⟩
  · exact CompileEntryWitness.called ⟨frame, dispatched, batchStart, initial, final,
      dispatch, added, created, validated, finished, slotBound, vacant, rfl⟩
  · simpa only [CompilationBudgetEffect] using effect

end Itasca.Runtime.Compiler

end

end

/-! ## PreparedBatchSource -/

section

/-!
Prepared compiler-batch source certificates. Entry uniqueness and conservative function-demand envelopes establish the batch source/resource relation.
-/

/-! ## Function Demand Envelope -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Conservative per-function charges from independent source maxima. -/
def functionDemandRate (bodyBytes localCount : Nat) : ChargeCounter → Nat
  | .instructions => 3*bodyBytes
  | .branches => bodyBytes
  | .controls => 1+bodyBytes
  | .locals => localCount

/-- Module-wide numerical headroom for uniformly bounded source functions.
The maxima concern source bytes, expanded locals, and validated operand depth;
no emitted target object or compilation result occurs here. -/
structure FunctionDemandEnvelope {A : Type} (budget : runtime.compiler.Budget A)
    (functions bodyBytes localCount peak bound : Nat) : Prop where
  size : bodyBytes ≤ limits.MAX_FUNCTION_BYTES.val
  counters : ∀ counter, (counter.used budget).val+functions*functionDemandRate bodyBytes localCount counter ≤
    (counter.limit budget).val
  temporary : 3*bodyBytes+3 ≤ bound
  locals : localCount ≤ bound
  operands : peak ≤ bound
  slots : 2*localCount+2*peak ≤ U32.max

/-- Each source function fits the remaining module-wide budget after the
preceding functions' conservative charges. -/
theorem FunctionDemandEnvelope.prepared {A : Type}
    {base budget : runtime.compiler.Budget A} {functions bodyBytes localCount peak bound processed}
    (envelope : FunctionDemandEnvelope base functions bodyBytes localCount peak bound)
    (paid : CompilationBudgetEffect base budget (fun counter => processed*functionDemandRate bodyBytes localCount counter))
    (remaining : processed < functions) (ctx : code.Context) (length operands : Nat)
    (bytes : length ≤ bodyBytes) (locals : ctx.locals.val.length ≤ localCount) (stack : operands ≤ peak) :
    PreparedFunctionDemand budget ctx length operands bound := by
  have counterRoom (counter : ChargeCounter) :
      (counter.used budget).val+functionDemandRate bodyBytes localCount counter ≤ (counter.limit budget).val := by
    have before := envelope.counters counter
    have used := (paid.counts counter).2
    have mult : (processed+1)*functionDemandRate bodyBytes localCount counter ≤ functions*functionDemandRate bodyBytes localCount counter :=
      Nat.mul_le_mul_right _ (by omega)
    have unchanged : counter.limit budget = counter.limit base := by
      cases counter <;> simp only [ChargeCounter.limit,paid.limits]
    rw [unchanged]
    simp only [Nat.add_mul,Nat.one_mul] at mult
    omega
  refine ⟨bytes.trans envelope.size,?_,?_,?_,?_,?_,locals.trans envelope.locals,stack.trans envelope.operands,?_⟩
  · have room := counterRoom .instructions
    simp only [ChargeCounter.used,ChargeCounter.limit,functionDemandRate] at room
    omega
  · have room := counterRoom .branches
    simp only [ChargeCounter.used,ChargeCounter.limit,functionDemandRate] at room
    omega
  · have room := counterRoom .controls
    simp only [ChargeCounter.used,ChargeCounter.limit,functionDemandRate] at room
    omega
  · have room := counterRoom .locals
    simp only [ChargeCounter.used,ChargeCounter.limit,functionDemandRate] at room
    omega
  · have room := envelope.temporary
    omega
  · have room := envelope.slots
    omega

/-- The exact prepared-function allowance fits the independent uniform rate. -/
theorem prepared_allowance_le_rate (ctx : code.Context) (length bodyBytes localCount : Nat)
    (bytes : length ≤ bodyBytes) (locals : ctx.locals.val.length ≤ localCount) :
    ∀ counter, preparedFunctionAllowance ctx length counter ≤ functionDemandRate bodyBytes localCount counter := by
  intro counter
  cases counter <;> simp only [preparedFunctionAllowance,functionDemandRate] <;> omega

end Itasca.Runtime.Compiler

end

/-! ## Prepared Entry Unique -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Pure entry decoding determines all inputs to source body demand. Grouping
of declared locals does not affect the expanded context consumed by compilation. -/
theorem prepared_entry_unique {data env index start}
    (first second : CodeEntry.Prepared data env index start) :
    first.typeIdx = second.typeIdx ∧ first.ctx = second.ctx ∧ first.body = second.body ∧
      first.bodyStart = second.bodyStart ∧ first.finish = second.finish := by
  have typeEq : first.typeIdx = second.typeIdx := first.index_type.symm.trans second.index_type
  have functionEq : first.ft = second.ft := by
    have left := first.function_type
    have right := second.function_type
    simpa only [typeEq,right] using left.symm
  obtain ⟨sizeEq,contentEq⟩ := first.header.unique second.header
  have finishEq : first.finish = second.finish := UScalar.eq_of_val_eq (by
    have left := first.extent
    have right := second.extent
    rw [sizeEq,contentEq] at left
    omega)
  obtain ⟨declaredLeft,decodedLeft,valuesLeft⟩ := metadata.decode_locals.complete data first.content first.groups
    first.bodyStart first.locals_bytes first.locals_bound
  obtain ⟨declaredRight,decodedRight,valuesRight⟩ := metadata.decode_locals.complete data second.content second.groups
    second.bodyStart second.locals_bytes second.locals_bound
  rw [contentEq,decodedRight] at decodedLeft
  have localsEq : declaredLeft = declaredRight ∧ first.bodyStart = second.bodyStart := by
    simpa only [Result.ok.injEq,core.result.Result.Ok.injEq,Prod.mk.injEq] using decodedLeft.symm
  have groupsEq : ModuleLocals.declared first.groups = ModuleLocals.declared second.groups := by
    rw [localsEq.1] at valuesLeft
    exact valuesLeft.symm.trans valuesRight
  have ctxLocals : first.ctx.locals = second.ctx.locals := alloc.vec.Vec.ext _ _ (by
    rw [first.context_locals,second.context_locals,functionEq,groupsEq])
  have ctxResults : first.ctx.results = second.ctx.results := alloc.vec.Vec.ext _ _ (by
    rw [first.context_results,second.context_results,functionEq])
  have ctxEq : first.ctx = second.ctx := by
    cases left : first.ctx
    cases right : second.ctx
    simp_all
  have bodyEq : first.body = second.body := Slice.ext _ _ (by
    have left := first.body_bytes.suffix
    rw [localsEq.2,finishEq] at left
    exact List.append_cancel_right (left.symm.trans second.body_bytes.suffix))
  exact ⟨typeEq,ctxEq,bodyEq,localsEq.2,finishEq⟩

end Itasca.Runtime.Compiler

end

/-! ## Entry Demand -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- One independently prepared source entry suffices to establish all entry
resource eligibility. Pure decoding fixes every operand of the numeric demand,
so no compiler run or universal family of callback proofs is supplied. -/
theorem EntryResourceDemand.of_prepared {A : Type} {budget : runtime.compiler.Budget A}
    {data env index start bound}
    (prepared : CodeEntry.Prepared data env index start)
    (demand : PreparedFunctionDemand budget prepared.ctx prepared.body.length
      (independentBodyDemand prepared.body env prepared.ctx prepared.typeIdx).operands bound) :
    EntryResourceDemand budget data env index start bound := by
  intro other
  obtain ⟨typeEq,ctxEq,bodyEq,_,_⟩ := prepared_entry_unique prepared other
  simpa only [← typeEq,← ctxEq,← bodyEq] using demand

end Itasca.Runtime.Compiler

end

/-! ## Prepared Batch Source -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Independently prepared, encoded, and typed source entries in byte/index
order, with conservative source maxima. Preparation contains only source
metadata and decoding facts, never a compiler callback or target certificate. -/
inductive PreparedBatchSource (data : Slice U8) (env : metadata.Env)
    (bodyBytes localCount peak : Nat) : Nat → Usize → List ModuleBinary.Code → Usize → Prop where
  | nil (index start) : PreparedBatchSource data env bodyBytes localCount peak index start [] start
  | cons {index start next finish entry entries}
      (ordinal : Usize) (ordinalValue : ordinal.val = index)
      (indexBound : ordinal.val < env.func_type_indices.val.length)
      (typed : Profile.EntryTyped env env.func_type_indices.val[ordinal.val] entry)
      (encoded : ModuleBinary.At (Profile.CodeEncodingWithinLimits) data start entry next)
      (prepared : CodeEntry.Prepared data env ordinal start) (ending : prepared.finish = next)
      (bytes : prepared.body.length ≤ bodyBytes) (locals : prepared.ctx.locals.val.length ≤ localCount)
      (operands : (independentBodyDemand prepared.body env prepared.ctx prepared.typeIdx).operands ≤ peak)
      (rest : PreparedBatchSource data env bodyBytes localCount peak (index+1) next entries finish) :
      PreparedBatchSource data env bodyBytes localCount peak index start (entry::entries) finish

end Itasca.Runtime.Compiler

end

end

/-! ## BatchLoopAvailable -/

section

/-!
Successful compiler batch-loop execution, including entry dispatch and the published function-slot prefix.
-/

/-! ## Dispatch Entry Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096
private theorem count_room (count limit : Usize) (less : count.val < limit.val) :
    count.val+1 ≤ Usize.max := by scalar_tac


private theorem count_not_ge (count limit : Usize) (less : count.val < limit.val) :
    ¬ count ≥ limit := by scalar_tac

/-- Source framing and intrinsic coordinate bounds construct the actual next
scheduler dispatch, retaining the independent validation cursor unchanged. -/
theorem compiler_next_entry_available (batch : stream.CodeBatch) (content finish : Usize)
    (remaining : batch.num_dispatched.val < batch.num_funcs.val)
    (indices : batch.first_func.val+batch.num_funcs.val ≤ Usize.max)
    (extent : ModuleCode.Extent batch.code batch.dispatch_end content finish)
    (coordinates : batch.code_offset.val+finish.val ≤ limits.MAX_MODULE_BYTES.val) :
    ∃ index count frame, index.val = batch.first_func.val+batch.num_dispatched.val ∧
      count.val = batch.num_dispatched.val+1 ∧ frame.index = index ∧
      stream.CodeBatch.next_entry batch = .ok (.Ok frame,{batch with num_dispatched := count,dispatch_end := finish}) := by
  obtain ⟨index,added,indexValue⟩ := WP.spec_imp_exists
    (Usize.add_spec (x := batch.first_func) (y := batch.num_dispatched) (by scalar_tac))
  obtain ⟨frame,framed,content',finish',actual,same,_,_,endValue,_⟩ :=
    stream.frame_entry.complete batch.code batch.dispatch_end index batch.code_offset content finish extent coordinates
  have finishEq : finish' = finish := by
    obtain ⟨size,read,span,bound⟩ := actual
    obtain ⟨size',read',span',bound'⟩ := extent
    obtain ⟨sizes,contents⟩ := ModuleCode.decoded_unique read read'
    apply UScalar.eq_of_val_eq
    rw [span,span',←sizes,←contents]
  subst finish'
  obtain ⟨endOffset,subtracted,offsetValue⟩ := WP.spec_imp_exists
    (Usize.sub_spec (x := frame.end) (y := batch.code_offset) (by scalar_tac))
  have offsetEq : endOffset = finish := UScalar.eq_of_val_eq (by omega)
  subst endOffset
  obtain ⟨count,increment,countValue⟩ := WP.spec_imp_exists
    (Usize.add_spec (x := batch.num_dispatched) (y := 1#usize) (by simpa using count_room _ _ remaining))
  refine ⟨index,count,frame,indexValue,by simpa using countValue,same,?_⟩
  have more : ¬ batch.num_dispatched ≥ batch.num_funcs := count_not_ge _ _ remaining
  simp [Itasca.stream.CodeBatch.next_entry,more,added,framed,
    core.result.Result.Insts.CoreOpsTry.branch,subtracted,increment]

end Itasca.Runtime.Compiler

end

/-! ## Function Slot Prefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Published source slots form a dense prefix; all later slots remain vacant. -/
structure FunctionSlotPrefix (count cursor : Nat)
    (functions : List (Option runtime.bytecode.CompiledFunction)) : Prop where
  length : functions.length = count
  inside : cursor ≤ count
  filled : ∀ index, index < cursor → ∃ function, functions[index]? = some (some function)
  vacant : ∀ index, cursor ≤ index → index < count → functions[index]? = some none

/-- Publishing exactly the next source slot extends the prefix once. -/
theorem FunctionSlotPrefix.publish {count cursor functions}
    (held : FunctionSlotPrefix count cursor functions) (remaining : cursor < count)
    (function : runtime.bytecode.CompiledFunction) :
    FunctionSlotPrefix count (cursor+1) (functions.set cursor (some function)) := by
  refine ⟨by simpa only [List.length_set] using held.length,by omega,?_,?_⟩
  · intro index bound
    by_cases same : index = cursor
    · subst index
      exact ⟨function,by simp [List.getElem?_set_self,held.length,remaining]⟩
    · obtain ⟨previous,found⟩ := held.filled index (by omega)
      exact ⟨previous,by rw [List.getElem?_set_ne (by omega)]; exact found⟩
  · intro index lower upper
    rw [List.getElem?_set_ne (by omega)]
    exact held.vacant index (by omega) upper

end Itasca.Runtime.Compiler

end

/-! ## Batch Loop Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096

private theorem increment_room (index count : Usize) (remaining : index.val < count.val) :
    index.val+1 ≤ Usize.max := by scalar_tac

/-- The actual eager batch loop accepts an independent prepared source sequence.
The uniform numerical envelope pays cumulative charges across all functions;
publication fills each source slot once, including unreachable body code. -/
theorem compiler_batch_loop_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (base : runtime.compiler.Budget A) (bodyBytes localCount peak : Nat)
    (before : runtime.compiler.CompileScheduler A) (batch : stream.CodeBatch)
    (loopIndex finish : Usize) (entries : List ModuleBinary.Code)
    (source : PreparedBatchSource batch.code batch.env bodyBytes localCount peak
      (batch.first_func.val+batch.num_validated.val) batch.validated_end entries finish)
    (envelope : FunctionDemandEnvelope base batch.env.func_type_indices.val.length bodyBytes localCount peak bound)
    (paid : CompilationBudgetEffect base before.budget
      (fun counter => (batch.first_func.val+batch.num_validated.val)*functionDemandRate bodyBytes localCount counter))
    (slots : FunctionSlotPrefix batch.env.func_type_indices.val.length
      (batch.first_func.val+batch.num_validated.val) before.functions.val)
    (synchronized : batch.num_dispatched = batch.num_validated) (cursor : batch.dispatch_end = batch.validated_end)
    (noError : batch.error = none) (iteration : loopIndex = batch.num_validated)
    (count : batch.num_validated.val+entries.length = batch.num_funcs.val)
    (range : batch.first_func.val+batch.num_funcs.val ≤ batch.env.func_type_indices.val.length)
    (bounds : CodeEntry.Bounds batch.env)
    (limits : Profile.EnvironmentWithinLimits batch.env)
    (signatures : SignatureSequence before.signatures.val batch.env.types.val)
    (functionSlots : before.func_param_slots.val.map (fun word => word.val) =
      batch.env.func_types.val.map (fun ty => signatureSlots ty.params.val))
    (coordinates : batch.code_offset.val+batch.code.length ≤ Itasca.limits.MAX_MODULE_BYTES.val)
    (arithmetic : before.code_start.val+batch.code_offset.val+batch.code.length ≤ Usize.max) :
    ∃ after worker,
      runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop ops before batch loopIndex (.Ok ()) =
        .ok (submitPack after worker (.Ok ())) ∧
      worker.num_validated = batch.num_funcs ∧ worker.validated_end = finish ∧ worker.error = none ∧
      after.completed = before.completed ∧
      FunctionSlotPrefix batch.env.func_type_indices.val.length (batch.first_func.val+batch.num_funcs.val) after.functions.val ∧
      CompilationBudgetEffect base after.budget
        (fun counter => (batch.first_func.val+batch.num_funcs.val)*functionDemandRate bodyBytes localCount counter) := by
  induction entries generalizing before batch loopIndex with
  | nil =>
    cases source
    have ended : batch.num_validated = batch.num_funcs := UScalar.eq_of_val_eq (by simpa using count)
    subst loopIndex
    refine ⟨before,batch,?_,ended,rfl,noError,rfl,?_,?_⟩
    · exact runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop.done
        ops before batch batch.num_validated (by simp [ended])
    · simpa only [ended] using slots
    · simpa only [ended] using paid
  | cons entry entries ih =>
    cases source with
    | cons ordinal ordinalValue indexBound typed encoded prepared ending bytes locals operands rest =>
      have more : batch.num_validated.val < batch.num_funcs.val := by simp only [List.length_cons] at count; omega
      obtain ⟨raw,encoding,span⟩ := encoded
      have encoded : ModuleBinary.At (Profile.CodeEncodingWithinLimits) batch.code batch.validated_end entry prepared.finish :=
        ending ▸ ⟨raw,encoding,span⟩
      have rawEncoded : ModuleBinary.At (Profile.CodeEncoding) batch.code batch.validated_end entry prepared.finish :=
        ⟨raw,encoding.encoding,by simpa only [ending] using span⟩
      obtain ⟨content,extent⟩ := rawEncoded.code_extent
      obtain ⟨index,dispatchedCount,frame,indexValue,dispatchedValue,frameIndex,dispatch⟩ :=
        compiler_next_entry_available batch content prepared.finish (by simpa only [synchronized] using more)
          (range.trans batch.env.func_type_indices.property) (by simpa only [cursor] using extent)
          (by have endBound := rawEncoded.span.2; omega)
      rw [synchronized] at indexValue dispatchedValue
      have selected : frame.index = ordinal := UScalar.eq_of_val_eq (by rw [frameIndex]; omega)
      cases selected
      let dispatched := {batch with num_dispatched := dispatchedCount,dispatch_end := prepared.finish}
      have localDemand : EntryResourceDemand (A := A) {before.budget with marker := ()} batch.code batch.env
          frame.index batch.validated_end bound := by
        apply EntryResourceDemand.of_prepared prepared
        exact envelope.prepared (by simpa only [CompilationBudgetEffect] using paid) (by omega)
          prepared.ctx prepared.body.length _ bytes locals operands
      obtain ⟨validatedCount,final,validatedValue,compiled,w,finished,effect⟩ := compiler_scheduled_entry_available ops law bound allocation
        before batch dispatched frame prepared.finish entry dispatch noError more ordinalValue
        indexBound typed bounds limits
        encoded signatures functionSlots arithmetic
        (by rw [slots.length]; exact indexBound)
        (by rw [ordinalValue]; exact slots.vacant _ (Nat.le_refl _) (by omega))
        localDemand
      dsimp only [dispatched] at validatedValue
      have unique := prepared_entry_unique prepared w
      have allowance : ∀ counter, preparedFunctionAllowance w.ctx w.body.length counter ≤ functionDemandRate bodyBytes localCount counter := by
        obtain ⟨_,sameCtx,sameBody,_,_⟩ := unique
        exact prepared_allowance_le_rate _ _ _ _ (by simpa only [←sameBody] using bytes) (by simpa only [←sameCtx] using locals)
      let nextScheduler := {before with functions := before.functions.set frame.index (some final.function),budget := final.budget}
      let nextBatch := {dispatched with num_validated := validatedCount,validated_end := prepared.finish}
      have nextPaid : CompilationBudgetEffect base nextScheduler.budget
          (fun counter => (nextBatch.first_func.val+nextBatch.num_validated.val)*functionDemandRate bodyBytes localCount counter) := by
        have combined := paid.trans (effect.weaken allowance)
        apply combined.weaken
        intro counter
        dsimp only [nextBatch,dispatched]
        rw [validatedValue]
        simp only [Nat.add_mul,Nat.one_mul]
        omega
      have nextSlots : FunctionSlotPrefix nextBatch.env.func_type_indices.val.length
          (nextBatch.first_func.val+nextBatch.num_validated.val) nextScheduler.functions.val := by
        have published := slots.publish (by omega) final.function
        simpa only [nextBatch,dispatched,nextScheduler,alloc.vec.Vec.set_val_eq,ordinalValue,validatedValue,Nat.add_assoc] using published
      have restSource : PreparedBatchSource nextBatch.code nextBatch.env bodyBytes localCount peak
          (nextBatch.first_func.val+nextBatch.num_validated.val) nextBatch.validated_end entries finish := by
        simpa only [nextBatch,dispatched,validatedValue,Nat.add_assoc,ending] using rest
      obtain ⟨after,worker,continued,validated,ended,error,queue,published,charged⟩ := ih nextScheduler nextBatch validatedCount restSource
        envelope nextPaid nextSlots (by apply UScalar.eq_of_val_eq; dsimp only [nextBatch,dispatched]; rw [dispatchedValue,validatedValue]) rfl
        noError rfl (by dsimp only [nextBatch,dispatched]; simp only [List.length_cons] at count; omega)
        range bounds limits signatures functionSlots coordinates arithmetic
      refine ⟨after,worker,?_,validated,ended,error,queue,published,charged⟩
      subst loopIndex
      obtain ⟨incremented,increment,incrementValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := batch.num_validated) (y := 1#usize) (by simpa using increment_room _ _ more))
      have incrementEq : incremented = validatedCount := UScalar.eq_of_val_eq (by simpa only [show (1#usize).val = 1 from rfl] using incrementValue.trans validatedValue.symm)
      subst incremented
      have live : batch.num_validated < batch.num_funcs := by simpa only [UScalar.lt_equiv] using more
      exact runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop.available_step
        ⟨nextScheduler, nextBatch, validatedCount, live, compiled, increment⟩ after worker continued

end Itasca.Runtime.Compiler

end

end
