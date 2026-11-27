import Itasca.Runtime.Compiler.Module.Definitions
import Itasca.Runtime.Compiler.Local.Initializer
import Itasca.Runtime.Compiler.Body.Relations.Entry.EntryBodyExecutable
import Itasca.Runtime.Compiler.Local.Publication.ControlMapPublication
import Itasca.Runtime.Compiler.Module.Compilation
import Itasca.Runtime.Compiler.Local.Coordinates.SourceCoordinates
import Itasca.Runtime.Compiler.Local.Source.StartJumpTableBounds
import Itasca.Runtime.Compiler.Body.Relations.Checking.BodyChecked
import Itasca.Runtime.Compiler.Local.Checking.InstructionBounds
import Itasca.Stream.WorkersAndSource
import Itasca.Runtime.Compiler.Module.SourceAndSubmission
import Itasca.Runtime.Compiler.Module.DriverAndCodeRegions
import Itasca.Binary.Scalar.MemoryMeaning
import Itasca.Module.Code.Framing
import Itasca.Stream.RetirementAndFraming
import Itasca.Runtime.Compiler.Body.SourceOperandBound
import Itasca.Runtime.Compiler.Local.Callbacks.CallbackEquations
import Mathlib.Data.List.Forall2
import Itasca.Runtime.Compiler.Local.Relations.Function.CapturedContext
import Itasca.Stream.Completeness

/-!
Proofs for Runtime / Compiler / Module.

This module collects BatchLoopAvailable, EnvironmentCompilationAvailable, StreamingAvailable.
Each section documents its contracts and consumers.
-/

/-! ## BatchLoopAvailable -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

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


end Itasca.Compiler

open Itasca.Representation

/-!
# Batch Loop Available

Prepared entries establish source coordinates, checked bodies and successful finish. Independent per-function demand composes through issued batch entries and the batch loop.
-/

/-! ## EntryFinishAvailable -/

section

/-!
Successful checked-entry finishing from prepared source and publication bounds. Body instruction checks, header publication and final finish establish the entry availability theorem.
-/

/-! ## Entry Header Publication -/

section

namespace Itasca.Compiler
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
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translation.valueType)))
    (endFits : batchStart.val+finish.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    {source : List instr} (encoded : Body.BodyEncoding w.body source) :
    FunctionPublicationHeader final.function ∧ final.frames.val = [] ∧ final.function.code.length ≤ U32.max := by
  have bodyFacts : CompilerEntryFacts w.startedState env w.ctx w.typeIdx w.ft w.body ∧
      StructuredCompiledBody final.function.jump_tables.val
        (ExecutableEmission (CompilerTables.ofFunction final.function) (Translation.Environment.context env w.ctx))
        w.startedState final (env.types.val.map Translation.Environment.funcType)
        (env.func_types.val.map Translation.Environment.funcType) (w.ft.results.val.map Translation.valueType)
        (w.ctx.locals.val.map Translation.valueType) source :=
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

end Itasca.Compiler

end

/-! ## Prepared Publication Start -/

section

namespace Itasca.Compiler
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
  refine ⟨compiler_start_source_coordinates ops signatures functionSlots budget batchStart initial started w.ctx
      w.typeIdx w.bodyStart w.finish created begun,
    compiler_start_map_publication ops law signatures functionSlots budget batchStart initial started w.ctx w.typeIdx
      sig w.bodyStart w.finish lookup beginFits endFits created begun,
    compiler_start_jump_table_bounds ops law signatures functionSlots budget batchStart initial started w.ctx w.typeIdx
      sig w.bodyStart w.finish lookup beginFits endFits created begun,?_⟩
  have length := w.body_bytes.length
  change w.finish.val = w.bodyStart.val+w.body.length at length
  omega

end Itasca.Compiler

end

/-! ## Prepared Body Checked -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

/-- Independent validity and source-only allocation/resource room establish
actual body success and every final source/control-target range check. Initial
publication bounds are constructed from actual fresh function-start internally. -/
theorem prepared_body_checked_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial started : runtime.compiler.FunctionCompiler A} {data env index start}
    (w : CodeEntry.Prepared data env index start)
    (limits : CodeEntry.EnvironmentWithinLimits env)
    (body : Body.Validated w.body env w.ctx.locals w.typeIdx)
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
    prepared_executable_safety ops law w room.size signaturesMatch slotsMatch batchBound created begun
  have contextEq : w.ctx = ⟨w.ctx.locals,w.ft.results⟩ := by
    have results : w.ctx.results = w.ft.results := alloc.vec.Vec.ext _ _ w.context_results
    cases h : w.ctx
    simp_all
  have accepted := compiler_body_checked_available ops law bound allocation started (Translation.Environment.context env w.ctx)
    (w.ctx.locals.val.map Translation.valueType) w.body env w.ctx.locals w.typeIdx w.ft point facts.localLayout
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
end Itasca.Compiler

end

/-! ## Prepared Function Checked -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

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
    (limits : CodeEntry.EnvironmentWithinLimits env)
    (body : Body.Validated w.body env w.ctx.locals w.typeIdx)
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

end Itasca.Compiler

end

/-! ## Entry Checked Available -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

/-- The actual entry parser, function-start callback, and complete body accept
an independently encoded and typed source function. Every compiler resource
premise is numerical and computed over source preparation; no successful target
trace, target certificate, or universal callback-acceptance premise is required. -/
theorem compiler_entry_checked_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (data : Slice U8) (env : metadata.Env) (index start finish : Usize)
    (entry : Binary.Code) (indexBound : index.val < env.func_type_indices.val.length)
    (typed : CodeEntry.Typed env env.func_type_indices.val[index.val] entry)
    (bounds : CodeEntry.Bounds env)
    (limits : CodeEntry.EnvironmentWithinLimits env)
    (encoded : Binary.At (CodeEntry.CodeEncodingWithinLimits) data start entry finish)
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
  obtain ⟨w,ending,body,_⟩ := source_entry_prepared data env index start finish entry indexBound typed bounds
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

end Itasca.Compiler

end

/-! ## Entry Finish Available -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

/-- Independent source validity and numerical demand construct
actual entry success, all publication header/range checks, and empty fixup
frames. The final checker and actual compiler finish both succeed. -/
theorem compiler_entry_finish_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (data : Slice U8) (env : metadata.Env) (index start finish : Usize)
    (entry : Binary.Code) (indexBound : index.val < env.func_type_indices.val.length)
    (typed : CodeEntry.Typed env env.func_type_indices.val[index.val] entry)
    (bounds : CodeEntry.Bounds env)
    (limits : CodeEntry.EnvironmentWithinLimits env)
    (encoded : Binary.At (CodeEntry.CodeEncodingWithinLimits) data start entry finish)
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
  obtain ⟨w⟩ := metadata.validate_code_entry_with.witness _ data start env index finish initial after bounds called
  have signature : env.types.val[w.typeIdx.val]? = some w.ft := by
    simp only [List.getElem?_eq_getElem w.type_lt,w.function_type]
  have valid := code.validate_body_with.sound _ w.body env w.ctx w.typeIdx w.startedState after
    w.body_accepted
  obtain ⟨_,source,_,bodyEncoding,_,_⟩ := valid
  have endFits : batchStart.val+finish.val ≤ Usize.max := by
    have last := w.body_bytes.bound
    omega
  have functionTable : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translation.valueType)) := slotsMatch
  obtain ⟨header,closed,codeBound⟩ := witness_header_publication ops law w signaturesMatch functionTable endFits created bodyEncoding
  rw [called,WP.spec_ok]
  exact ⟨rfl,ranges,header,closed,codeBound,compiler_finish_publication ops after closed header ranges instructions.indexed,effect⟩

end Itasca.Compiler

end

end

/-! ## CompileEntryAvailable -/

section

/-!
Successful scheduled entry compilation from batch entry availability.
-/

/-! ## Batch Entry Available -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- A valid worker entry compiles and finishes successfully, with actual worker
bookkeeping and source-paid budget charges. Only source and numerical demand
premises are supplied; no accepting visitor contract is required. -/
theorem compiler_batch_entry_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (batch : stream.CodeBatch) (index finish : Usize) (entry : Binary.Code)
    (noError : batch.error = none) (remaining : batch.num_validated.val < batch.num_funcs.val)
    (position : index.val = batch.first_func.val+batch.num_validated.val)
    (indexBound : index.val < batch.env.func_type_indices.val.length)
    (typed : CodeEntry.Typed batch.env batch.env.func_type_indices.val[index.val] entry)
    (bounds : CodeEntry.Bounds batch.env)
    (limits : CodeEntry.EnvironmentWithinLimits batch.env)
    (encoded : Binary.At (CodeEntry.CodeEncodingWithinLimits) batch.code batch.validated_end entry finish)
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

end Itasca.Compiler

end

/-! ## Compile Entry Available -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- The scheduler compiles and publishes an independently valid dispatched
entry into its vacant source-indexed slot. All compiler calls, including finish,
are constructed from source-only demand and bounded allocation availability. -/
theorem compiler_scheduled_entry_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (before : runtime.compiler.CompileScheduler A) (batch dispatched : stream.CodeBatch)
    (frame : stream.CodeEntry) (finish : Usize) (entry : Binary.Code)
    (dispatch : stream.CodeBatch.next_entry batch = .ok (.Ok frame,dispatched))
    (noError : dispatched.error = none) (remaining : dispatched.num_validated.val < dispatched.num_funcs.val)
    (position : frame.index.val = dispatched.first_func.val+dispatched.num_validated.val)
    (indexBound : frame.index.val < dispatched.env.func_type_indices.val.length)
    (typed : CodeEntry.Typed dispatched.env dispatched.env.func_type_indices.val[frame.index.val] entry)
    (bounds : CodeEntry.Bounds dispatched.env)
    (limits : CodeEntry.EnvironmentWithinLimits dispatched.env)
    (encoded : Binary.At (CodeEntry.CodeEncodingWithinLimits)
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

end Itasca.Compiler

end

end

/-! ## PreparedBatchSource -/

section

/-!
Prepared compiler-batch source certificates. Entry uniqueness and conservative function-demand envelopes establish the batch source/resource relation.
-/

/-! ## Function Demand Envelope -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

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

end Itasca.Compiler

end

/-! ## Prepared Entry Unique -/

section

namespace Itasca.Compiler
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
  have groupsEq : CodeEntry.Locals.declared first.groups = CodeEntry.Locals.declared second.groups := by
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

end Itasca.Compiler

end

/-! ## Entry Demand -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

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

end Itasca.Compiler

end

/-! ## Prepared Batch Source -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

/-- Independently prepared, encoded, and typed source entries in byte/index
order, with conservative source maxima. Preparation contains only source
metadata and decoding facts, never a compiler callback or target certificate. -/
inductive PreparedBatchSource (data : Slice U8) (env : metadata.Env)
    (bodyBytes localCount peak : Nat) : Nat → Usize → List Binary.Code → Usize → Prop where
  | nil (index start) : PreparedBatchSource data env bodyBytes localCount peak index start [] start
  | cons {index start next finish entry entries}
      (ordinal : Usize) (ordinalValue : ordinal.val = index)
      (indexBound : ordinal.val < env.func_type_indices.val.length)
      (typed : CodeEntry.Typed env env.func_type_indices.val[ordinal.val] entry)
      (encoded : Binary.At (CodeEntry.CodeEncodingWithinLimits) data start entry next)
      (prepared : CodeEntry.Prepared data env ordinal start) (ending : prepared.finish = next)
      (bytes : prepared.body.length ≤ bodyBytes) (locals : prepared.ctx.locals.val.length ≤ localCount)
      (operands : (independentBodyDemand prepared.body env prepared.ctx prepared.typeIdx).operands ≤ peak)
      (rest : PreparedBatchSource data env bodyBytes localCount peak (index+1) next entries finish) :
      PreparedBatchSource data env bodyBytes localCount peak index start (entry::entries) finish

end Itasca.Compiler

end

end

/-! ## BatchLoopAvailable -/

section

/-!
Successful compiler batch-loop execution, including entry dispatch and the published function-slot prefix.
-/

/-! ## Dispatch Entry Available -/

section

namespace Itasca.Compiler
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
    (extent : Module.Code.Extent batch.code batch.dispatch_end content finish)
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
    obtain ⟨sizes,contents⟩ := Module.Code.decoded_unique read read'
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

end Itasca.Compiler

end

/-! ## Function Slot Prefix -/

section

namespace Itasca.Compiler
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

end Itasca.Compiler

end

/-! ## Batch Loop Available -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace
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
    (loopIndex finish : Usize) (entries : List Binary.Code)
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
    (limits : CodeEntry.EnvironmentWithinLimits batch.env)
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
      have encoded : Binary.At (CodeEntry.CodeEncodingWithinLimits) batch.code batch.validated_end entry prepared.finish :=
        ending ▸ ⟨raw,encoding,span⟩
      have rawEncoded : Binary.At (CodeEntry.CodeEncoding) batch.code batch.validated_end entry prepared.finish :=
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

end Itasca.Compiler

end

end

end

/-! ## EnvironmentCompilationAvailable -/

section

open Itasca.Representation

/-! ## CompilerQueueAvailable -/

section

/-!
Compiler queue availability and completed-worker collection. Prepared batch encoding and successful submission establish the retained queue readiness certificate.
-/

/-! ## Completed Worker Queue -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- A queued worker retains its issued identity and a proved successful finish. -/
def CompletedWorker (issued : Stream.Batch.Issued) (worker : Itasca.stream.CodeBatch) : Prop :=
  Stream.Batch.Identity issued worker ∧ Itasca.stream.CodeBatch.finish worker = .ok (.Ok ())

/-- The actual reverse-order poll selects the final logical issued worker. -/
theorem completed_workers_last {queue : List Stream.Batch.Issued} {workers : List Itasca.stream.CodeBatch}
    (related : List.Forall₂ CompletedWorker queue workers) (nonempty : queue ≠ []) :
    ∃ issued rest worker previous, queue = rest++[issued] ∧ workers = previous++[worker] ∧
      List.Forall₂ CompletedWorker rest previous ∧ CompletedWorker issued worker := by
  induction related with
  | nil => exact False.elim (nonempty rfl)
  | @cons issued worker queue workers same related ih =>
    by_cases empty : queue = []
    · subst queue
      cases related
      exact ⟨issued,[],worker,[],rfl,rfl,.nil,same⟩
    · obtain ⟨last,rest,final,previous,queueEq,workersEq,paired,ready⟩ := ih empty
      exact ⟨last,issued::rest,final,worker::previous,by simp only [queueEq,List.cons_append],
        by simp only [workersEq,List.cons_append],.cons same paired,ready⟩

/-- Appending the actual successful worker retains the complete queue relation. -/
theorem completed_workers_append {queue workers issued worker}
    (held : List.Forall₂ CompletedWorker queue workers) (ready : CompletedWorker issued worker) :
    List.Forall₂ CompletedWorker (queue++[issued]) (workers++[worker]) :=
  List.rel_append held (.cons ready .nil)

end Itasca.Compiler

end

/-! ## Prepared Batch Encoding -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

private def sourceOrdinal (env : metadata.Env) (index : Nat)
    (bounded : index < env.func_type_indices.val.length) : Usize :=
  Usize.ofNatCore index (by have cap := env.func_type_indices.property; scalar_tac)

/-- Independent entry encoding and typing construct the prepared source
sequence. The remaining assumptions bound only pure source preparation and
independently validated operand demand. -/
theorem PreparedBatchSource.of_encoded (data : Slice U8) (env : metadata.Env)
    (bodyBytes localCount peak index : Nat) (start finish : Usize) (entries : List Binary.Code)
    (typed : Module.Code.EntriesTyped env index entries)
    (encoded : Binary.At (Binary.Rep (CodeEntry.CodeEncodingWithinLimits)) data start entries finish)
    (bounds : CodeEntry.Bounds env)
    (limits : CodeEntry.EnvironmentWithinLimits env)
    {codeBytes : Nat} (regionSize : data.length ≤ codeBytes)
    (maxima : SourcePreparationMaxima env codeBytes bodyBytes localCount peak) :
    PreparedBatchSource data env bodyBytes localCount peak index start entries finish := by
  induction entries generalizing index start with
  | nil =>
    have same := encoded.rep_nil
    subst finish
    exact .nil index start
  | cons entry entries ih =>
    cases typed with
    | cons head rest =>
      obtain ⟨indexBound,entryTyped,_⟩ := head
      have fullTyped := entryTyped
      let ordinal := sourceOrdinal env index indexBound
      have value : ordinal.val = index := rfl
      obtain ⟨next,entryBytes,remaining⟩ := encoded.rep_cons
      obtain ⟨w,ending,body,size⟩ := source_entry_prepared data env ordinal start next entry
        (by simpa only [value] using indexBound) (by simpa only [value] using fullTyped)
        bounds limits entryBytes
      have selected : w.typeIdx ∈ env.func_type_indices.val := by
        rw [← w.index_type]
        exact List.getElem_mem w.index_lt
      have signature : env.types.val[w.typeIdx.val]? = some w.ft := by
        simp only [List.getElem?_eq_getElem w.type_lt, w.function_type]
      obtain ⟨byteCap,localCap,operandCap⟩ := maxima w.typeIdx selected w.ft signature
      have bodyInRegion : w.body.length ≤ codeBytes := by
        have span := w.body_bytes.length
        have endingBound := w.body_bytes.bound
        simp only [Slice.length] at *
        omega
      have sourceSize := Nat.le_min.mpr ⟨bodyInRegion, size⟩
      have bytes := sourceSize.trans byteCap
      have locals : w.ctx.locals.val.length ≤ localCount := by
        rw [w.context_locals, List.length_append]
        have := w.locals_bound
        omega
      have operands := (independentBodyDemand.byte_bound w.body env w.ctx w.typeIdx limits size body).trans
        ((Nat.mul_le_mul_left 500 sourceSize).trans operandCap)
      exact .cons ordinal value (by simpa only [value] using indexBound) (by simpa only [value] using fullTyped)
        entryBytes w ending bytes locals operands (ih (index+1) next rest remaining)

end Itasca.Compiler

end

/-! ## Submit Available -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

/-- Eager submission compiles every independently prepared source entry,
publishes its completed worker, and retains aggregate numerical resource and
source-slot invariants. Queue publication uses bounded allocation availability. -/
theorem compiler_submit_batch_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (base : runtime.compiler.Budget A) (bodyBytes localCount peak : Nat)
    (before : runtime.compiler.CompileScheduler A) (issued : Stream.Batch.Issued)
    (entries : List Binary.Code)
    (source : PreparedBatchSource issued.code issued.env bodyBytes localCount peak
      issued.first_func.val 0#usize entries (Slice.len issued.code))
    (count : entries.length = issued.num_funcs.val) (bounded : issued.Bounded)
    (envelope : FunctionDemandEnvelope base issued.env.func_type_indices.val.length bodyBytes localCount peak bound)
    (paid : CompilationBudgetEffect base before.budget
      (fun counter => issued.first_func.val*functionDemandRate bodyBytes localCount counter))
    (slots : FunctionSlotPrefix issued.env.func_type_indices.val.length issued.first_func.val before.functions.val)
    (bounds : CodeEntry.Bounds issued.env)
    (limits : CodeEntry.EnvironmentWithinLimits issued.env)
    (signatures : SignatureSequence before.signatures.val issued.env.types.val)
    (functionSlots : before.func_param_slots.val.map (fun word => word.val) =
      issued.env.func_types.val.map (fun ty => signatureSlots ty.params.val))
    (origin : before.code_start.val ≤ Itasca.limits.MAX_MODULE_BYTES.val)
    (queueCapacity : before.completed.length < Usize.max) (queueReserve : before.completed.length+1 ≤ bound) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch ops before issued.seed
      ⦃ out => out.1 = .Ok () ∧
        FunctionSlotPrefix issued.env.func_type_indices.val.length (issued.first_func.val+issued.num_funcs.val) out.2.functions.val ∧
        CompilationBudgetEffect base out.2.budget
          (fun counter => (issued.first_func.val+issued.num_funcs.val)*functionDemandRate bodyBytes localCount counter) ∧
        ∃ worker, out.2.completed.val = before.completed.val++[worker] ∧
          Itasca.stream.CodeBatch.finish worker = .ok (.Ok ()) ⦄ := by
  have arithmetic : before.code_start.val+issued.code_offset.val+issued.code.length ≤ Usize.max := by
    have wordRoom : Itasca.limits.MAX_MODULE_BYTES.val+Itasca.limits.MAX_MODULE_BYTES.val ≤ Usize.max := by
      simp only [Itasca.limits.MAX_MODULE_BYTES]
      scalar_tac
    have coordinates := bounded.2.2
    omega
  obtain ⟨middle,worker,compiled,validated,ended,noError,queue,published,charged⟩ := compiler_batch_loop_available ops law bound allocation
    base bodyBytes localCount peak before issued.seed 0#usize (Slice.len issued.code) entries
    (by simpa only [Stream.Batch.Issued.seed,show (0#usize).val = 0 from rfl,Nat.add_zero] using source)
    envelope (by simpa [Stream.Batch.Issued.seed] using paid) (by simpa [Stream.Batch.Issued.seed] using slots)
    rfl rfl rfl rfl (by simpa [Stream.Batch.Issued.seed] using count) bounded.2.1 bounds limits signatures functionSlots bounded.2.2 arithmetic
  have run := (submit_loop_accepted ops before middle issued.seed worker 0#usize (.Ok ()) compiled).2
  have identity := (run.reachable .seed).validation.1
  obtain ⟨_,_,_,sameCode,_,_,sameCount⟩ := identity
  have finished : Itasca.stream.CodeBatch.finish worker = .ok (.Ok ()) := by
    apply (Itasca.stream.CodeBatch.finish.accepted_iff worker).mpr
    exact ⟨noError,validated.trans sameCount.symm,ended.trans (by rw [sameCode])⟩
  obtain ⟨⟨reply,budget,completed⟩,pushed,status,sameBudget,appended⟩ := WP.spec_imp_exists
    (budget_push_available ops bound allocation middle.budget middle.completed worker
      (by simpa only [queue] using queueCapacity) (by simpa only [queue] using queueReserve))
  dsimp only at status sameBudget appended
  subst reply budget
  have called := runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch.available
    ops before middle issued.seed worker middle.budget completed compiled pushed
  simp only [called, WP.spec_ok]
  refine ⟨True.intro,published,charged,worker,?_,finished⟩
  rw [appended,queue]

end Itasca.Compiler

end

/-! ## Compiler Queue Available -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace
set_option maxRecDepth 4096

/-- The compiler's local numerical and publication state at the source cursor. -/
structure SchedulerCompilationReady {A : Type} (env : metadata.Env) (base : runtime.compiler.Budget A)
    (bodyBytes localCount cursor : Nat) (scheduler : runtime.compiler.CompileScheduler A) : Prop where
  signatures : SignatureSequence scheduler.signatures.val env.types.val
  functionSlots : scheduler.func_param_slots.val.map (fun word => word.val) =
    env.func_types.val.map (fun ty => signatureSlots ty.params.val)
  origin : scheduler.code_start.val ≤ Itasca.limits.MAX_MODULE_BYTES.val
  slots : FunctionSlotPrefix env.func_type_indices.val.length cursor scheduler.functions.val
  paid : CompilationBudgetEffect base scheduler.budget
    (fun counter => cursor*functionDemandRate bodyBytes localCount counter)

/-- Completed workers remain paired with their exact issued identities while
source slots and the aggregate module budget advance independently of polling. -/
def CompilerQueued {A : Type} (env : metadata.Env) (base : runtime.compiler.Budget A)
    (bodyBytes localCount : Nat) (_id : U64) (queue : List Stream.Batch.Issued)
    (cursor : Nat) (scheduler : runtime.compiler.CompileScheduler A) : Prop :=
  SchedulerCompilationReady env base bodyBytes localCount cursor scheduler ∧
    List.Forall₂ CompletedWorker queue scheduler.completed.val

private theorem four_room (length : Nat) (bounded : length < 4) : length < Usize.max := by
  have room : 4 ≤ Usize.max := by scalar_tac
  omega

/-- The concrete eager compiler satisfies a local accepting queue policy under
independent source maxima, aggregate numerical demand, and allocation
availability. The policy uses actual compiler workers and reverse-order polls. -/
theorem compiler_queue_policy {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (env : metadata.Env) (base : runtime.compiler.Budget A)
    (codeBytes bodyBytes localCount peak : Nat)
    (envelope : FunctionDemandEnvelope base env.func_type_indices.val.length bodyBytes localCount peak bound)
    (maxima : SourcePreparationMaxima env codeBytes bodyBytes localCount peak)
    (queueRoom : 4 ≤ bound) :
    StreamAvailability.QueuePolicy (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
      ⟨25000#usize,4#usize⟩ env codeBytes (CompilerQueued env base bodyBytes localCount) := by
  constructor
  · decide
  · decide
  · intro id queue cursor issued before held valid sameEnv moduleId first queueCapacity regionSize
    obtain ⟨ready,workers⟩ := held
    obtain ⟨entries,count,typed,encoded⟩ := valid.entries
    have source := PreparedBatchSource.of_encoded issued.code issued.env bodyBytes localCount peak
      issued.first_func.val 0#usize (Slice.len issued.code) entries
      typed ⟨issued.code.val,encoded,by constructor <;> simp⟩
      valid.entry_bounds valid.limits regionSize
      (by cases sameEnv; exact maxima)
    have length := workers.length_eq
    have capacity : before.completed.length < 4 := by
      simpa only [alloc.vec.Vec.length,show (4#usize).val = 4 from rfl] using length ▸ queueCapacity
    obtain ⟨⟨reply,after⟩,called,status,slots,paid,worker,queueEq,finished⟩ := WP.spec_imp_exists
      (compiler_submit_batch_available ops law bound allocation base bodyBytes localCount peak before issued entries source count valid.bounded
        (by simpa only [sameEnv] using envelope) (by simpa only [sameEnv,first] using ready.paid)
        (by simpa only [sameEnv,first] using ready.slots) valid.entry_bounds
        valid.limits
        (by simpa only [sameEnv] using ready.signatures) (by simpa only [sameEnv] using ready.functionSlots) ready.origin
        (four_room _ capacity) (by omega))
    dsimp only at status slots paid queueEq finished
    subst reply
    obtain ⟨middle,actual,run,actualQueue,shape⟩ := compiler_submit_accepted ops law before after issued.seed called
    have sameWorker : actual = worker := by
      rw [queueEq] at actualQueue
      exact List.cons.inj (List.append_cancel_left actualQueue.symm) |>.1
    subst actual
    have identity := (run.reachable .seed).validation.1
    have static : schedulerStatic after = schedulerStatic before := by rw [shape]; exact run.static
    have fields : after.signatures = before.signatures ∧ after.func_param_slots = before.func_param_slots ∧
        after.code_start = before.code_start := by simpa only [schedulerStatic,Prod.mk.injEq] using static
    refine ⟨after,called,⟨?_,?_⟩⟩
    · exact ⟨by simpa only [fields.1] using ready.signatures,by simpa only [fields.2.1] using ready.functionSlots,
        by simpa only [fields.2.2] using ready.origin,by simpa only [sameEnv,first] using slots,
        by simpa only [sameEnv,first] using paid⟩
    · rw [queueEq]
      exact completed_workers_append workers ⟨identity,finished⟩
  · intro id queue cursor before held nonempty
    obtain ⟨ready,workers⟩ := held
    obtain ⟨issued,rest,worker,previous,queueEq,completedEq,paired,identity,finished⟩ := completed_workers_last workers nonempty
    let completed := alloc.vec.Vec.from previous (by have bound := before.completed.property; rw [completedEq] at bound; simp only [List.length_append,List.length_singleton] at bound; omega)
    let after := {before with completed := completed}
    have polled : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.poll_code_batch ops before = .ok (.Ok worker,after) := by
      rw [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.poll_code_batch.eq]
      simp [alloc.vec.Vec.pop,completedEq,core.option.Option.ok_or,after,completed]
    refine ⟨issued,rest,worker,after,?_,polled,identity,finished,?_,?_⟩
    · rw [queueEq]
      exact (List.perm_append_singleton _ _).symm
    · exact ⟨ready.signatures,ready.functionSlots,ready.origin,ready.slots,ready.paid⟩
    · simpa only [after,completed,alloc.vec.Vec.from_val] using paired

end Itasca.Compiler

end

end

/-! ## EnvironmentCompilationAvailable -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Fresh environment capture constructs the compiler queue, empty publication
prefix, and initial aggregate budget state from independent numerical demand. -/
theorem compiler_environment_compilation_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (before : runtime.compiler.CompileScheduler A) (env : metadata.Env) (bodyBytes localCount : Nat)
    (demand : EnvironmentDemand before env bound)
    (emptyTypes : before.signatures.val = []) (emptySlots : before.func_param_slots.val = [])
    (emptyFunctions : before.functions.val = []) (emptyQueue : before.completed.val = [])
    (origin : before.code_start.val ≤ Itasca.limits.MAX_MODULE_BYTES.val) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready ops before env
      ⦃ out => out.1 = .Ok ⟨25000#usize,4#usize⟩ ∧
        CompilerQueued env before.budget bodyBytes localCount 0#u64 [] 0 out.2 ∧ out.2.tail = before.tail ⦄ := by
  obtain ⟨⟨reply,after⟩,called,status,budget⟩ := WP.spec_imp_exists
    (environment_ready_available ops bound allocation before env demand)
  dsimp only at status budget
  subst reply
  have facts := compiler_environment_ready_sequence ops law before env emptyTypes emptySlots emptyFunctions
  rw [called,WP.spec_ok] at facts
  obtain ⟨signatures,functionSlots,functions⟩ := facts _ rfl
  have frame := compiler_environment_frame ops before after env ⟨25000#usize,4#usize⟩ called
  have fields : after.completed = before.completed ∧ after.tail = before.tail ∧ after.code_start = before.code_start := by
    simpa only [schedulerFrame,Prod.mk.injEq] using frame
  rw [called,WP.spec_ok]
  refine ⟨rfl,⟨?_,?_⟩,fields.2.1⟩
  · refine ⟨signatures,functionSlots,by simpa only [fields.2.2] using origin,?_,?_⟩
    · refine ⟨by simp only [functions,List.length_replicate],Nat.zero_le _,?_,?_⟩
      · intro index impossible
        omega
      · intro index lower upper
        simp [functions,List.getElem?_replicate,upper]
    · rw [budget]
      simpa only [Nat.zero_mul] using CompilationBudgetEffect.refl before.budget
  · rw [fields.1,emptyQueue]
    exact .nil

end Itasca.Compiler

end

end

/-! ## StreamingAvailable -/

section

/-!
Proofs for Runtime / Compiler / Module.

This module collects SourceRegionsAvailable, StreamingAvailable, CompilationAvailable.
Each section documents its contracts and consumers.
-/

/-! ## SourceRegionsAvailable -/

section

/-! ## SourceCompilationDemand -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Aggregate source demand supplies the actual initializer phase after all
functions have consumed at most their conservative source-paid allowances. -/
theorem SourceCompilationDemand.initializers {A env tail limits codeBytes bodyBytes localCount peak bound}
    (demand : SourceCompilationDemand env tail limits codeBytes bodyBytes localCount peak bound)
    (functions : alloc.vec.Vec runtime.bytecode.CompiledFunction)
    (count : functions.length = env.func_type_indices.val.length) (budget : runtime.compiler.Budget A)
    (paid : CompilationBudgetEffect (initialScheduler A limits 0#usize).budget budget
      (fun counter => env.func_type_indices.val.length*functionDemandRate bodyBytes localCount counter)) :
    InitializerCompilationDemand (uninitializedModule env tail functions) budget bound := by
  have limitEq : budget.limits = limits := paid.limits
  have instructions := (paid.counts .instructions).2
  simp only [initialScheduler,ChargeCounter.used,functionDemandRate,show (0#usize).val = 0 from rfl,Nat.zero_add] at instructions
  have countVal : functions.val.length = env.func_type_indices.val.length := count
  constructor
  · have total := demand.instructions
    simp only [uninitializedModule,segmentCompilationDemand,limitEq]
    simp only [sourceInitializerInstructions,alloc.vec.Vec.length] at total
    omega
  · simpa [uninitializedModule,initializerSize,alloc.vec.Vec.new,alloc.vec.Vec.length,countVal] using demand.mappingCapacity
  · simpa [uninitializedModule,initializerSize,alloc.vec.Vec.new,alloc.vec.Vec.length,countVal] using demand.mappingReserve
  · exact demand.literalReserve
  · simpa [uninitializedModule,segmentCompilationDemand] using demand.segmentCapacity
  · simpa [uninitializedModule,segmentCompilationDemand] using demand.segmentReserve
  · exact demand.elementCount
  · exact demand.dataCount
  · exact demand.elementLengths
  · exact demand.dataLengths

/-- Fresh scheduler metadata demand is independent of the source coordinate
chosen by the scanner. -/
theorem SourceCompilationDemand.environment_at {A env tail limits codeBytes bodyBytes localCount peak bound}
    (demand : SourceCompilationDemand env tail limits codeBytes bodyBytes localCount peak bound) (start : Usize) :
    EnvironmentDemand (initialScheduler A limits start) env bound := by
  have ready := demand.environment
  refine ⟨ready.functionLimit,ready.typeLimit,ready.signatureWidths,ready.functionWidths,
    ?_,?_,?_,?_,?_,?_⟩
  all_goals simp only [initialScheduler, alloc.vec.Vec.new, alloc.vec.Vec.length, alloc.vec.Vec.from_val,
    List.length_nil, Nat.zero_add]
  · exact env.types.property
  · exact ready.signatureReserve
  · exact env.func_types.property
  · exact ready.slotReserve
  · exact env.func_type_indices.property
  · exact ready.functionReserve

/-- Source inequalities supply the internal envelope because all initial
counters are zero. Initializer instructions only strengthen the instruction cap. -/
theorem SourceCompilationDemand.functions_at {A : Type} {env tail limits codeBytes bodyBytes localCount peak bound}
    (demand : SourceCompilationDemand env tail limits codeBytes bodyBytes localCount peak bound) (start : Usize) :
    FunctionDemandEnvelope (initialScheduler A limits start).budget
      env.func_type_indices.val.length bodyBytes localCount peak bound := by
  have ready := demand.functions
  refine ⟨ready.size, ?_, ready.temporary, ready.locals, ready.operands, ready.slots⟩
  intro counter
  cases counter <;> simp only [initialScheduler, ChargeCounter.used, ChargeCounter.limit,
    functionDemandRate, show (0#usize).val = 0 from rfl, Nat.zero_add]
  · have total := demand.instructions
    omega
  · exact ready.branches
  · exact ready.controls
  · exact ready.localCharges

end Itasca.Compiler

end

/-! ## SourceRegionsAvailable -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

private theorem slice_value (data region : Slice U8) (first last : Usize)
    (ordered : first.val ≤ last.val) (bounded : last.val ≤ data.length)
    (called : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) data ⟨first,last⟩ = .ok region) :
    region.val = data.val.slice first.val last.val := by
  have post := core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec ⟨first,last⟩ data (by scalar_tac) bounded
  change core.slice.index.SliceIndexRangeUsizeSlice.index ⟨first,last⟩ data = .ok region at called
  rw [called,WP.spec_ok] at post
  exact post.1

/-- The runtime's immutable source makes every region of the canonical split
available whenever its scanner selected those same byte coordinates. -/
theorem compiler_source_regions_available (data : Slice U8) (regions : Itasca.stream.SliceSource)
    (codeStart codeEnd : Usize)
    (split : Stream.CompleteRegions.ComputedSplit data regions)
    (selected : Itasca.stream.find_code_region data = .ok (codeStart,codeEnd)) :
    Stream.Source.Available runtime.compiler.CompileSource.Insts.ItascaStreamSource
      {bytes := data,code_start := codeStart,code_end := codeEnd} regions.env.val regions.code.val regions.tail.val := by
  obtain ⟨first,last,scanned,environment,code,tail⟩ := split
  have same : first = codeStart ∧ last = codeEnd := by
    simpa only [Result.ok.injEq,Prod.mk.injEq] using scanned.symm.trans selected
  simp only [same.1,same.2] at environment code tail
  obtain ⟨ordered,bounded⟩ := Itasca.stream.find_code_region.bounds data codeStart codeEnd selected
  have envValue := slice_value data regions.env 0#usize codeStart (by simp) (by omega) environment
  have codeValue := slice_value data regions.code codeStart codeEnd ordered bounded code
  have tailValue := slice_value data regions.tail codeEnd (Slice.len data) (by simpa using bounded) (by simp) tail
  have envEq : regions.env.val = data.val.take codeStart.val := by simpa [List.slice] using envValue
  have tailEq : regions.tail.val = data.val.drop codeEnd.val := by
    simp only [List.slice,Slice.len_val] at tailValue
    rw [←List.length_drop] at tailValue
    simpa only [List.take_length] using tailValue
  have available := source_available ({bytes := data,code_start := codeStart,code_end := codeEnd} : runtime.compiler.CompileSource)
    ⟨ordered,bounded⟩
  simpa only [sourceEnvironment,sourceCode,sourceTail,←envEq,←codeValue,←tailEq] using available

end Itasca.Compiler

end

end

/-! ## StreamingAvailable -/

section

/-!
Successful compiler streaming from source submission invariants through the remaining driver work. The proof follows actual submit/poll results under availability premises.
-/

/-! ## Source Submission Available -/

section

open Aeneas Aeneas.Std Itasca

namespace Itasca.Compiler.StreamAvailability
open Binary Stream.Scheduler

/-- The scheduler's queue of valid work matches the pending vector, and the remaining bytes and
entries keep their independent encoding and typing. -/
def CompleteInvariant {V : Type} (Queued : U64 → List Stream.Batch.Issued → Nat → V → Prop)
    (code : Slice U8) (env : metadata.Env) (id : U64) (config : Itasca.stream.Config)
    (v : V) (pending : alloc.vec.Vec Usize) (pos func batchId : Usize) : Prop :=
  batchId.val ≤ func.val ∧ pending.length ≤ batchId.val ∧ pending.length ≤ config.max_batches.val ∧
    ∃ queue entries, Queued id queue func.val v ∧ ValidQueue id queue ∧
      pending.val.Perm (queue.map Stream.Batch.Issued.batch_id) ∧
      func.val + entries.length = env.func_type_indices.val.length ∧
      Module.Code.EntriesTyped env func.val entries ∧
      At (Rep (CodeEntry.CodeEncodingWithinLimits)) code pos entries (Slice.len code)

/-- A successful submission leaves a valid queue whose batch IDs are a permutation of the pending
IDs, so the final drain can retire exactly this queue. Errors are excluded. -/
def CompletePost {V : Type} (Queued : U64 → List Stream.Batch.Issued → Nat → V → Prop)
    (id : U64) (config : Itasca.stream.Config) (env : metadata.Env) :
    (core.result.Result (alloc.vec.Vec Usize) error.Error × V) → Prop
  | (.Ok pending, v) => ∃ queue, Queued id queue env.func_type_indices.val.length v ∧ ValidQueue id queue ∧
      pending.val.Perm (queue.map Stream.Batch.Issued.batch_id) ∧ pending.length ≤ config.max_batches.val
  | (.Err _, _) => False

private def CompleteBodyPost {V : Type} (Queued : U64 → List Stream.Batch.Issued → Nat → V → Prop)
    (code : Slice U8) (env : metadata.Env) (id : U64) (config : Itasca.stream.Config) (func : Usize) :
    ControlFlow (V × alloc.vec.Vec Usize × Usize × Usize × Usize)
      (core.result.Result (alloc.vec.Vec Usize) error.Error × V) → Prop
  | .done result => CompletePost Queued id config env result
  | .cont (v, pending, pos, next, batchId) =>
      CompleteInvariant Queued code env id config v pending pos next batchId ∧ func.val < next.val

private theorem increment (n bound : Usize) (h : n.val < bound.val) :
    ∃ next, (n + 1#usize : Result Usize) = .ok next ∧ next.val = n.val + 1 := by
  obtain ⟨next, hr, hv⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x := n) (y := 1#usize) (by scalar_tac))
  exact ⟨next, hr, by simpa using hv⟩

private theorem resume_complete {S V : Type} (source : Itasca.stream.Source S)
    (visitor : Itasca.stream.StreamingVisitor V) (Queued : U64 → List Stream.Batch.Issued → Nat → V → Prop)
    (config : Itasca.stream.Config)
    (state : S) (moduleId : U64) (env : metadata.Env) (code : Slice U8)
    (ha : QueuePolicy visitor config env code.length Queued)
    (environment tail : List U8) (hs : Stream.Source.Available source state environment code.val tail)
    (henv : CodeEntry.Bounds env)
    (hlimits : CodeEntry.EnvironmentWithinLimits env)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (v : V) (pending : alloc.vec.Vec Usize) (pos func batchId : Usize)
    (queue : List Stream.Batch.Issued) (entries : List Binary.Code)
    (hv : Queued moduleId queue func.val v) (hq : ValidQueue moduleId queue)
    (hp : pending.val.Perm (queue.map Stream.Batch.Issued.batch_id))
    (hcount : func.val + entries.length = env.func_type_indices.val.length)
    (htyped : Module.Code.EntriesTyped env func.val entries)
    (hbytes : At (Rep (CodeEntry.CodeEncodingWithinLimits)) code pos entries (Slice.len code))
    (hbatch : batchId.val ≤ func.val) (hpending : pending.length ≤ batchId.val)
    (hfunc : func.val < env.func_type_indices.val.length)
    (hroom : pending.length < config.max_batches.val) :
    (do
      let r ← Itasca.stream.get_next_batch source state (Slice.len code) pos func (alloc.vec.Vec.len env.func_type_indices) config.batch_bytes
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let (finish, next) := val
        let r1 ← Itasca.stream.read_exact source state pos finish
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue bytes =>
          let pending1 ← alloc.vec.Vec.push pending batchId
          let count ← next - func
          let (r2, v') ← visitor.submit_code_batch v
            { module_id := moduleId, batch_id := batchId, env := env, code := bytes,
              code_offset := pos, first_func := func, num_funcs := count,
              num_dispatched := 0#usize, dispatch_end := 0#usize,
              num_validated := 0#usize, validated_end := 0#usize, error := none }
          let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
          match cf2 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let nextId ← batchId + 1#usize
            Result.ok (ControlFlow.cont (v', pending1, finish, next, nextId))
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r3 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              (alloc.vec.Vec Usize) (core.convert.FromSame error.Error) residual
            Result.ok (ControlFlow.done (r3, v'))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (alloc.vec.Vec Usize) (core.convert.FromSame error.Error) residual
          Result.ok (ControlFlow.done (r2, v))
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          (alloc.vec.Vec Usize) (core.convert.FromSame error.Error) residual
        Result.ok (ControlFlow.done (r1, v))) ⦃ out => CompleteBodyPost Queued code env moduleId config func out ⦄ := by
  obtain ⟨finish, next, taken, rest, view, hframe, hframepost, heq, hne, hnext, hrestcount,
      htakenbytes, hrestbytes, hread, hspan, hrep⟩ := Itasca.stream.get_next_batch.complete_view source state
    environment tail code hs (Slice.len code) pos func (alloc.vec.Vec.len env.func_type_indices)
    config.batch_bytes entries rfl (by simpa using hcap) (by simpa using hfunc)
    (by simpa using hcount) hbytes
  obtain ⟨hprogress, hfinishbound, hnextprogress, hnextbound⟩ := hframepost
  rw [heq] at htyped
  obtain ⟨htaken, hrest⟩ := htyped.split
  have hnexttyped : Module.Code.EntriesTyped env next.val rest := by simpa [hnext] using hrest
  obtain ⟨nextPending, hpush, hpushval⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec pending batchId (by scalar_tac))
  obtain ⟨count, hsub, hsubval⟩ := WP.spec_imp_exists
    (UScalar.sub_spec (x := next) (y := func) (by scalar_tac))
  have hcountval : count.val = taken.length := by omega
  let issued : Stream.Batch.Issued := ⟨moduleId, batchId, env, view, pos, func, count⟩
  have hbounded : issued.Bounded := by
    have hlen := hspan.length
    change finish.val = pos.val + view.length at hlen
    dsimp [issued, Stream.Batch.Issued.Bounded]
    have hfunctions : next.val ≤ env.func_type_indices.val.length := by simpa using hnextbound
    have hfinishcap : finish.val ≤ limits.MAX_MODULE_BYTES.val :=
      le_trans (by simpa using hfinishbound) hcap
    simp only [Slice.length] at hlen ⊢
    omega
  have hvalid : Valid issued :=
    ⟨hbounded, henv, hlimits, taken, hcountval.symm, htaken, hrep⟩
  have hqueuelen : queue.length = pending.length := by
    simpa [alloc.vec.Vec.length] using hp.length_eq.symm
  obtain ⟨v', hsubmit, hv'⟩ := ha.submit moduleId queue func.val issued v hv hvalid rfl rfl rfl (by omega)
    (by
      have span := hspan.length
      have bounded := hspan.bound
      change view.length ≤ code.length
      simp only [Slice.length] at *
      omega)
  have hvNext : Queued moduleId (queue++[issued]) next.val v' := by
    have nextValue : func.val+issued.num_funcs.val = next.val := by dsimp only [issued]; omega
    simpa only [nextValue] using hv'
  obtain ⟨nextId, hinc, hnextId⟩ := increment batchId (alloc.vec.Vec.len env.func_type_indices)
    (by simpa using (show batchId.val < env.func_type_indices.val.length by omega))
  simp only [issued, Stream.Batch.Issued.seed] at hsubmit
  simp [hframe, core.result.Result.Insts.CoreOpsTry.branch, hread, hpush, hsub, hsubmit, hinc]
  change CompleteInvariant Queued code env moduleId config v' nextPending finish next nextId ∧ _
  constructor
  · refine ⟨by omega, ?_, ?_, queue ++ [issued], rest, hvNext, ?_, ?_, ?_, hnexttyped, hrestbytes⟩
    · change nextPending.val.length ≤ _
      rw [hpushval, List.length_append, List.length_singleton]
      change pending.val.length ≤ _ at hpending
      omega
    · change nextPending.val.length ≤ _
      rw [hpushval, List.length_append, List.length_singleton]
      change pending.val.length < _ at hroom
      omega
    · intro old hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hq old hm
      · have he : old = issued := by simpa using hm
        exact he ▸ ⟨rfl, hvalid⟩
    · rw [hpushval, List.map_append, List.map_cons, List.map_nil]
      exact hp.append_right [batchId]
    · simpa using hrestcount.symm
  · simpa using hnextprogress

end Itasca.Compiler.StreamAvailability

namespace Itasca.Compiler.StreamAvailability
open Binary Stream.Scheduler

private theorem body_complete {S V : Type} (source : Itasca.stream.Source S)
    (visitor : Itasca.stream.StreamingVisitor V) (Queued : U64 → List Stream.Batch.Issued → Nat → V → Prop)
    (config : Itasca.stream.Config)
    (state : S) (moduleId : U64) (env : metadata.Env) (code : Slice U8)
    (ha : QueuePolicy visitor config env code.length Queued)
    (environment tail : List U8) (hs : Stream.Source.Available source state environment code.val tail)
    (henv : CodeEntry.Bounds env)
    (hlimits : CodeEntry.EnvironmentWithinLimits env)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (v : V) (pending : alloc.vec.Vec Usize) (pos func batchId : Usize)
    (hinv : CompleteInvariant Queued code env moduleId config v pending pos func batchId) :
    Itasca.stream.submit_code_batches_loop.body source visitor moduleId state env.types env.imports
      env.globals env.exports env.elements env.data_count env.declared_funcs env.start
      env.func_type_indices env.func_types
      env.table_types env.mem_types env.global_types env.num_imported_funcs env.num_imported_globals
      (Slice.len code) config (alloc.vec.Vec.len env.func_type_indices) v pending pos func batchId
        ⦃ CompleteBodyPost Queued code env moduleId config func ⦄ := by
  obtain ⟨hbatch, hpending, hmax, queue, entries, hv, hq, hp, hcount, htyped, hbytes⟩ := hinv
  unfold Itasca.stream.submit_code_batches_loop.body
  by_cases hmore : func < alloc.vec.Vec.len env.func_type_indices
  · rw [if_pos hmore]
    have hfunc : func.val < env.func_type_indices.val.length := by simpa using hmore
    by_cases hfull : alloc.vec.Vec.len pending ≥ config.max_batches
    · rw [if_pos hfull]
      have hnonempty : pending.val ≠ [] := by
        intro he
        have hz : pending.length = 0 := by simp [alloc.vec.Vec.length, he]
        have hp := ha.capacity_positive
        have hge : config.max_batches.val ≤ pending.length := by simpa using hfull
        omega
      obtain ⟨v', remaining, rest, hr, hv', hvalid, hids, hlen⟩ :=
        retire_complete visitor config env Queued ha moduleId queue func.val v pending hv hq hp hnonempty
      rw [hr]
      simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
      have hresume := resume_complete source visitor Queued config state moduleId env code ha
        environment tail hs henv hlimits hcap v' remaining pos func batchId rest entries
        hv' hvalid hids hcount htyped hbytes hbatch (by omega) hfunc (by omega)
      simp [core.result.Result.Insts.CoreOpsTry.branch] at hresume ⊢
      convert hresume using 1
      rfl
    · rw [if_neg hfull]
      exact resume_complete source visitor Queued config state moduleId env code ha
        environment tail hs henv hlimits hcap v pending pos func batchId queue entries
        hv hq hp hcount htyped hbytes hbatch hpending hfunc (by scalar_tac)
  · rw [if_neg hmore]
    have hn : env.func_type_indices.val.length ≤ func.val := by scalar_tac
    have he : entries = [] := by simpa using (show entries.length = 0 by omega)
    subst entries
    have hpos : pos = Slice.len code := hbytes.rep_nil.symm
    simp only [hpos, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    have cursor : func.val = env.func_type_indices.val.length := by simpa using hcount
    exact ⟨queue,by simpa only [cursor] using hv,hq,hp,hmax⟩

end Itasca.Compiler.StreamAvailability

namespace Itasca.Compiler.StreamAvailability
open Binary Stream.Scheduler

/-- The submission loop accepts independently encoded and typed entries, maintaining the queue of
outstanding work as its function cursor advances. -/
theorem submit_loop_complete_spec {S V : Type} (source : Itasca.stream.Source S)
    (visitor : Itasca.stream.StreamingVisitor V) (Queued : U64 → List Stream.Batch.Issued → Nat → V → Prop)
    (config : Itasca.stream.Config)
    (state : S) (moduleId : U64) (env : metadata.Env) (code : Slice U8)
    (ha : QueuePolicy visitor config env code.length Queued)
    (environment tail : List U8) (hs : Stream.Source.Available source state environment code.val tail)
    (henv : CodeEntry.Bounds env)
    (hlimits : CodeEntry.EnvironmentWithinLimits env)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (v : V) (pending : alloc.vec.Vec Usize) (pos func batchId : Usize)
    (hinv : CompleteInvariant Queued code env moduleId config v pending pos func batchId) :
    Itasca.stream.submit_code_batches_loop source visitor moduleId state env.types env.imports
      env.globals env.exports env.elements env.data_count env.declared_funcs env.start
      env.func_type_indices env.func_types
      env.table_types env.mem_types env.global_types env.num_imported_funcs env.num_imported_globals
      (Slice.len code) config v pending pos func batchId (alloc.vec.Vec.len env.func_type_indices)
        ⦃ CompletePost Queued moduleId config env ⦄ := by
  unfold Itasca.stream.submit_code_batches_loop
  apply loop.spec_decr_nat (fun s => env.func_type_indices.val.length - s.2.2.2.1.val)
    (fun s => CompleteInvariant Queued code env moduleId config
      s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2)
  · rintro ⟨v', pending', pos', func', batchId'⟩ h
    apply WP.spec_mono (body_complete source visitor Queued config state moduleId env
      code ha environment tail hs henv hlimits hcap v' pending' pos' func' batchId' h)
    intro out hout
    cases out with
    | done result => exact hout
    | cont next =>
      obtain ⟨v'', pending'', pos'', func'', batchId''⟩ := next
      obtain ⟨hinv'', hprogress⟩ := hout
      refine ⟨hinv'', ?_⟩
      obtain ⟨_, _, _, queue, entries, _, _, _, hcount, _, _⟩ := hinv''
      dsimp only
      omega
  · exact hinv

/-- From an independently encoded and typed code region and an accepting scheduler policy,
`Itasca.stream.submit_code_batches` submits and retires batches successfully. The remaining valid queue
matches the pending IDs for the final drain. -/
theorem submit_complete {S V : Type} (source : Itasca.stream.Source S)
    (visitor : Itasca.stream.StreamingVisitor V) (Queued : U64 → List Stream.Batch.Issued → Nat → V → Prop)
    (config : Itasca.stream.Config)
    (state : S) (moduleId : U64) (env : metadata.Env) (code : Slice U8)
    (ha : QueuePolicy visitor config env code.length Queued) (start : Usize)
    (environment tail : List U8) (hs : Stream.Source.Available source state environment code.val tail)
    (henv : CodeEntry.Bounds env)
    (hlimits : CodeEntry.EnvironmentWithinLimits env)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (entries : List Binary.Code) (hcount : entries.length = env.func_type_indices.val.length)
    (htyped : Module.Code.EntriesTyped env 0 entries)
    (hbytes : At (Rep (CodeEntry.CodeEncodingWithinLimits)) code start entries (Slice.len code))
    (v : V) (hv : Queued moduleId [] 0 v) :
    ∃ pending v' queue,
      Itasca.stream.submit_code_batches source visitor moduleId state env (Slice.len code) start config v =
        .ok (.Ok pending, v') ∧ Queued moduleId queue env.func_type_indices.val.length v' ∧ ValidQueue moduleId queue ∧
      pending.val.Perm (queue.map Stream.Batch.Issued.batch_id) ∧
      pending.length ≤ config.max_batches.val := by
  have hi : CompleteInvariant Queued code env moduleId config v
      (alloc.vec.Vec.new _) start 0#usize 0#usize := by
    refine ⟨by simp, by simp [alloc.vec.Vec.new], by simp [alloc.vec.Vec.new],
      [], entries, hv, ?_, ?_, by simpa using hcount, htyped, hbytes⟩
    · simp [ValidQueue]
    · simp [alloc.vec.Vec.new]
  obtain ⟨⟨r, v'⟩, hr, hp⟩ := WP.spec_imp_exists
    (submit_loop_complete_spec source visitor Queued config state moduleId env code ha
      environment tail hs henv hlimits hcap v (alloc.vec.Vec.new _) start 0#usize 0#usize hi)
  cases r with
  | Err e => exact False.elim hp
  | Ok pending =>
    obtain ⟨queue, hv', hvalid, hids, hmax⟩ := hp
    exact ⟨pending, v', queue, hr, hv', hvalid, hids, hmax⟩

end Itasca.Compiler.StreamAvailability

end

/-! ## Remaining Available -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

private theorem compiler_hooks_accept {A : Type} (ops : runtime.platform.Alloc A) :
    Module.Tail.HooksAccept (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops).metadataModuleVisitorInst := by
  intro before chunk
  exact ⟨before,rfl⟩

/-- Actual environment capture, all issued batches, tail delivery, and final
reverse-order retirement accept from independent region validity and numerical
demand. No successful compiler call or emitted certificate is an input. -/
theorem compiler_remaining_available {A S : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (source : Itasca.stream.Source S) (state : S) (id : U64)
    (data : Slice U8) (raw : Binary.Module) (regions : Itasca.stream.SliceSource)
    (env : metadata.Env) (tail : metadata.Tail)
    (certificate : Stream.CompleteRegions.Certificate data raw regions env tail)
    (available : Stream.Source.Available source state regions.env.val regions.code.val regions.tail.val)
    (before : runtime.compiler.CompileScheduler A) (bodyBytes localCount peak : Nat)
    (environmentDemand : EnvironmentDemand before env bound)
    (envelope : FunctionDemandEnvelope before.budget env.func_type_indices.val.length bodyBytes localCount peak bound)
    (maxima : SourcePreparationMaxima env regions.code.length bodyBytes localCount peak) (queueRoom : 4 ≤ bound)
    (emptyTypes : before.signatures.val = []) (emptySlots : before.func_param_slots.val = [])
    (emptyFunctions : before.functions.val = []) (emptyQueue : before.completed.val = [])
    (origin : before.code_start.val ≤ Itasca.limits.MAX_MODULE_BYTES.val) :
    ∃ after, ∃ run : Stream.Run.Remaining source (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
      id state env (Slice.len regions.env) before after,
      run.tail = tail ∧ after.tail = some tail ∧
      CompilerQueued env before.budget bodyBytes localCount id [] env.func_type_indices.val.length after := by
  let visitor := runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops
  let Queued := CompilerQueued env before.budget bodyBytes localCount
  have policy := compiler_queue_policy ops law bound allocation env before.budget regions.code.length bodyBytes localCount peak envelope maxima queueRoom
  obtain ⟨len,lengthCall,lengthValue⟩ := available.code_len_read
  have lengthEq : len = Slice.len regions.code := UScalar.eq_of_val_eq lengthValue
  subst len
  have codeRoom : regions.env.length+regions.code.length ≤ Itasca.limits.MAX_MODULE_BYTES.val := by
    have bytes := congrArg List.length certificate.bytes
    have bounded := certificate.bounded
    simp only [List.length_append,Slice.length] at bytes bounded ⊢
    omega
  obtain ⟨codeEnd,codeBound,codeEndValue⟩ := Itasca.limits.add_offset.complete
    (Slice.len regions.env) (Slice.len regions.code) (by simpa using codeRoom)
  obtain ⟨entries,header,encoded⟩ := certificate.code
  have headerCall := Itasca.stream.read_code_header.complete source state (Slice.len regions.code)
    env entries regions.code regions.env.val regions.tail.val available rfl (by omega) header
  obtain ⟨⟨reply,configured⟩,configuredCall,status,configuredReady,configuredTail⟩ := WP.spec_imp_exists
    (compiler_environment_compilation_available ops law bound allocation before env bodyBytes localCount environmentDemand
      emptyTypes emptySlots emptyFunctions emptyQueue origin)
  dsimp only at status configuredReady configuredTail
  subst reply
  obtain ⟨pending,submitted,queue,submitCall,submittedReady,valid,ids,pendingBound⟩ := StreamAvailability.submit_complete source visitor Queued
    ⟨25000#usize,4#usize⟩ state id env regions.code policy entries regions.env.val regions.tail.val available
    certificate.entry_bounds certificate.signature_limits (by omega) raw.codes certificate.code_count certificate.typed encoded
    configured configuredReady
  obtain ⟨tailBytes,tailCall,tailValue⟩ := available.tail_read
  have tailEq : tailBytes = regions.tail := Slice.ext _ _ tailValue
  subst tailBytes
  have wholeRoom : codeEnd.val+regions.tail.length ≤ Itasca.limits.MAX_MODULE_BYTES.val := by
    have endEq : codeEnd.val = regions.env.length+regions.code.length := by simpa using codeEndValue
    have bytesLength : data.length = regions.env.length+regions.code.length+regions.tail.length := by
      simpa [List.length_append,Nat.add_assoc] using congrArg List.length certificate.bytes
    rw [endEq,←bytesLength]
    exact certificate.bounded
  obtain ⟨moduleEnd,moduleBound,_⟩ := Itasca.limits.add_offset.complete codeEnd (Slice.len regions.tail) (by simpa using wholeRoom)
  obtain ⟨decoded,decodedCall⟩ := metadata.validate_tail_with.accepted_lift visitor.metadataModuleVisitorInst
    (compiler_hooks_accept ops) regions.tail 0#usize env submitted tail certificate.tail_accepted
  have decodedEq : decoded = submitted := metadata.validate_tail_with.accepted_invariant visitor.metadataModuleVisitorInst
    (fun scheduler => scheduler = submitted) (compiler_custom_preserves ops _) regions.tail 0#usize env submitted tail decoded decodedCall rfl
  subst decoded
  let ready := {submitted with tail := some tail}
  have readyQueued : Queued id queue env.func_type_indices.val.length ready := by
    obtain ⟨stateReady,workers⟩ := submittedReady
    exact ⟨⟨stateReady.signatures,stateReady.functionSlots,stateReady.origin,stateReady.slots,stateReady.paid⟩,workers⟩
  obtain ⟨after,remaining,drainCall,empty,afterQueued⟩ := StreamAvailability.drain_complete visitor ⟨25000#usize,4#usize⟩ env Queued policy
    id queue env.func_type_indices.val.length ready pending readyQueued valid ids
  have finalFrame := compiler_drain_frame ops id ready after pending remaining drainCall
  refine ⟨after,⟨Slice.len regions.code,codeEnd,entries,⟨25000#usize,4#usize⟩,configured,pending,submitted,submitted,
    regions.tail,moduleEnd,submitted,tail,submitted,ready,remaining,lengthCall,codeBound,headerCall,configuredCall,
    by decide,by decide,submitCall,rfl,tailCall,moduleBound,rfl,decodedCall,rfl,drainCall⟩,rfl,?_,afterQueued⟩
  rw [finalFrame]

end Itasca.Compiler

end

/-! ## Streaming Available -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- The complete streaming compiler phase accepts independently certified
source regions from source-only numerical demand and allocation availability.
The certificate is produced by independent validator completeness, not by an
accepted compiler trace or a caller-supplied emitted-code certificate. -/
theorem compiler_streaming_available {A S : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (source : Itasca.stream.Source S) (state : S) (id : U64)
    (data : Slice U8) (raw : Binary.Module) (regions : Itasca.stream.SliceSource)
    (env : metadata.Env) (tail : metadata.Tail)
    (certificate : Stream.CompleteRegions.Certificate data raw regions env tail)
    (available : Stream.Source.Available source state regions.env.val regions.code.val regions.tail.val)
    (before : runtime.compiler.CompileScheduler A) (storage : metadata.Env) (bodyBytes localCount peak : Nat)
    (environmentDemand : EnvironmentDemand before env bound)
    (envelope : FunctionDemandEnvelope before.budget env.func_type_indices.val.length bodyBytes localCount peak bound)
    (maxima : SourcePreparationMaxima env regions.code.length bodyBytes localCount peak) (queueRoom : 4 ≤ bound)
    (emptyTypes : before.signatures.val = []) (emptySlots : before.func_param_slots.val = [])
    (emptyFunctions : before.functions.val = []) (emptyQueue : before.completed.val = [])
    (origin : before.code_start.val ≤ Itasca.limits.MAX_MODULE_BYTES.val) :
    ∃ after, ∃ run : Stream.Run.Accepted source (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
      id state before after env,
      Itasca.stream.validate_streaming source (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
        id state before storage = .ok (.Ok (),after,env) ∧
      run.remaining.tail = tail ∧ after.tail = some tail ∧
      CompilerQueued env before.budget bodyBytes localCount id [] env.func_type_indices.val.length after := by
  let visitor := runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops
  have hooks : Module.Tail.HooksAccept visitor.metadataModuleVisitorInst := by
    intro scheduler chunk
    exact ⟨scheduler,rfl⟩
  obtain ⟨bytes,environmentCall,environmentValue⟩ := available.environment_read
  have bytesEq : bytes = regions.env := Slice.ext _ _ environmentValue
  subst bytes
  have environmentRoom : regions.env.length ≤ Itasca.limits.MAX_MODULE_BYTES.val := by
    have length := congrArg List.length certificate.bytes
    have bound := certificate.bounded
    simp only [List.length_append,Slice.length] at length bound ⊢
    omega
  obtain ⟨environmentEnd,environmentBound,environmentLength⟩ := Itasca.limits.add_offset.complete 0#usize (Slice.len regions.env)
    (by simpa using environmentRoom)
  have endEq : environmentEnd = Slice.len regions.env := UScalar.eq_of_val_eq (by simpa using environmentLength)
  subst environmentEnd
  obtain ⟨decoded,decodeCall⟩ := metadata.validate_env_with.accepted_lift visitor.metadataModuleVisitorInst hooks regions.env before env
    (Slice.len regions.env) certificate.environment
  have decodedEq : decoded = before := metadata.validate_env_with.accepted_invariant visitor.metadataModuleVisitorInst
    (fun scheduler => scheduler = before) (compiler_custom_preserves ops _) regions.env before env (Slice.len regions.env) decoded decodeCall rfl
  subst decoded
  obtain ⟨after,remaining,tailEq,delivered,retained⟩ := compiler_remaining_available ops law bound allocation source state id
    data raw regions env tail certificate available before bodyBytes localCount peak environmentDemand envelope maxima queueRoom
    emptyTypes emptySlots emptyFunctions emptyQueue origin
  let run : Stream.Run.Accepted source visitor id state before after env :=
    ⟨regions.env,Slice.len regions.env,before,before,environmentCall,environmentBound,rfl,decodeCall,remaining⟩
  exact ⟨after,run,run.run storage,tailEq,delivered,retained⟩

end Itasca.Compiler

end

end

/-! ## CompilationAvailable -/

section

/-!
# Successful compilation from source validity

Independent module validity, source-derived compiler bounds and available bounded allocations construct actual compilation success. Initializer typing is derived from the source certificate.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

private theorem certificate_initializer_typing {bytes raw regions env tail}
    (certificate : Stream.CompleteRegions.Certificate bytes raw regions env tail)
    (functions : alloc.vec.Vec runtime.bytecode.CompiledFunction) :
    InitializerSourceTyping (uninitializedModule env tail functions) := by
  have environment := Itasca.metadata.validate_env.semantic_spec regions.env
  rw [certificate.environment,WP.spec_ok] at environment
  obtain ⟨_,_,valid,_,_,_⟩ := environment
  have dataValid := Itasca.metadata.validate_tail.spec regions.tail 0#usize env (by simp)
  rw [certificate.tail_accepted,WP.spec_ok] at dataValid
  exact InitializerSourceTyping.of_valid valid dataValid.2.1

/-- Independently valid modules for WebAssembly Core 2.0 compile successfully
when explicit source-only compiler bounds and bounded allocations are available.
Aeneas normal return and the successful Rust result are both conclusions. -/
theorem compile_with_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (bytes : Slice U8) (raw : Binary.Module)
    (limits : runtime.compiler.CompileLimits) (valid : ValidCompilationSource bytes raw)
    (eligible : InternalCompileEligible bytes raw limits bound) :
    ∃ executable, runtime.compiler.compile_with ops bytes limits = .ok (.Ok executable) := by
  obtain ⟨regions,env,tail,certificate⟩ := Stream.CompleteRegions.prepare bytes raw valid.encoding valid.signatures
    valid.elaborated valid.typed valid.restrictions
  obtain ⟨bodyBytes,localCount,peak,demand⟩ := eligible.demand env tail certificate.realization
  obtain ⟨codeStart,codeEnd,scanned,_,_,_⟩ := certificate.split
  have regionCall : runtime.compiler.code_region bytes = .ok (codeStart,codeEnd) :=
    (compiler_code_region_eq_stream bytes raw valid.encoding).trans scanned
  have available := compiler_source_regions_available bytes regions codeStart codeEnd certificate.split scanned
  have origin : codeStart.val ≤ Itasca.limits.MAX_MODULE_BYTES.val := by
    obtain ⟨ordered,bounded⟩ := Itasca.stream.find_code_region.bounds bytes codeStart codeEnd scanned
    exact (ordered.trans bounded).trans certificate.bounded
  have codeSize : regions.code.length ≤ bytes.length := by
    have lengths := congrArg List.length certificate.bytes
    simp only [Slice.length, List.length_append] at *
    omega
  have regionMaxima : SourcePreparationMaxima env regions.code.length bodyBytes localCount peak := by
    intro index member signature found
    obtain ⟨body, locals, operands⟩ := demand.maxima index member signature found
    have smaller : Nat.min regions.code.length Itasca.limits.MAX_FUNCTION_BYTES.val ≤
        Nat.min bytes.length Itasca.limits.MAX_FUNCTION_BYTES.val :=
      min_le_min codeSize (Nat.le_refl _)
    exact ⟨smaller.trans body, locals, (Nat.mul_le_mul_left 500 smaller).trans operands⟩
  obtain ⟨storage,initialized,_⟩ := WP.spec_imp_exists Itasca.metadata.Env.new.spec
  obtain ⟨scheduler,run,streamCall,tailEq,tailReady,ready,workers⟩ := compiler_streaming_available ops law bound allocation
    runtime.compiler.CompileSource.Insts.ItascaStreamSource {bytes,code_start := codeStart,code_end := codeEnd} 0#u64
    bytes raw regions env tail certificate available (initialScheduler A limits codeStart) storage bodyBytes localCount peak
    (demand.environment_at codeStart) (demand.functions_at codeStart) regionMaxima demand.queueReserve rfl rfl rfl rfl origin
  have functionReserve : scheduler.functions.length ≤ bound := by
    change scheduler.functions.val.length ≤ bound
    rw [ready.slots.length]
    have reserve := demand.mappingReserve
    omega
  obtain ⟨⟨reply,budget,pending⟩,collected,budgetEq,functions,status,order⟩ := WP.spec_imp_exists
    (collect_functions_available ops law bound allocation scheduler.budget scheduler.functions functionReserve (by
      intro index inside
      apply ready.slots.filled index
      rw [←ready.slots.length]
      exact inside))
  dsimp only at budgetEq status order
  subst reply
  have functionCount : functions.length = env.func_type_indices.val.length := by
    have counted := congrArg List.length order
    simp only [List.length_map] at counted
    exact counted.symm.trans ready.slots.length
  have paid : CompilationBudgetEffect (initialScheduler A limits 0#usize).budget budget
      (fun counter => env.func_type_indices.val.length*functionDemandRate bodyBytes localCount counter) := by
    rw [budgetEq]
    exact ready.paid
  obtain ⟨⟨reply,executable,finalBudget⟩,lowered,status,_,_,_⟩ := WP.spec_imp_exists
    (initializer_compilation_available ops law bound allocation (uninitializedModule env tail functions) budget
      (certificate_initializer_typing certificate functions) (demand.initializers functions functionCount budget paid))
  dsimp only at status
  subst reply
  refine ⟨executable,?_⟩
  exact runtime.compiler.compile_with.available eligible.moduleBytes
    ⟨codeStart, codeEnd, storage, env, scheduler, tail, functions, pending, budget, finalBudget,
      regionCall, initialized, streamCall, tailReady, collected, lowered⟩

end Itasca.Compiler

end

end
