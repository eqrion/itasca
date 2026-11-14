import Itasca.Runtime.Compiler.Local.Initializer.ModuleLoopContracts
import Itasca.Runtime.Compiler.Local.Relations.Function.EnvironmentContracts
import Itasca.Runtime.Compiler.Local.Initializer.GlobalContracts
import Itasca.Runtime.Compiler.Local.Relations.Function.SignatureCapture
import Itasca.Runtime.Compiler.Local.Callbacks.CallbackEquations
import Itasca.Runtime.Compiler.Module.CompileTotal
import Itasca.Runtime.Compiler.Local.Capacity.IndependentBodyReplay
import Itasca.Runtime.Compiler.Body.Reader.Acceptance.SourceStepAcceptanceWasm2
import Itasca.Runtime.Compiler.Body.Reader.Source.SourceBudgetAdvance
import Itasca.Runtime.Compiler.Module.PreparedFunctionDemand
import Itasca.Profile.BinaryUnique
import Itasca.Module.Code.Framing
import Itasca.Stream.DriverRegions
import Itasca.Runtime.Compiler.Local.Capacity.BudgetAvailability
import Itasca.Runtime.Compiler.Local.Relations.Function.FunctionEnvironment
import Itasca.Runtime.Compiler.Local.Initializer.InitializerExpressionAvailable
import Itasca.Runtime.Compiler.Module.InitializerTotal
import Itasca.Module.Const.Parser
import Itasca.Runtime.Compiler.Local.Initializer

/-!
Sections, each formerly its own module: PreparedFunctionAvailable, SourceEntryPrepared, EntryAvailable, SourceQueuePolicy, EnvironmentReadyAvailable, InitializerGlobalsAvailable.
-/

/-! ## PreparedFunctionAvailable -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Source-derived conservative total charges for one prepared function. -/
abbrev preparedFunctionAllowance (ctx : code.Context) (length : Nat) : ChargeCounter → Nat
  | .instructions => 3*length
  | .branches => length
  | .controls => 1+length
  | .locals => ctx.locals.val.length

end Itasca.Runtime.Compiler

end

/-! ## SourceEntryPrepared -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Forget visitor observations while retaining the independently decoded
source entry. No compiler result occurs in this record. -/
def preparedOfSourceWitness {V : Type} {visitor : code.OpVisitor V} {data env index start finish before after}
    (w : CodeEntry.Witness visitor data env index start finish before after) :
    CodeEntry.Prepared data env index start where
  finish := finish
  typeIdx := w.typeIdx
  ft := w.ft
  groups := w.groups
  ctx := w.ctx
  content := w.content
  bodyStart := w.bodyStart
  body := w.body
  size := w.size
  index_lt := w.index_lt
  index_type := w.index_type
  type_lt := w.type_lt
  function_type := w.function_type
  header := w.header
  extent := w.extent
  locals_bytes := w.locals_bytes
  locals_bound := w.locals_bound
  context_locals := w.context_locals
  context_results := w.context_results
  body_bytes := w.body_bytes

/-- Independent entry encoding and typing construct prepared source metadata
and body validity, with no compiler visitor or accepted target trace. -/
theorem source_entry_prepared (data : Slice U8) (env : metadata.Env) (index start finish : Usize)
     (entry : ModuleBinary.Code)
    (indexBound : index.val < env.func_type_indices.val.length)
    (typed : Profile.EntryTyped env env.func_type_indices.val[index.val] entry)
    (bounds : CodeEntry.Bounds env)
    (limits : Profile.EnvironmentWithinLimits env)
    (encoded : ModuleBinary.At (Profile.CodeEncodingWithinLimits) data start entry finish) :
    ∃ w : CodeEntry.Prepared data env index start,
      w.finish = finish ∧ Wasm2.Validated w.body env w.ctx.locals w.typeIdx := by
  obtain ⟨⟨reply,after⟩,called,accepted⟩ := WP.spec_imp_exists
    (metadata.validate_code_entry_with.complete_spec_of_body code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      FullVisitor.empty_accepts data start env index entry finish () indexBound typed bounds encoded (by
        intro body ctx typeIdx ft signature results size bodyValid started
        exact code.validate_body_with.profile_complete _ FullVisitor.empty_accepts body env ctx typeIdx started
          limits size bodyValid))
  dsimp only at accepted
  subst reply
  obtain ⟨w⟩ := metadata.validate_code_entry_with.witness_profile code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
    data start env index finish () after bounds called
  refine ⟨preparedOfSourceWitness w,rfl,?_⟩
  exact code.validate_body_with.profile_sound _ w.body env w.ctx w.typeIdx w.startedState after
    w.body_accepted

end Itasca.Runtime.Compiler

end

/-! ## EntryAvailable -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Independent numerical resource eligibility over decoded source entry
metadata. This mentions no target callback, emitted function, or target run. -/
def EntryResourceDemand {A : Type} (budget : runtime.compiler.Budget A)
    (data : Slice U8) (env : metadata.Env) (index start : Usize)
     (bound : Nat) : Prop :=
  ∀ w : CodeEntry.Prepared data env index start,
    PreparedFunctionDemand budget w.ctx w.body.length
      (independentBodyDemand w.body env w.ctx w.typeIdx).operands bound

end Itasca.Runtime.Compiler

end

/-! ## SourceQueuePolicy -/

section

namespace Itasca.Runtime.Compiler.StreamAvailability
open Aeneas Aeneas.Std Itasca

/-- Local acceptance contract at a fixed validated environment and source
cursor. Unlike an unrestricted visitor contract, this permits finite numerical
module budgets and retains actual completed worker identities and finish checks. -/
structure QueuePolicy {V : Type} (visitor : Itasca.stream.StreamingVisitor V)
    (config : Itasca.stream.Config) (env : metadata.Env)
    (Queued : U64 → List StreamBatch.Issued → Nat → V → Prop) : Prop where
  batch_positive : 0 < config.batch_bytes.val
  capacity_positive : 0 < config.max_batches.val
  submit : ∀ id queue cursor issued before,
    Queued id queue cursor before → StreamAcceptingScheduler.Valid issued →
    issued.env = env → issued.module_id = id → issued.first_func.val = cursor →
    queue.length < config.max_batches.val →
    ∃ after, visitor.submit_code_batch before issued.seed = .ok (.Ok (),after) ∧
      Queued id (queue++[issued]) (cursor+issued.num_funcs.val) after
  poll : ∀ id queue cursor before, Queued id queue cursor before → queue ≠ [] →
    ∃ issued rest worker after, (issued::rest).Perm queue ∧
      visitor.poll_code_batch before = .ok (.Ok worker,after) ∧
      StreamBatch.Identity issued worker ∧ Itasca.stream.CodeBatch.finish worker = .ok (.Ok ()) ∧
      Queued id rest cursor after

/-- A real queued worker retires successfully. Its finish proof comes from
concrete compilation; dispatch cursors need not match an empty visitor run. -/
theorem retire_complete {V : Type} (visitor : Itasca.stream.StreamingVisitor V)
    (config : Itasca.stream.Config) (env : metadata.Env)
    (Queued : U64 → List StreamBatch.Issued → Nat → V → Prop)
    (policy : QueuePolicy visitor config env Queued)
    (id : U64) (queue : List StreamBatch.Issued) (cursor : Nat) (before : V)
    (pending : alloc.vec.Vec Usize) (held : Queued id queue cursor before)
    (valid : StreamAcceptingScheduler.ValidQueue id queue)
    (ids : pending.val.Perm (queue.map StreamBatch.Issued.batch_id)) (nonempty : pending.val ≠ []) :
    ∃ after remaining rest,
      Itasca.stream.retire_code_batch visitor id before pending = .ok (.Ok (),after,remaining) ∧
      Queued id rest cursor after ∧ StreamAcceptingScheduler.ValidQueue id rest ∧
      remaining.val.Perm (rest.map StreamBatch.Issued.batch_id) ∧ remaining.length+1 = pending.length := by
  have queued : queue ≠ [] := by
    intro empty
    have length := ids.length_eq
    simp only [empty,List.map_nil,List.length_nil] at length
    exact nonempty (by simpa using length)
  obtain ⟨issued,rest,worker,after,permutation,polled,identity,finished,retained⟩ := policy.poll id queue cursor before held queued
  have member : issued ∈ queue := permutation.mem_iff.mp (by simp)
  obtain ⟨moduleId,_⟩ := valid issued member
  have pendingIds : (issued.batch_id::rest.map StreamBatch.Issued.batch_id).Perm pending.val :=
    (permutation.map StreamBatch.Issued.batch_id).trans ids.symm
  obtain ⟨remaining,retired,removed⟩ := Itasca.stream.retire_code_batch.complete visitor id before after pending worker polled
    (identity.1.trans moduleId) (by rw [identity.2.1]; exact pendingIds.mem_iff.mp (by simp)) finished
  refine ⟨after,remaining,rest,retired,retained,?_,?_,?_⟩
  · intro old member
    exact valid old (permutation.mem_iff.mp (by simp [member]))
  · rw [identity.2.1] at removed
    exact List.Perm.cons_inv (removed.trans pendingIds.symm)
  · have length := removed.length_eq
    simpa only [List.length_cons] using length

/-- Draining the actual completed-worker queue preserves the source cursor and
terminates with every pending worker retired. -/
theorem drain_complete {V : Type} (visitor : Itasca.stream.StreamingVisitor V)
    (config : Itasca.stream.Config) (env : metadata.Env)
    (Queued : U64 → List StreamBatch.Issued → Nat → V → Prop)
    (policy : QueuePolicy visitor config env Queued)
    (id : U64) (queue : List StreamBatch.Issued) (cursor : Nat) (before : V)
    (pending : alloc.vec.Vec Usize) (held : Queued id queue cursor before)
    (valid : StreamAcceptingScheduler.ValidQueue id queue)
    (ids : pending.val.Perm (queue.map StreamBatch.Issued.batch_id)) :
    ∃ after remaining,
      Itasca.stream.retire_all_code_batches visitor id before pending = .ok (.Ok (),after,remaining) ∧
      remaining.val = [] ∧ Queued id [] cursor after := by
  generalize count : pending.val.length = n
  induction n using Nat.strong_induction_on generalizing queue before pending with
  | h n ih =>
    by_cases empty : pending.val = []
    · have queueEmpty : queue = [] := by
        have length := ids.length_eq
        simp only [empty,List.length_nil,List.length_map] at length
        simpa using length.symm
      refine ⟨before,pending,?_,empty,by simpa only [queueEmpty] using held⟩
      rw [Itasca.stream.retire_all_code_batches,Itasca.stream.retire_all_code_batches_loop,loop]
      simp [Itasca.stream.retire_all_code_batches_loop.body,alloc.vec.Vec.is_empty,empty]
    · obtain ⟨middle,remaining,rest,retired,retained,restValid,restIds,length⟩ :=
        retire_complete visitor config env Queued policy id queue cursor before pending held valid ids empty
      change remaining.val.length+1 = pending.val.length at length
      obtain ⟨after,final,continued,finished,result⟩ := ih remaining.val.length (by omega)
        rest middle remaining retained restValid restIds rfl
      refine ⟨after,final,?_,finished,result⟩
      rw [Itasca.stream.retire_all_code_batches,Itasca.stream.retire_all_code_batches_loop,loop]
      have nonempty : pending.val.isEmpty = false := by simpa using empty
      simpa [Itasca.stream.retire_all_code_batches_loop.body,alloc.vec.Vec.is_empty,nonempty,retired,
        core.result.Result.Insts.CoreOpsTry.branch,Itasca.stream.retire_all_code_batches,
        Itasca.stream.retire_all_code_batches_loop] using continued

end Itasca.Runtime.Compiler.StreamAvailability

end

/-! ## EnvironmentReadyAvailable -/

section

/-!
Successful compiler environment capture, from signature and function slots through the completed function vector. EnvironmentDemand bounds the requests needed to reach the ready compiler environment.
-/

/-! ## Signature Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

end Itasca.Runtime.Compiler

end

/-! ## Environment Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

end Itasca.Runtime.Compiler

end

/-! ## Environment Function Slots Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

end Itasca.Runtime.Compiler

end

/-! ## Environment Function Vector Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

end Itasca.Runtime.Compiler

end

/-! ## Environment Ready Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- The actual environment-ready callback accepts from independent source
widths, input limits, and allocation demand. No accepted callback trace is
supplied. All budget counters remain unchanged in this metadata phase. -/
theorem environment_ready_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (scheduler : runtime.compiler.CompileScheduler A) (env : Itasca.metadata.Env)
    (demand : EnvironmentDemand scheduler env bound) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready ops scheduler env
      ⦃ out => out.1 = .Ok ⟨25000#usize,4#usize⟩ ∧ out.2.budget = scheduler.budget ⦄ := by
  exact runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready.available ops bound available scheduler env demand

end Itasca.Runtime.Compiler

end

end

/-! ## InitializerGlobalsAvailable -/

section

/-!
Availability of constant/global initializers and their global-segment fold.
-/

/-! ## Initializer Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- A checked global initializer publishes both its synthetic function and its
mapping under an independent combined-vector demand bound. -/
theorem initializer_global_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A) (index : Usize)
    (inside : index.val < module.module.env.globals.val.length)
    (typed : ∀ global ∈ module.module.env.globals.val,
      Itasca.ModuleConstants.Valid module.module.env global.init global.gtype.valtype)
    (instructions : budget.instructions.val + 2 ≤ budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound) (reserve : initializerSize module + 2 ≤ bound)
    (capacity : initializerSize module + 2 ≤ Usize.max) :
    runtime.compiler.initialize.lower_global ops module budget index ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.instructions.val = budget.instructions.val + 2 ∧
      out.2.2.limits = budget.limits ∧ out.2.1.module = module.module ∧
      initializerSize out.2.1 = initializerSize module + 2 ⦄ := by
  let global := module.module.env.globals.val[index.val]'inside
  have found : module.module.env.globals.val[index.val]? = some global := List.getElem?_eq_getElem inside
  have valid := typed global (List.getElem_mem inside)
  have vector : ∀ lo hi, global.init = .V128 lo hi → global.gtype.valtype = .V128 := by
    intros lo hi matching
    rw [matching] at valid
    generalize valueTypeEq : global.gtype.valtype = valueType at valid ⊢
    cases valid
    rfl
  apply WP.spec_mono (runtime.compiler.initialize.lower_global.available ops bound available module budget index global found
    vector instructions codeRequest
    (by simp only [initializerSize, alloc.vec.Vec.length] at reserve ⊢; omega)
    (by simp only [initializerSize, alloc.vec.Vec.length] at capacity ⊢; omega)
    (by simp only [initializerSize, alloc.vec.Vec.length] at reserve ⊢; omega)
    (by simp only [initializerSize, alloc.vec.Vec.length] at capacity ⊢; omega))
  rintro ⟨status, after, afterBudget⟩ ⟨accepted, count, limits, frame, mapped, function, certified, appended⟩
  have moduleEq := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) frame
  refine ⟨accepted, count, limits, moduleEq, ?_⟩
  rw [frame]
  simp only [initializerSize]
  rw [mapped, appended]
  simp only [List.length_append, List.length_singleton]
  omega

end Itasca.Runtime.Compiler

end

/-! ## Initializer Globals Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Every remaining independently typed global is accepted by the actual
initializer loop. The demand is computed from the source global count, not
from an assumed accepted compilation or emitted-code certificate. -/
theorem initializer_globals_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A) (index : Usize)
    (inside : index.val ≤ module.module.env.globals.val.length)
    (typed : ∀ global ∈ module.module.env.globals.val,
      Itasca.ModuleConstants.Valid module.module.env global.init global.gtype.valtype)
    (instructions : budget.instructions.val + 2*(module.module.env.globals.val.length-index.val) ≤
      budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound)
    (reserve : initializerSize module + 2*(module.module.env.globals.val.length-index.val) ≤ bound)
    (capacity : initializerSize module + 2*(module.module.env.globals.val.length-index.val) ≤ Usize.max) :
    runtime.compiler.initialize.lower_loop0 ops module budget index (.Ok ()) ⦃ out =>
      out.2.2 = .Ok () ∧ out.1.module = module.module ∧
      initializerSize out.1 = initializerSize module + 2*(module.module.env.globals.val.length-index.val) ∧
      out.2.1.instructions.val = budget.instructions.val + 2*(module.module.env.globals.val.length-index.val) ∧
      out.2.1.limits = budget.limits ⦄ := by
  let P := fun current (charged : runtime.compiler.Budget A) (cursor : Usize) =>
    charged.limits = budget.limits ∧
    initializerSize current + 2 * (module.module.env.globals.val.length - cursor.val) =
      initializerSize module + 2 * (module.module.env.globals.val.length - index.val) ∧
    charged.instructions.val + 2 * (module.module.env.globals.val.length - cursor.val) =
      budget.instructions.val + 2 * (module.module.env.globals.val.length - index.val)
  change WP.spec (loop (initializerGlobalLoop ops).body (module, budget, index, .Ok ())) _
  apply InitializerModuleLoop.available
    { rules := initializerGlobalLoop ops, before := module, budget := budget, j := index,
      length := alloc.vec.Vec.len module.module.env.globals, lengthEq := rfl, bounded := inside, P := P,
      Q := (fun after afterBudget => after.module = module.module ∧
      initializerSize after = initializerSize module + 2*(module.module.env.globals.val.length-index.val) ∧
      afterBudget.instructions.val = budget.instructions.val + 2*(module.module.env.globals.val.length-index.val) ∧
      afterBudget.limits = budget.limits), advance := ?_, finish := ?_, initial := ?_ }
  · intro current charged cursor source position prior
    obtain ⟨limits, size, used⟩ := prior
    change cursor.val < module.module.env.globals.val.length at position
    have currentBound : cursor.val < current.module.env.globals.val.length := by
      simpa only [source] using position
    apply WP.spec_mono (initializer_global_available ops bound available current charged cursor currentBound
      (by simpa only [source] using typed) (by rw [limits]; omega) codeRequest (by omega) (by omega))
    rintro ⟨result, next, nextBudget⟩ ⟨accepted, usedAgain, limitsAgain, sourceAgain, sizeAgain⟩
    dsimp only at accepted usedAgain limitsAgain sourceAgain sizeAgain
    refine ⟨accepted, ?_⟩
    intro nextIndex increment
    exact ⟨limitsAgain.trans limits, by omega, by omega⟩
  · intro current charged cursor source last prior
    obtain ⟨limits, size, used⟩ := prior
    change cursor.val = module.module.env.globals.val.length at last
    exact ⟨source, by omega, by omega, limits⟩
  · exact ⟨rfl, by omega, by omega⟩

end Itasca.Runtime.Compiler

end

end
