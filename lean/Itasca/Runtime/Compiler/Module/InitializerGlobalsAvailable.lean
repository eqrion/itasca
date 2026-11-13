import Itasca.Runtime.Compiler.Module.CompileTotal
import Itasca.Runtime.Compiler.Local.Capacity.IndependentBodyReplay
import Itasca.Runtime.Compiler.Body.Reader.Acceptance.SourceStepAcceptanceWasm2
import Itasca.Runtime.Compiler.Body.Reader.Source.SourceBudgetAdvance
import Itasca.Runtime.Compiler.Module.PreparedFunctionDemand
import Itasca.Profile.EntryComplete
import Itasca.Profile.EntrySound
import Itasca.Module.Code.Framing
import Itasca.Stream.SchedulerComplete
import Itasca.Runtime.Compiler.Local.Capacity.BudgetAvailability
import Itasca.Runtime.Compiler.Local.Relations.Function.FunctionEnvironment
import Itasca.Runtime.Compiler.Local.Initializer.InitializerExpressionAvailable
import Itasca.Runtime.Compiler.Module.InitializerTotal
import Itasca.Module.Const.Syntax

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

/-- Independent source signature width excludes the actual accumulator error. -/
theorem type_slots_available (types : Slice Itasca.wasm_types.ValueType)
    (bounded : signatureSlots types.val ≤ U32.max) :
    runtime.compiler.type_slots types ⦃ out =>
      ∃ amount, out = .Ok amount ∧ amount.val = signatureSlots types.val ⦄ := by
  apply WP.spec_mono (compiler_type_slots types)
  intro out counted
  cases out with
  | Ok amount => exact ⟨amount,rfl,counted⟩
  | Err error => omega

/-- Signature capture accepts from independently bounded parameter/result
widths and its actual append demand. -/
theorem capture_signature_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (scheduler : runtime.compiler.CompileScheduler A) (env : Itasca.metadata.Env) (index : Usize)
    (type : Itasca.wasm_types.FuncType) (lookup : env.types.val[index.val]? = some type)
    (parameters : signatureSlots type.params.val ≤ U32.max)
    (results : signatureSlots type.results.val ≤ U32.max)
    (capacity : scheduler.signatures.length < Usize.max)
    (request : scheduler.signatures.length + 1 ≤ bound) :
    runtime.compiler.CompileScheduler.capture_signature ops scheduler env index ⦃ out =>
      out.1 = .Ok () ∧ ∃ signatures signature,
        out.2 = {scheduler with signatures} ∧
        signatures.val = scheduler.signatures.val ++ [signature] ∧
        SignatureMatches signature (type.params.val.map Itasca.Translate.valueType)
          (type.results.val.map Itasca.Translate.valueType) ⦄ := by
  unfold runtime.compiler.CompileScheduler.capture_signature
  simp only [Itasca.metadata.Env.impl.types,bind_ok]
  have inside := (List.getElem?_eq_some_iff.mp lookup).1
  step as ⟨actual,found⟩
  · simpa [alloc.vec.Vec.deref] using inside
  have same : actual = type := by
    simpa [List.getElem?_eq_getElem inside,alloc.vec.Vec.deref,found] using lookup
  rw [same]
  step with type_slots_available type.params.deref (by simpa [alloc.vec.Vec.deref] using parameters) as ⟨status,params,accepted,paramWords⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with type_slots_available type.results.deref (by simpa [alloc.vec.Vec.deref] using results) as ⟨status,returned,accepted,resultWords⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with budget_push_available ops bound available scheduler.budget scheduler.signatures
    ⟨alloc.vec.Vec.len type.params,alloc.vec.Vec.len type.results,params,returned⟩ capacity request
    as ⟨status,budget,signatures,accepted,sameBudget,appended⟩
  rw [accepted]
  simp only [runtime.compiler.visitor_result,bind_ok,WP.spec_ok]
  refine ⟨trivial,signatures,_,?_,appended,?_⟩
  · rw [sameBudget]
  · constructor
    · simp [alloc.vec.Vec.len]
    · simp [alloc.vec.Vec.len]
    · simpa [signatureSlots,alloc.vec.Vec.deref] using paramWords
    · simpa [signatureSlots,alloc.vec.Vec.deref] using resultWords

/-- Function-import/definition parameter capture accepts the same independently
bounded source width and append request. -/
theorem capture_func_slots_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (scheduler : runtime.compiler.CompileScheduler A) (env : Itasca.metadata.Env) (index : Usize)
    (type : Itasca.wasm_types.FuncType) (lookup : env.func_types.val[index.val]? = some type)
    (parameters : signatureSlots type.params.val ≤ U32.max)
    (capacity : scheduler.func_param_slots.length < Usize.max)
    (request : scheduler.func_param_slots.length + 1 ≤ bound) :
    runtime.compiler.CompileScheduler.capture_func_slots ops scheduler env index ⦃ out =>
      out.1 = .Ok () ∧ ∃ slots amount,
        out.2 = {scheduler with func_param_slots := slots} ∧
        slots.val = scheduler.func_param_slots.val ++ [amount] ∧
        amount.val = signatureSlots type.params.val ⦄ := by
  unfold runtime.compiler.CompileScheduler.capture_func_slots
  simp only [Itasca.metadata.Env.impl.func_types,bind_ok]
  have inside := (List.getElem?_eq_some_iff.mp lookup).1
  step as ⟨actual,found⟩
  · simpa [alloc.vec.Vec.deref] using inside
  have same : actual = type := by
    simpa [List.getElem?_eq_getElem inside,alloc.vec.Vec.deref,found] using lookup
  rw [same]
  step with type_slots_available type.params.deref (by simpa [alloc.vec.Vec.deref] using parameters) as ⟨status,amount,accepted,counted⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with budget_push_available ops bound available scheduler.budget scheduler.func_param_slots amount capacity request
    as ⟨status,budget,slots,accepted,sameBudget,appended⟩
  rw [accepted]
  simp only [runtime.compiler.visitor_result,bind_ok,WP.spec_ok]
  exact ⟨trivial,slots,amount,by rw [sameBudget],appended,by simpa [alloc.vec.Vec.deref] using counted⟩

end Itasca.Runtime.Compiler

end

/-! ## Environment Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

abbrev EnvironmentCapture (A : Type) :=
  alloc.vec.Vec runtime.compiler.Signature × alloc.vec.Vec U32 × alloc.vec.Vec Itasca.stream.CodeBatch ×
  alloc.vec.Vec (Option runtime.bytecode.CompiledFunction) × Option Itasca.metadata.Tail × Usize ×
  runtime.compiler.Budget A × core.result.Result Unit Itasca.error.Error

def captureState {A : Type} (scheduler : runtime.compiler.CompileScheduler A)
    (status : core.result.Result Unit Itasca.error.Error) : EnvironmentCapture A :=
  (scheduler.signatures,scheduler.func_param_slots,scheduler.completed,scheduler.functions,
    scheduler.tail,scheduler.code_start,scheduler.budget,status)

/-- The actual type-capture loop accepts independently bounded source signature
widths and reserve demand for its remaining entries. -/
theorem environment_signatures_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (scheduler : runtime.compiler.CompileScheduler A) (env : Itasca.metadata.Env) (index : Usize)
    (inside : index.val ≤ env.types.val.length)
    (widths : ∀ type ∈ env.types.val,
      signatureSlots type.params.val ≤ U32.max ∧ signatureSlots type.results.val ≤ U32.max)
    (capacity : scheduler.signatures.length + (env.types.val.length-index.val) ≤ Usize.max)
    (request : scheduler.signatures.length + (env.types.val.length-index.val) ≤ bound) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0
      ops scheduler env index (.Ok ()) ⦃ out => ∃ after,
        out = captureState after (.Ok ()) ∧
        after = {scheduler with signatures := after.signatures} ∧
        after.signatures.length = scheduler.signatures.length + (env.types.val.length-index.val) ⦄ := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0
  apply loop.spec_decr_nat (fun state => env.types.val.length-state.2.1.val)
    (fun state => state.1 = {scheduler with signatures := state.1.signatures} ∧ state.2.2 = .Ok () ∧
      state.2.1.val ≤ env.types.val.length ∧
      state.1.signatures.length + (env.types.val.length-state.2.1.val) =
        scheduler.signatures.length + (env.types.val.length-index.val))
  · rintro ⟨current,next,status⟩ ⟨same,accepted,position,count⟩
    dsimp only at same accepted position count
    subst status
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0.body
    simp only [Itasca.metadata.Env.impl.types,bind_ok]
    split
    · rename_i more
      have insideType : next.val < env.types.val.length := by
        simpa [UScalar.lt_equiv,alloc.vec.Vec.deref,Slice.len] using more
      let type := env.types.val[next.val]
      have lookup : env.types.val[next.val]? = some type := List.getElem?_eq_getElem insideType
      obtain ⟨params,results⟩ := widths type (List.getElem_mem insideType)
      simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
      step with capture_signature_available ops bound available current env next type lookup params results
        (by omega) (by omega) as ⟨status,middle,accepted,signatures,signature,shape,appended,matched⟩
      subst status middle
      step as ⟨following,followingEq⟩
      refine ⟨?_,?_,?_,?_⟩
      · rw [same]
      · clear same; scalar_tac
      · simp only [alloc.vec.Vec.length,appended,List.length_append,List.length_singleton]
        simp only [alloc.vec.Vec.length] at count
        omega
      · clear same; scalar_tac
    · rename_i stopped
      have last : next.val = env.types.val.length := by
        have ended : env.types.val.length ≤ next.val := by
          simpa [UScalar.lt_equiv,alloc.vec.Vec.deref,Slice.len] using stopped
        omega
      exact WP.spec.ret ⟨current,rfl,same,by simpa [last] using count⟩
  · exact ⟨rfl,rfl,inside,rfl⟩

end Itasca.Runtime.Compiler

end

/-! ## Environment Function Slots Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- The actual function-parameter capture loop accepts independently bounded source parameter
widths and reserve demand for its remaining entries. -/
theorem environment_function_slots_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (scheduler : runtime.compiler.CompileScheduler A) (env : Itasca.metadata.Env) (index : Usize)
    (inside : index.val ≤ env.func_types.val.length)
    (widths : ∀ type ∈ env.func_types.val,
      signatureSlots type.params.val ≤ U32.max)
    (capacity : scheduler.func_param_slots.length + (env.func_types.val.length-index.val) ≤ Usize.max)
    (request : scheduler.func_param_slots.length + (env.func_types.val.length-index.val) ≤ bound) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1
      ops scheduler env index (.Ok ()) ⦃ out => ∃ after,
        out = captureState after (.Ok ()) ∧
        after = {scheduler with func_param_slots := after.func_param_slots} ∧
        after.func_param_slots.length = scheduler.func_param_slots.length + (env.func_types.val.length-index.val) ⦄ := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1
  apply loop.spec_decr_nat (fun state => env.func_types.val.length-state.2.1.val)
    (fun state => state.1 = {scheduler with func_param_slots := state.1.func_param_slots} ∧ state.2.2 = .Ok () ∧
      state.2.1.val ≤ env.func_types.val.length ∧
      state.1.func_param_slots.length + (env.func_types.val.length-state.2.1.val) =
        scheduler.func_param_slots.length + (env.func_types.val.length-index.val))
  · rintro ⟨current,next,status⟩ ⟨same,accepted,position,count⟩
    dsimp only at same accepted position count
    subst status
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1.body
    simp only [Itasca.metadata.Env.impl.func_types,bind_ok]
    split
    · rename_i more
      have insideType : next.val < env.func_types.val.length := by
        simpa [UScalar.lt_equiv,alloc.vec.Vec.deref,Slice.len] using more
      let type := env.func_types.val[next.val]
      have lookup : env.func_types.val[next.val]? = some type := List.getElem?_eq_getElem insideType
      have params := widths type (List.getElem_mem insideType)
      simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
      step with capture_func_slots_available ops bound available current env next type lookup params
        (by omega) (by omega) as ⟨status,middle,accepted,slots,amount,shape,appended,counted⟩
      subst status middle
      step as ⟨following,followingEq⟩
      refine ⟨?_,?_,?_,?_⟩
      · rw [same]
      · clear same; scalar_tac
      · simp only [alloc.vec.Vec.length,appended,List.length_append,List.length_singleton]
        simp only [alloc.vec.Vec.length] at count
        omega
      · clear same; scalar_tac
    · rename_i stopped
      have last : next.val = env.func_types.val.length := by
        have ended : env.func_types.val.length ≤ next.val := by
          simpa [UScalar.lt_equiv,alloc.vec.Vec.deref,Slice.len] using stopped
        omega
      exact WP.spec.ret ⟨current,rfl,same,by simpa [last] using count⟩
  · exact ⟨rfl,rfl,inside,rfl⟩

end Itasca.Runtime.Compiler

end

/-! ## Environment Function Vector Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Allocating the defined-function slots accepts under a reserve bound computed
from the remaining source function declarations. The budget is unchanged. -/
theorem environment_function_vector_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (functions : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (budget : runtime.compiler.Budget A) (env : Itasca.metadata.Env) (index : Usize)
    (inside : index.val ≤ env.func_type_indices.val.length)
    (capacity : functions.length + (env.func_type_indices.val.length-index.val) ≤ Usize.max)
    (request : functions.length + (env.func_type_indices.val.length-index.val) ≤ bound) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2
      ops functions budget env index (.Ok ()) ⦃ out =>
        out.2.2 = .Ok () ∧ out.2.1 = budget ∧
        out.1.length = functions.length + (env.func_type_indices.val.length-index.val) ⦄ := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2
  apply loop.spec_decr_nat (fun state => env.func_type_indices.val.length-state.2.2.1.val)
    (fun state => state.2.1 = budget ∧ state.2.2.2 = .Ok () ∧
      state.2.2.1.val ≤ env.func_type_indices.val.length ∧
      state.1.length + (env.func_type_indices.val.length-state.2.2.1.val) =
        functions.length + (env.func_type_indices.val.length-index.val))
  · rintro ⟨current,charged,next,status⟩ ⟨same,accepted,position,count⟩
    dsimp only at same accepted position count
    subst charged status
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2.body
    simp only [Itasca.metadata.Env.impl.func_type_indices,bind_ok]
    split
    · rename_i more
      have inbounds : next.val < env.func_type_indices.val.length := by
        simpa [UScalar.lt_equiv,alloc.vec.Vec.deref,Slice.len] using more
      simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
      step with budget_push_available ops bound available budget current none (by change current.length < Usize.max; omega)
        (by change current.length + 1 ≤ bound; omega)
        as ⟨status,charged,after,accepted,same,appended⟩
      subst status charged
      simp only [runtime.compiler.visitor_result,bind_ok]
      step as ⟨following,followingEq⟩
      refine ⟨?_,?_,?_⟩
      · scalar_tac
      · simp only [alloc.vec.Vec.length,appended,List.length_append,List.length_singleton]
        simp only [alloc.vec.Vec.length] at count
        omega
      · scalar_tac
    · rename_i stopped
      have last : next.val = env.func_type_indices.val.length := by
        have ended : env.func_type_indices.val.length ≤ next.val := by
          simpa [UScalar.lt_equiv,alloc.vec.Vec.deref,Slice.len] using stopped
        omega
      exact WP.spec.ret ⟨rfl,rfl,by simpa [last] using count⟩
  · exact ⟨rfl,rfl,inside,rfl⟩

end Itasca.Runtime.Compiler

end

/-! ## Environment Ready Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Independent numerical eligibility of the compiler's environment phase. -/
structure EnvironmentDemand {A : Type} (scheduler : runtime.compiler.CompileScheduler A)
    (env : Itasca.metadata.Env) (bound : Nat) : Prop where
  functionLimit : env.func_type_indices.length ≤ scheduler.budget.limits.max_functions.val
  typeLimit : env.types.length ≤ scheduler.budget.limits.max_types.val
  signatureWidths : ∀ type ∈ env.types.val,
    signatureSlots type.params.val ≤ U32.max ∧ signatureSlots type.results.val ≤ U32.max
  functionWidths : ∀ type ∈ env.func_types.val, signatureSlots type.params.val ≤ U32.max
  signatureCapacity : scheduler.signatures.length + env.types.length ≤ Usize.max
  signatureReserve : scheduler.signatures.length + env.types.length ≤ bound
  slotCapacity : scheduler.func_param_slots.length + env.func_types.length ≤ Usize.max
  slotReserve : scheduler.func_param_slots.length + env.func_types.length ≤ bound
  functionCapacity : scheduler.functions.length + env.func_type_indices.length ≤ Usize.max
  functionReserve : scheduler.functions.length + env.func_type_indices.length ≤ bound

/-- The actual environment-ready callback accepts from independent source
widths, input limits, and allocation demand. No accepted callback trace is
supplied. All budget counters remain unchanged in this metadata phase. -/
theorem environment_ready_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (scheduler : runtime.compiler.CompileScheduler A) (env : Itasca.metadata.Env)
    (demand : EnvironmentDemand scheduler env bound) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready ops scheduler env
      ⦃ out => out.1 = .Ok ⟨25000#usize,4#usize⟩ ∧ out.2.budget = scheduler.budget ⦄ := by
  have functions : ¬ Slice.len (alloc.vec.Vec.deref env.func_type_indices) > scheduler.budget.limits.max_functions := by
    have limit := demand.functionLimit
    simp [Slice.len,alloc.vec.Vec.deref,alloc.vec.Vec.length] at *
    scalar_tac
  have types : ¬ Slice.len (alloc.vec.Vec.deref env.types) > scheduler.budget.limits.max_types := by
    have limit := demand.typeLimit
    simp [Slice.len,alloc.vec.Vec.deref,alloc.vec.Vec.length] at *
    scalar_tac
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready
  simp only [Itasca.metadata.Env.impl.func_type_indices,Itasca.metadata.Env.impl.types,bind_ok,if_neg functions,if_neg types]
  obtain ⟨captured,actual,first,same,firstShape,firstLength⟩ := WP.spec_imp_exists
    (environment_signatures_available ops bound available scheduler env 0#usize (by simp)
      demand.signatureWidths (by simpa using demand.signatureCapacity) (by simpa using demand.signatureReserve))
  rw [same] at actual
  rw [actual]
  simp only [captureState,bind_ok,uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch]
  have slots : first.func_param_slots = scheduler.func_param_slots :=
    congrArg (fun value => value.func_param_slots) firstShape
  have firstFunctions : first.functions = scheduler.functions := congrArg (fun value => value.functions) firstShape
  have firstBudget : first.budget = scheduler.budget := congrArg (fun value => value.budget) firstShape
  obtain ⟨captured,actual,second,same,secondShape,secondLength⟩ := WP.spec_imp_exists
    (environment_function_slots_available ops bound available first env 0#usize (by simp)
      demand.functionWidths (by simpa [slots] using demand.slotCapacity) (by simpa [slots] using demand.slotReserve))
  rw [same] at actual
  rw [actual]
  simp only [captureState,bind_ok,uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch]
  have secondFunctions : second.functions = scheduler.functions :=
    (congrArg (fun value => value.functions) secondShape).trans firstFunctions
  have secondBudget : second.budget = scheduler.budget :=
    (congrArg (fun value => value.budget) secondShape).trans firstBudget
  step with environment_function_vector_available ops bound available second.functions second.budget env 0#usize
    (by simp) (by simpa [secondFunctions] using demand.functionCapacity)
    (by simpa [secondFunctions] using demand.functionReserve)
    as ⟨functions,budget,status,accepted,sameBudget,length⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,WP.spec_ok]
  exact ⟨trivial,by rw [sameBudget,secondBudget]⟩

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

/-- Independent constant-expression typing supplies the vector-width condition
needed by the actual initializer compiler. -/
theorem initializer_source_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType)
    (typed : Itasca.ModuleConstants.Valid module.module.env expr ty)
    (instructions : budget.instructions.val + 2 ≤ budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound) (functionsRequest : module.functions.length + 1 ≤ bound)
    (functionsFit : module.functions.length < Usize.max) :
    runtime.compiler.initialize.expression ops module budget expr ty ⦃ out =>
      out.1 = .Ok (alloc.vec.Vec.len module.functions) ∧
      out.2.2.instructions.val = budget.instructions.val + 2 ∧
      out.2.2.limits = budget.limits ∧
      ∃ function, InitializerCode function expr ty ∧
        out.2.1.functions.val = module.functions.val ++ [function] ∧
        out.2.1 = {module with functions := out.2.1.functions} ⦄ := by
  apply initializer_expression_available ops bound available module budget expr ty _ instructions
    codeRequest functionsRequest functionsFit
  intro lo hi same
  subst expr
  cases typed
  rfl

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
  unfold runtime.compiler.initialize.lower_global
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.metadata.Module.impl.env,Itasca.metadata.Env.impl.globals,bind_ok]
  step as ⟨global,found⟩
  · simpa [alloc.vec.Vec.deref] using inside
  have valid := typed global (by rw [found]; simpa [alloc.vec.Vec.deref] using List.getElem_mem inside)
  step with initializer_source_available ops bound available module budget global.init global.gtype.valtype valid
    instructions codeRequest (by simp only [initializerSize,alloc.vec.Vec.length] at reserve ⊢; omega)
    (by simp only [initializerSize,alloc.vec.Vec.length] at capacity ⊢; omega)
    as ⟨status,middle,charged,accepted,used,limits,function,shape,appended,same⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  have inits : middle.global_initializers = module.global_initializers := by rw [same]
  step with budget_push_available ops bound available charged middle.global_initializers _
    (by rw [inits]; simp only [initializerSize,alloc.vec.Vec.length] at capacity ⊢; omega)
    (by rw [inits]; simp only [initializerSize,alloc.vec.Vec.length] at reserve ⊢; omega)
    as ⟨status,afterBudget,initializers,accepted,sameBudget,mapped⟩
  refine ⟨accepted,?_,?_,?_,?_⟩
  · simpa [sameBudget] using used
  · simpa [sameBudget] using limits
  · change middle.module = module.module
    exact congrArg (fun value => value.module) same
  · rw [same] at mapped ⊢
    simp only [initializerSize] at *
    rw [mapped,appended]
    simp only [List.length_append,List.length_singleton]
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
  unfold runtime.compiler.initialize.lower_loop0
  apply loop.spec_decr_nat (fun state => module.module.env.globals.val.length-state.2.2.1.val)
    (fun state => state.1.module = module.module ∧ state.2.1.limits = budget.limits ∧
      state.2.2.2 = .Ok () ∧ state.2.2.1.val ≤ module.module.env.globals.val.length ∧
      initializerSize state.1 + 2*(module.module.env.globals.val.length-state.2.2.1.val) =
        initializerSize module + 2*(module.module.env.globals.val.length-index.val) ∧
      state.2.1.instructions.val + 2*(module.module.env.globals.val.length-state.2.2.1.val) =
        budget.instructions.val + 2*(module.module.env.globals.val.length-index.val))
  · rintro ⟨current,charged,next,status⟩ ⟨same,limits,accepted,position,size,used⟩
    dsimp only at same limits accepted position size used
    subst status
    unfold runtime.compiler.initialize.lower_loop0.body
    simp only [runtime.compiler.ExecutableModule.env,
      Itasca.metadata.Module.impl.env,Itasca.metadata.Env.impl.globals,bind_ok]
    split
    · rename_i more
      have currentBound : next.val < current.module.env.globals.val.length := by
        simpa [UScalar.lt_equiv,alloc.vec.Vec.len,alloc.vec.Vec.deref,Slice.len] using more
      have sourceBound : next.val < module.module.env.globals.val.length := by simpa [same] using currentBound
      simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
      step with initializer_global_available ops bound available current charged next currentBound
        (by simpa [same] using typed) (by rw [limits]; omega) codeRequest (by omega) (by omega)
        as ⟨status,middle,afterBudget,accepted,usedAgain,limitsAgain,sameAgain,sizeAgain⟩
      subst status
      step as ⟨following,followingEq⟩
      refine ⟨?_,?_,?_,?_,?_,?_⟩
      · exact sameAgain.trans same
      · exact limitsAgain.trans limits
      · scalar_tac
      · omega
      · omega
      · scalar_tac
    · rename_i stopped
      have last : next.val = module.module.env.globals.val.length := by
        have endBound : current.module.env.globals.val.length ≤ next.val := by
          simpa [UScalar.lt_equiv,alloc.vec.Vec.len,alloc.vec.Vec.deref,Slice.len] using stopped
        rw [same] at endBound
        omega
      simp only [WP.spec_ok]
      exact ⟨trivial,same,by simpa [last] using size,by simpa [last] using used,limits⟩
  · exact ⟨rfl,rfl,rfl,inside,rfl,rfl⟩

end Itasca.Runtime.Compiler

end

end
