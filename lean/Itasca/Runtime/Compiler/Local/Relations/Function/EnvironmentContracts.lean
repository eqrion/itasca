import Itasca.Runtime.Compiler.Local.Relations.Function.SignatureCapture

/-! Scheduler environment capture, exact source metadata and bounded allocation. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.ResultFacts

def SignatureSequence (signatures : List runtime.compiler.Signature)
    (types : List Itasca.wasm_types.FuncType) : Prop :=
  List.Forall₂ (fun signature ty => SignatureMatches signature
    (ty.params.val.map Itasca.Translate.valueType) (ty.results.val.map Itasca.Translate.valueType)) signatures types

theorem SignatureSequence.append {signatures types signature ty}
    (before : SignatureSequence signatures types)
    (last : SignatureMatches signature (ty.params.val.map Itasca.Translate.valueType)
      (ty.results.val.map Itasca.Translate.valueType)) :
    SignatureSequence (signatures ++ [signature]) (types ++ [ty]) := by
  induction before with
  | nil => exact .cons last .nil
  | cons head tail ih => exact .cons head ih

def schedulerFrame {A : Type} (scheduler : runtime.compiler.CompileScheduler A) :=
  (scheduler.completed, scheduler.tail, scheduler.code_start)

abbrev EnvironmentCapture (A : Type) :=
  alloc.vec.Vec runtime.compiler.Signature × alloc.vec.Vec U32 × alloc.vec.Vec Itasca.stream.CodeBatch ×
  alloc.vec.Vec (Option runtime.bytecode.CompiledFunction) × Option Itasca.metadata.Tail × Usize ×
  runtime.compiler.Budget A × core.result.Result Unit Itasca.error.Error

def captureState {A : Type} (scheduler : runtime.compiler.CompileScheduler A)
    (status : core.result.Result Unit Itasca.error.Error) : EnvironmentCapture A :=
  (scheduler.signatures,scheduler.func_param_slots,scheduler.completed,scheduler.functions,
    scheduler.tail,scheduler.code_start,scheduler.budget,status)

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

theorem _root_.Itasca.runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0.inv {A : Type} (allocator : runtime.platform.Alloc A)
    (before : runtime.compiler.CompileScheduler A) (env : metadata.Env) (index : Usize)
    (result : core.result.Result Unit error.Error) (output)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0
      allocator before env index result = .ok output) :
    (output.2.2.1, output.2.2.2.2.1, output.2.2.2.2.2.1) = schedulerFrame before := by
  generalize measure : Usize.max - index.val = n
  induction n using Nat.strong_induction_on generalizing before index result with
  | h n ih =>
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0 at accepted
    rw [loop] at accepted
    simp only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0.body, Itasca.metadata.Env.impl.types, bind_ok] at accepted
    split at accepted
    · cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at accepted
        subst output
        rfl
      | Ok acceptedUnit =>
        cases acceptedUnit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, Std.bind_assoc] at accepted
        obtain ⟨⟨nextResult, middle⟩, entry, tail⟩ := bind_ok_inv _ _ _ accepted
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := bind_ok_inv _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by simpa using arithmetic.2.1
        have nextMax := nextIndex.hmax
        have smaller : Usize.max - nextIndex.val < n := by scalar_tac
        have tail' : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0
            allocator middle env nextIndex nextResult = .ok output := by
          simpa only [uncurry_apply_pair, bind_ok,
            runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0,
            runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0.body, Itasca.metadata.Env.impl.types, core.result.Result.is_ok] using tail
        have frame : schedulerFrame middle = schedulerFrame before := by
          unfold schedulerFrame
          rw [runtime.compiler.CompileScheduler.capture_signature.inv allocator before middle env index nextResult entry]
        exact (ih _ smaller middle nextIndex nextResult tail' rfl).trans frame
    · simp only [bind_ok, Result.ok.injEq] at accepted
      subst output
      rfl


theorem _root_.Itasca.runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1.inv {A : Type} (allocator : runtime.platform.Alloc A)
    (before : runtime.compiler.CompileScheduler A) (env : metadata.Env) (index : Usize)
    (result : core.result.Result Unit error.Error) (output)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1
      allocator before env index result = .ok output) :
    (output.2.2.1, output.2.2.2.2.1, output.2.2.2.2.2.1) = schedulerFrame before := by
  generalize measure : Usize.max - index.val = n
  induction n using Nat.strong_induction_on generalizing before index result with
  | h n ih =>
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1 at accepted
    rw [loop] at accepted
    simp only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1.body, Itasca.metadata.Env.impl.func_types, bind_ok] at accepted
    split at accepted
    · cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at accepted
        subst output
        rfl
      | Ok acceptedUnit =>
        cases acceptedUnit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, Std.bind_assoc] at accepted
        obtain ⟨⟨nextResult, middle⟩, entry, tail⟩ := bind_ok_inv _ _ _ accepted
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := bind_ok_inv _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by simpa using arithmetic.2.1
        have nextMax := nextIndex.hmax
        have smaller : Usize.max - nextIndex.val < n := by scalar_tac
        have tail' : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1
            allocator middle env nextIndex nextResult = .ok output := by
          simpa only [uncurry_apply_pair, bind_ok,
            runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1,
            runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1.body, Itasca.metadata.Env.impl.func_types, core.result.Result.is_ok] using tail
        have frame : schedulerFrame middle = schedulerFrame before := by
          unfold schedulerFrame
          rw [runtime.compiler.CompileScheduler.capture_func_slots.inv allocator before middle env index nextResult entry]
        exact (ih _ smaller middle nextIndex nextResult tail' rfl).trans frame
    · simp only [bind_ok, Result.ok.injEq] at accepted
      subst output
      rfl


theorem _root_.Itasca.runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0.total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (scheduler : runtime.compiler.CompileScheduler A)
    (env : Itasca.metadata.Env) (index : Usize) (status : core.result.Result Unit Itasca.error.Error)
    (bound : index.val ≤ env.types.val.length)
    (prefixMatches : status = .Ok () → SignatureSequence scheduler.signatures.val (env.types.val.take index.val)) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0
      ops scheduler env index status ⦃ (signatures, slots, completed, functions, tail, codeStart, budget, reply) =>
      reply = .Ok () → SignatureSequence signatures.val env.types.val ∧
        slots = scheduler.func_param_slots ∧ functions = scheduler.functions ⦄ := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0
  apply loop.spec_decr_nat (fun p => env.types.val.length - p.2.1.val)
    (fun p => p.2.1.val ≤ env.types.val.length ∧
      (p.2.2 = .Ok () → SignatureSequence p.1.signatures.val (env.types.val.take p.2.1.val) ∧
        p.1.func_param_slots = scheduler.func_param_slots ∧ p.1.functions = scheduler.functions))
  · rintro ⟨current, i, result⟩ ⟨hi, certified⟩
    dsimp only at hi certified
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0.body
    simp only [Itasca.metadata.Env.impl.types, bind_ok]
    split
    · rename_i more
      have hb : i.val < env.types.val.length := by simp [alloc.vec.Vec.deref, Slice.len] at more; scalar_tac
      cases result with
      | Err error => simp [core.result.Result.is_ok]
      | Ok unit =>
        cases unit
        obtain ⟨currentMatches, sameSlots, sameFunctions⟩ := certified rfl
        have length := List.Forall₂.length_eq currentMatches
        have capacity := env.types.property
        have fits : current.signatures.val.length < Usize.max := by simp [List.length_take, Nat.min_eq_left hi] at length; omega
        simp only [core.result.Result.is_ok, bind_ok, ite_true]
        step with runtime.compiler.CompileScheduler.capture_signature.total ops law current env i env.types.val[i.val]
          (List.getElem?_eq_getElem hb) fits as ⟨answer, changed, effect⟩
        step as ⟨next, hnext⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        intro accepted
        obtain ⟨signature, budget, changedEq, appended, exactSignature⟩ := effect accepted
        refine ⟨?_, ?_, ?_⟩
        · rw [hnext, ← List.take_concat_get' env.types.val i.val hb, appended]
          exact currentMatches.append exactSignature
        · rw [changedEq]
          exact sameSlots
        · rw [changedEq]
          exact sameFunctions
    · rename_i finished
      have same : i.val = env.types.val.length := by simp [alloc.vec.Vec.deref, Slice.len] at finished; scalar_tac
      simp only [WP.spec_ok]
      intro accepted
      simpa [same] using certified accepted
  · exact ⟨bound, fun accepted => ⟨prefixMatches accepted, rfl, rfl⟩⟩

theorem _root_.Itasca.runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1.total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (scheduler : runtime.compiler.CompileScheduler A)
    (env : Itasca.metadata.Env) (index : Usize) (status : core.result.Result Unit Itasca.error.Error)
    (bound : index.val ≤ env.func_types.val.length)
    (prefixMatches : status = .Ok () → scheduler.func_param_slots.val.map (fun word => word.val) =
      (env.func_types.val.take index.val).map (fun ty => signatureSlots ty.params.val)) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1
      ops scheduler env index status ⦃ (signatures, slots, completed, functions, tail, codeStart, budget, reply) =>
      reply = .Ok () →
        signatures = scheduler.signatures ∧ slots.val.map (fun word => word.val) =
          env.func_types.val.map (fun ty => signatureSlots ty.params.val) ∧
        functions = scheduler.functions ⦄ := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1
  apply loop.spec_decr_nat (fun p => env.func_types.val.length - p.2.1.val)
    (fun p => p.2.1.val ≤ env.func_types.val.length ∧
      (p.2.2 = .Ok () → p.1.signatures = scheduler.signatures ∧
        p.1.func_param_slots.val.map (fun word => word.val) =
          (env.func_types.val.take p.2.1.val).map (fun ty => signatureSlots ty.params.val) ∧
        p.1.functions = scheduler.functions))
  · rintro ⟨current, i, result⟩ ⟨hi, certified⟩
    dsimp only at hi certified
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1.body
    simp only [Itasca.metadata.Env.impl.func_types, bind_ok]
    split
    · rename_i more
      have hb : i.val < env.func_types.val.length := by simp [alloc.vec.Vec.deref, Slice.len] at more; scalar_tac
      cases result with
      | Err error => simp [core.result.Result.is_ok]
      | Ok unit =>
        cases unit
        obtain ⟨signaturesEq, currentMatches, sameFunctions⟩ := certified rfl
        have length := congrArg List.length currentMatches
        have capacity := env.func_types.property
        have fits : current.func_param_slots.val.length < Usize.max := by
          simp only [List.length_map, List.length_take, Nat.min_eq_left hi] at length
          omega
        simp only [core.result.Result.is_ok, bind_ok, ite_true]
        step with runtime.compiler.CompileScheduler.capture_func_slots.total ops law current env i env.func_types.val[i.val]
          (List.getElem?_eq_getElem hb) fits as ⟨answer, changed, effect⟩
        step as ⟨next, hnext⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        intro accepted
        obtain ⟨word, budget, changedEq, appended, exactWidth⟩ := effect accepted
        refine ⟨?_, ?_, ?_⟩
        · rw [changedEq]
          exact signaturesEq
        · rw [hnext, ← List.take_concat_get' env.func_types.val i.val hb, appended]
          simp only [List.map_append, List.map_singleton, currentMatches, exactWidth]
        · rw [changedEq]
          exact sameFunctions
    · rename_i finished
      have same : i.val = env.func_types.val.length := by simp [alloc.vec.Vec.deref, Slice.len] at finished; scalar_tac
      simp only [WP.spec_ok]
      intro accepted
      simpa [same] using certified accepted
  · exact ⟨bound, fun accepted => ⟨rfl, prefixMatches accepted, rfl⟩⟩

theorem _root_.Itasca.runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2.total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (functions : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (env : Itasca.metadata.Env) (index : Usize) (status : core.result.Result Unit Itasca.error.Error)
    (bound : index.val ≤ env.func_type_indices.val.length)
    (initialized : status = .Ok () → functions.val = List.replicate index.val none) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2
      ops functions budget env index status ⦃ (afterFunctions, afterBudget, reply) =>
      reply = .Ok () → afterFunctions.val = List.replicate env.func_type_indices.val.length none ⦄ := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2
  apply loop.spec_decr_nat (fun p => env.func_type_indices.val.length - p.2.2.1.val)
    (fun p => p.2.2.1.val ≤ env.func_type_indices.val.length ∧
      (p.2.2.2 = .Ok () → p.1.val = List.replicate p.2.2.1.val none))
  · rintro ⟨functions, budget, i, result⟩ ⟨hi, filled⟩
    dsimp only at hi filled
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2.body
    simp only [Itasca.metadata.Env.impl.func_type_indices, bind_ok]
    split
    · rename_i more
      have hb : i.val < env.func_type_indices.val.length := by
        simp [alloc.vec.Vec.deref, Slice.len] at more; scalar_tac
      cases result with
      | Err error => simp [core.result.Result.is_ok]
      | Ok unit =>
        cases unit
        have initialized := filled rfl
        have capacity := env.func_type_indices.property
        have fits : functions.val.length < Usize.max := by simp [initialized]; omega
        simp only [core.result.Result.is_ok, bind_ok, ite_true]
        step with budget_push ops law budget functions none fits as ⟨status, nextBudget, nextFunctions, pushed⟩
        rcases pushed with ⟨rfl, rfl, appended⟩ | ⟨rfl, rfl, rejected⟩
        · simp only [runtime.compiler.visitor_result.eq, bind_ok]
          step as ⟨next, hnext⟩
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          intro _
          rw [appended, initialized, hnext, List.replicate_add]
          simp
        · simp only [runtime.compiler.visitor_result.eq, bind_ok]
          step as ⟨next, hnext⟩
          exact ⟨by scalar_tac, by simp, by scalar_tac⟩
    · rename_i finished
      have same : i.val = env.func_type_indices.val.length := by
        simp [alloc.vec.Vec.deref, Slice.len] at finished; scalar_tac
      simp only [WP.spec_ok]
      intro accepted
      simpa [same] using filled accepted
  · exact ⟨bound, initialized⟩

theorem _root_.Itasca.runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0.available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (scheduler : runtime.compiler.CompileScheduler A) (env : Itasca.metadata.Env) (index : Usize)
    (inside : index.val ≤ env.types.val.length)
    (widths : ∀ type ∈ env.types.val,
      signatureSlots type.params.val ≤ U32.max ∧ signatureSlots type.results.val ≤ U32.max)
    (capacity : scheduler.signatures.length + (env.types.val.length-index.val) ≤ Usize.max)
    (request : scheduler.signatures.length + (env.types.val.length-index.val) ≤ bound) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0
      ops scheduler env index (.Ok ()) ⦃ (signatures, slots, completed, functions, tail, codeStart, budget, reply) => ∃ after,
        (signatures, slots, completed, functions, tail, codeStart, budget, reply) = captureState after (.Ok ()) ∧
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
      step with runtime.compiler.CompileScheduler.capture_signature.available ops bound available current env next type lookup params results
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


theorem _root_.Itasca.runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1.available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (scheduler : runtime.compiler.CompileScheduler A) (env : Itasca.metadata.Env) (index : Usize)
    (inside : index.val ≤ env.func_types.val.length)
    (widths : ∀ type ∈ env.func_types.val,
      signatureSlots type.params.val ≤ U32.max)
    (capacity : scheduler.func_param_slots.length + (env.func_types.val.length-index.val) ≤ Usize.max)
    (request : scheduler.func_param_slots.length + (env.func_types.val.length-index.val) ≤ bound) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1
      ops scheduler env index (.Ok ()) ⦃ (signatures, slots, completed, functions, tail, codeStart, budget, reply) => ∃ after,
        (signatures, slots, completed, functions, tail, codeStart, budget, reply) = captureState after (.Ok ()) ∧
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
      step with runtime.compiler.CompileScheduler.capture_func_slots.available ops bound available current env next type lookup params
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


theorem _root_.Itasca.runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2.available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (functions : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (budget : runtime.compiler.Budget A) (env : Itasca.metadata.Env) (index : Usize)
    (inside : index.val ≤ env.func_type_indices.val.length)
    (capacity : functions.length + (env.func_type_indices.val.length-index.val) ≤ Usize.max)
    (request : functions.length + (env.func_type_indices.val.length-index.val) ≤ bound) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2
      ops functions budget env index (.Ok ()) ⦃ (afterFunctions, afterBudget, reply) =>
        reply = .Ok () ∧ afterBudget = budget ∧
        afterFunctions.length = functions.length + (env.func_type_indices.val.length-index.val) ⦄ := by
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
      simp only [runtime.compiler.visitor_result.eq,bind_ok]
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


theorem _root_.Itasca.runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready.inv {A : Type} (allocator : runtime.platform.Alloc A)
    (before after : runtime.compiler.CompileScheduler A) (env : metadata.Env) (config : stream.Config)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready
      allocator before env = .ok (.Ok config, after)) : schedulerFrame after = schedulerFrame before := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready at accepted
  simp only [Itasca.metadata.Env.impl.func_type_indices, bind_ok] at accepted
  split at accepted
  · simp [runtime.compiler.Budget.reject.eq] at accepted
  · simp only [Itasca.metadata.Env.impl.types, bind_ok] at accepted
    split at accepted
    · simp [runtime.compiler.Budget.reject.eq] at accepted
    · obtain ⟨⟨signatures, slots, completed, functions, tail, start, budget, status⟩, loop0, rest⟩ :=
        bind_ok_inv _ _ _ accepted
      have frame0 := runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0.inv allocator before env 0#usize (.Ok ()) _ loop0
      cases status with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | Ok unit =>
        cases unit
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        obtain ⟨⟨signatures1, slots1, completed1, functions1, tail1, start1, budget1, status1⟩, loop1, rest⟩ :=
          bind_ok_inv _ _ _ rest
        have frame1 := runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1.inv allocator
          ⟨signatures, slots, completed, functions, tail, start, budget⟩ env 0#usize (.Ok ()) _ loop1
        cases status1 with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
        | Ok unit =>
          cases unit
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
          obtain ⟨⟨functions2, budget2, status2⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
          cases status2 with
          | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
          | Ok unit =>
            cases unit
            simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
              Result.ok.injEq, Prod.mk.injEq] at rest
            obtain ⟨_, output⟩ := rest
            subst after
            exact frame1.trans frame0

theorem _root_.Itasca.runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready.total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (scheduler : runtime.compiler.CompileScheduler A)
    (env : Itasca.metadata.Env) (emptyTypes : scheduler.signatures.val = [])
    (emptySlots : scheduler.func_param_slots.val = []) (emptyFunctions : scheduler.functions.val = []) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready ops scheduler env ⦃ (reply, after) =>
      ∀ config, reply = .Ok config →
        SignatureSequence after.signatures.val env.types.val ∧
        after.func_param_slots.val.map (fun word => word.val) = env.func_types.val.map (fun ty => signatureSlots ty.params.val) ∧
        after.functions.val = List.replicate env.func_type_indices.val.length none ⦄ := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready
  simp only [Itasca.metadata.Env.impl.func_type_indices, bind_ok]
  split
  · simp [runtime.compiler.Budget.reject.eq]
  · simp only [Itasca.metadata.Env.impl.types, bind_ok]
    split
    · simp [runtime.compiler.Budget.reject.eq]
    · step with runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0.total ops law scheduler env 0#usize (.Ok ())
        (by simp) (by intro _; simp [emptyTypes, SignatureSequence])
        as ⟨signatures, words, completed, functions, tail, codeStart, budget, status, effect⟩
      cases status with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok unit =>
        cases unit
        obtain ⟨sequence, slotsSame, functionsSame⟩ := effect rfl
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair]
        step with runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1.total ops law
          ⟨signatures, words, completed, functions, tail, codeStart, budget⟩ env 0#usize (.Ok ())
          (by simp) (by intro _; simp [slotsSame, emptySlots])
          as ⟨signatures1, words1, completed1, functions1, tail1, codeStart1, budget1, status1, effect1⟩
        cases status1 with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok unit =>
          cases unit
          obtain ⟨sameSignatures, slotsExact, functionsSame1⟩ := effect1 rfl
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair]
          step with runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2.total ops law budget1 functions1 env 0#usize (.Ok ())
            (by simp) (by intro _; simp [functionsSame1, functionsSame, emptyFunctions])
            as ⟨functions2, budget2, status2, effect2⟩
          cases status2 with
          | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok unit =>
            cases unit
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
            intro config accepted
            refine ⟨?_, slotsExact, effect2 rfl⟩
            simpa only [sameSignatures] using sequence


theorem _root_.Itasca.runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready.available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (scheduler : runtime.compiler.CompileScheduler A) (env : Itasca.metadata.Env)
    (demand : EnvironmentDemand scheduler env bound) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready ops scheduler env
      ⦃ (reply, after) => reply = .Ok ⟨25000#usize,4#usize⟩ ∧ after.budget = scheduler.budget ⦄ := by
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
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0.available ops bound available scheduler env 0#usize (by simp)
      demand.signatureWidths (by simpa using demand.signatureCapacity) (by simpa using demand.signatureReserve))
  rcases captured with ⟨firstOutputSignatures, firstOutputSlots, firstOutputCompleted, firstOutputFunctions, firstOutputTail, firstOutputStart, firstOutputBudget, firstOutputStatus⟩
  dsimp only at same
  rw [same] at actual
  rw [actual]
  simp only [captureState,bind_ok,uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch]
  have slots : first.func_param_slots = scheduler.func_param_slots :=
    congrArg (fun value => value.func_param_slots) firstShape
  have firstFunctions : first.functions = scheduler.functions := congrArg (fun value => value.functions) firstShape
  have firstBudget : first.budget = scheduler.budget := congrArg (fun value => value.budget) firstShape
  obtain ⟨captured,actual,second,same,secondShape,secondLength⟩ := WP.spec_imp_exists
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1.available ops bound available first env 0#usize (by simp)
      demand.functionWidths (by simpa [slots] using demand.slotCapacity) (by simpa [slots] using demand.slotReserve))
  rcases captured with ⟨secondOutputSignatures, secondOutputSlots, secondOutputCompleted, secondOutputFunctions, secondOutputTail, secondOutputStart, secondOutputBudget, secondOutputStatus⟩
  dsimp only at same
  rw [same] at actual
  rw [actual]
  simp only [captureState,bind_ok,uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch]
  have secondFunctions : second.functions = scheduler.functions :=
    (congrArg (fun value => value.functions) secondShape).trans firstFunctions
  have secondBudget : second.budget = scheduler.budget :=
    (congrArg (fun value => value.budget) secondShape).trans firstBudget
  step with runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2.available ops bound available second.functions second.budget env 0#usize
    (by simp) (by simpa [secondFunctions] using demand.functionCapacity)
    (by simpa [secondFunctions] using demand.functionReserve)
    as ⟨functions,budget,status,accepted,sameBudget,length⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,WP.spec_ok]
  exact ⟨rfl,by rw [sameBudget,secondBudget]⟩


/-- The function-vector loop's accepted result is the exact replicated source
length established by its total contract. -/
theorem _root_.Itasca.runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2.inv
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (budget : runtime.compiler.Budget A)
    (functions : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (env : Itasca.metadata.Env) (index : Usize) (status : core.result.Result Unit Itasca.error.Error)
    (bound : index.val ≤ env.func_type_indices.val.length)
    (initialized : status = .Ok () → functions.val = List.replicate index.val none)
    {output} (called : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2
      ops functions budget env index status = .ok output) :
    let (afterFunctions, _, reply) := output
    reply = .Ok () → afterFunctions.val = List.replicate env.func_type_indices.val.length none := by
  have effect := runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2.total
    ops law budget functions env index status bound initialized
  rw [called, WP.spec_ok] at effect
  exact effect

end Itasca.Runtime.Compiler
