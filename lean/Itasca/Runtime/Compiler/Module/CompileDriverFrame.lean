import Itasca.Runtime.Compiler.Local.Initializer.SegmentEmissionContracts
import Itasca.Runtime.Compiler.Local.Initializer.ElementContracts
import Itasca.Runtime.Compiler.Local.Initializer.ModuleLoopContracts
import Itasca.Runtime.Compiler.Local.Initializer.ElementLoopContracts
import Itasca.Runtime.Compiler.Local.Initializer.ElementValueContracts
import Itasca.Runtime.Compiler.Local.Initializer.DataOffsetContracts
import Itasca.Runtime.Compiler.Local.Initializer.ConstantContracts
import Itasca.Runtime.Compiler.Module.InitializerGlobalsAvailable
import Itasca.Runtime.Compiler.Local.Initializer.InitializerElementAppend
import Itasca.Runtime.Compiler.Module.InitializerTotal
import Itasca.Runtime.Compiler.Local.Initializer.InitializerExpressionAvailable
import Itasca.Runtime.Compiler.Local.Relations.Segments.SegmentData
import Itasca.Runtime.Compiler.Module.CodeRegionComplete
import Itasca.Runtime.Compiler.Local.Relations.Function.CoreFunctionContext
import Itasca.Stream.Header
import Itasca.Runtime.Compiler.Local.Initializer

/-!
Sections, each formerly its own module: InitializerDataAvailable, InitializerElementsAvailable, InitializerOffsetAvailable, CompileDriverFrame.
-/

/-! ## InitializerDataAvailable -/

section

/-!
Successful data initializer compilation from independently bounded source offsets and allocator availability.
-/

/-! ## Initializer Data Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Active offsets compile from independent constant-expression typing;
passive data needs only its mapping append. Both paths accept from conservative
source-independent reserve and two-instruction headroom bounds. -/
theorem initializer_data_offset_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A) (index : Usize)
    (inside : index.val < module.module.tail.data.val.length)
    (typed : ∀ segment ∈ module.module.tail.data.val, ∀ memory offset,
      segment.mode = .Active memory offset → Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (instructions : budget.instructions.val + 2 ≤ budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound) (reserve : initializerSize module + 2 ≤ bound)
    (capacity : initializerSize module + 2 ≤ Usize.max) :
    runtime.compiler.initialize.lower_data_offset ops module budget index ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.instructions.val ≤ budget.instructions.val + 2 ∧
      out.2.2.limits = budget.limits ∧ out.2.1.module = module.module ∧
      initializerSize out.2.1 ≤ initializerSize module + 2 ⦄ := by
  let segment := module.module.tail.data.val[index.val]'inside
  have found : module.module.tail.data.val[index.val]? = some segment := List.getElem?_eq_getElem inside
  have scalar : ∀ memory offset, segment.mode = .Active memory offset → ∀ lo hi, offset ≠ .V128 lo hi := by
    intros memory offset mode lo hi matching
    have valid := typed segment (List.getElem_mem inside) memory offset mode
    rw [matching] at valid
    cases valid
  apply WP.spec_mono (runtime.compiler.initialize.lower_data_offset.available ops bound available module budget index segment found
    scalar instructions codeRequest
    (by simp only [initializerSize, alloc.vec.Vec.length] at reserve ⊢; omega)
    (by simp only [initializerSize, alloc.vec.Vec.length] at capacity ⊢; omega)
    (by simp only [initializerSize, alloc.vec.Vec.length] at reserve ⊢; omega)
    (by simp only [initializerSize, alloc.vec.Vec.length] at capacity ⊢; omega))
  rintro ⟨status, after, afterBudget⟩ ⟨accepted, count, limits, frame, functions, offsets⟩
  have moduleEq := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) frame
  refine ⟨accepted, count, limits, moduleEq, ?_⟩
  rw [frame]
  simp only [initializerSize]
  omega

end Itasca.Runtime.Compiler

end

/-! ## Initializer Data Offsets Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Every remaining independently typed data offset is accepted by the actual
initializer loop. The demand is computed from the source data count, not
from an assumed accepted compilation or emitted-code certificate. -/
theorem initializer_data_offsets_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A) (index : Usize)
    (inside : index.val ≤ module.module.tail.data.val.length)
    (typed : ∀ segment ∈ module.module.tail.data.val, ∀ memory offset,
      segment.mode = .Active memory offset → Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (instructions : budget.instructions.val + 2*(module.module.tail.data.val.length-index.val) ≤
      budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound)
    (reserve : initializerSize module + 2*(module.module.tail.data.val.length-index.val) ≤ bound)
    (capacity : initializerSize module + 2*(module.module.tail.data.val.length-index.val) ≤ Usize.max) :
    runtime.compiler.initialize.lower_loop2 ops module budget index (.Ok ()) ⦃ out =>
      out.2.2 = .Ok () ∧ out.1.module = module.module ∧
      initializerSize out.1 ≤ initializerSize module + 2*(module.module.tail.data.val.length-index.val) ∧
      out.2.1.instructions.val ≤ budget.instructions.val + 2*(module.module.tail.data.val.length-index.val) ∧
      out.2.1.limits = budget.limits ⦄ := by
  let P := fun current (charged : runtime.compiler.Budget A) (cursor : Usize) =>
    charged.limits = budget.limits ∧
    initializerSize current + 2 * (module.module.tail.data.val.length - cursor.val) ≤
      initializerSize module + 2 * (module.module.tail.data.val.length - index.val) ∧
    charged.instructions.val + 2 * (module.module.tail.data.val.length - cursor.val) ≤
      budget.instructions.val + 2 * (module.module.tail.data.val.length - index.val)
  change WP.spec (loop (initializerDataOffsetLoop ops).body (module, budget, index, .Ok ())) _
  apply InitializerModuleLoop.available
    { rules := initializerDataOffsetLoop ops, before := module, budget := budget, j := index,
      length := alloc.vec.Vec.len module.module.tail.data, lengthEq := rfl, bounded := inside, P := P,
      Q := (fun after afterBudget => after.module = module.module ∧
      initializerSize after ≤ initializerSize module + 2*(module.module.tail.data.val.length-index.val) ∧
      afterBudget.instructions.val ≤ budget.instructions.val + 2*(module.module.tail.data.val.length-index.val) ∧
      afterBudget.limits = budget.limits), advance := ?_, finish := ?_, initial := ?_ }
  · intro current charged cursor source position prior
    obtain ⟨limits, size, used⟩ := prior
    change cursor.val < module.module.tail.data.val.length at position
    have currentBound : cursor.val < current.module.tail.data.val.length := by
      simpa only [source] using position
    apply WP.spec_mono (initializer_data_offset_available ops bound available current charged cursor currentBound
      (by simpa only [source] using typed) (by rw [limits]; omega) codeRequest (by omega) (by omega))
    rintro ⟨result, next, nextBudget⟩ ⟨accepted, usedAgain, limitsAgain, sourceAgain, sizeAgain⟩
    dsimp only at accepted usedAgain limitsAgain sourceAgain sizeAgain
    refine ⟨accepted, ?_⟩
    intro nextIndex increment
    exact ⟨limitsAgain.trans limits, by omega, by omega⟩
  · intro current charged cursor source last prior
    obtain ⟨limits, size, used⟩ := prior
    change cursor.val = module.module.tail.data.val.length at last
    exact ⟨source, by omega, by omega, limits⟩
  · exact ⟨rfl, by omega, by omega⟩

end Itasca.Runtime.Compiler

end

end

/-! ## InitializerElementsAvailable -/

section

/-!
Availability of individual element initializers and their complete element-segment fold.
-/

/-! ## Initializer Element Value Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

end Itasca.Runtime.Compiler

end

/-! ## Initializer Element Values Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

end Itasca.Runtime.Compiler

end

/-! ## Initializer Element Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- One complete element mapping is accepted from source typing and independently
bounded retained and scratch demand, including its optional active offset. -/
theorem initializer_element_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (index : Usize) (segment : Itasca.metadata.Element)
    (lookup : module.module.env.elements.val[index.val]? = some segment)
    (typed : ∀ expr ∈ segment.init.val, Itasca.ModuleConstants.Valid module.module.env expr
      (Itasca.ModuleConstants.referenceValueType segment.elem))
    (offsetTyped : ∀ table offset, segment.mode = .Active table offset →
      Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (instructions : budget.instructions.val + 2*segment.init.length + 2 ≤ budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound) (reserve : initializerSize module + segment.init.length + 3 ≤ bound)
    (capacity : initializerSize module + segment.init.length + 3 ≤ Usize.max) :
    runtime.compiler.initialize.lower_element ops module budget index ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.instructions.val ≤ budget.instructions.val + 2*segment.init.length + 2 ∧
      out.2.2.limits = budget.limits ∧ out.2.1.module = module.module ∧
      initializerSize out.2.1 ≤ initializerSize module + segment.init.length + 3 ⦄ := by
  exact runtime.compiler.initialize.lower_element.available ops bound available module budget index segment
    ⟨lookup, typed, offsetTyped, instructions, codeRequest, reserve, capacity⟩

end Itasca.Runtime.Compiler

end

/-! ## Initializer Elements Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- The complete element-mapping loop accepts from source typing and a demand
computed by summing source initializer counts plus three entries per segment.
Temporary element-index vectors are bounded by this same independent demand. -/
theorem initializer_elements_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A) (index : Usize)
    (inside : index.val ≤ module.module.env.elements.val.length)
    (typed : ∀ segment ∈ module.module.env.elements.val, ∀ expr ∈ segment.init.val,
      Itasca.ModuleConstants.Valid module.module.env expr (Itasca.ModuleConstants.referenceValueType segment.elem))
    (offsetTyped : ∀ segment ∈ module.module.env.elements.val, ∀ table offset,
      segment.mode = .Active table offset → Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (instructions : budget.instructions.val + 2*initializerElementCost (module.module.env.elements.val.drop index.val) ≤
      budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound)
    (reserve : initializerSize module + initializerElementCost (module.module.env.elements.val.drop index.val) ≤ bound)
    (capacity : initializerSize module + initializerElementCost (module.module.env.elements.val.drop index.val) ≤ Usize.max) :
    runtime.compiler.initialize.lower_loop1 ops module budget index (.Ok ()) ⦃ out =>
      out.2.2 = .Ok () ∧ out.1.module = module.module ∧ out.2.1.limits = budget.limits ∧
      initializerSize out.1 ≤ initializerSize module + initializerElementCost (module.module.env.elements.val.drop index.val) ∧
      out.2.1.instructions.val ≤ budget.instructions.val +
        2*initializerElementCost (module.module.env.elements.val.drop index.val) ⦄ := by
  let P := fun current (charged : runtime.compiler.Budget A) (cursor : Usize) =>
    charged.limits = budget.limits ∧
    initializerSize current + initializerElementCost (module.module.env.elements.val.drop cursor.val) ≤
      initializerSize module + initializerElementCost (module.module.env.elements.val.drop index.val) ∧
    charged.instructions.val + 2*initializerElementCost (module.module.env.elements.val.drop cursor.val) ≤
      budget.instructions.val + 2*initializerElementCost (module.module.env.elements.val.drop index.val)
  change WP.spec (loop (initializerElementLoop ops).body (module, budget, index, .Ok ())) _
  apply InitializerModuleLoop.available
    { rules := initializerElementLoop ops, before := module, budget := budget, j := index,
      length := alloc.vec.Vec.len module.module.env.elements, lengthEq := rfl, bounded := inside, P := P,
      Q := fun after afterBudget => after.module = module.module ∧ afterBudget.limits = budget.limits ∧
        initializerSize after ≤ initializerSize module + initializerElementCost (module.module.env.elements.val.drop index.val) ∧
        afterBudget.instructions.val ≤ budget.instructions.val + 2*initializerElementCost (module.module.env.elements.val.drop index.val),
      advance := ?_, finish := ?_, initial := ?_ }
  · intro current charged cursor source position prior
    obtain ⟨limits, size, used⟩ := prior
    change cursor.val < module.module.env.elements.val.length at position
    let segment := module.module.env.elements.val[cursor.val]'position
    have found : module.module.env.elements.val[cursor.val]? = some segment := List.getElem?_eq_getElem position
    have member := List.getElem_mem position
    have cost := initializer_element_cost_step _ _ _ found
    have initLength : segment.init.length = segment.init.val.length := rfl
    apply WP.spec_mono (runtime.compiler.initialize.lower_element.available ops bound available current charged cursor segment
      ⟨by simpa only [source] using found, by simpa only [source] using typed segment member,
        by simpa only [source] using offsetTyped segment member,
        by rw [limits]; omega, codeRequest, by omega, by omega⟩)
    rintro ⟨result, next, nextBudget⟩ ⟨accepted, usedAgain, limitsAgain, sourceAgain, sizeAgain⟩
    dsimp only at accepted usedAgain limitsAgain sourceAgain sizeAgain
    refine ⟨accepted, ?_⟩
    intro nextIndex increment
    dsimp only [P]
    rw [increment]
    exact ⟨limitsAgain.trans limits, by omega, by omega⟩
  · intro current charged cursor source last prior
    obtain ⟨limits, size, used⟩ := prior
    change cursor.val = module.module.env.elements.val.length at last
    simp only [last, List.drop_length, initializerElementCost, List.map_nil, List.sum_nil, Nat.mul_zero, Nat.add_zero] at size used
    exact ⟨source, limits, size, used⟩
  · exact ⟨rfl, Nat.le_refl _, Nat.le_refl _⟩

end Itasca.Runtime.Compiler

end

end

/-! ## CompileDriverFrame -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Compiler custom-section callbacks preserve every scheduler predicate. -/
theorem compiler_custom_preserves {A : Type} (ops : runtime.platform.Alloc A)
    (P : runtime.compiler.CompileScheduler A → Prop) :
    ModuleTail.PreservesInvariant
      (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops).metadataModuleVisitorInst P := by
  intro before chunk after accepted prior
  have same : before = after := congrArg Prod.snd (Result.ok_injective accepted)
  simpa only [← same] using prior

/-- Parsing the environment only delivers custom-section notifications, so the
actual compiler scheduler is unchanged before its environment-ready callback. -/
theorem compiler_driver_decoded {A S : Type} (ops : runtime.platform.Alloc A)
    {source : stream.Source S} {id state before after env}
    (run : StreamRun.Accepted source
      (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
      id state before after env) : run.decoded = before := by
  have region : run.region = before := (Result.ok_injective run.region_call).symm
  have decoded := metadata.validate_env_with.accepted_invariant
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops).metadataModuleVisitorInst
    (fun scheduler => scheduler = before) (compiler_custom_preserves ops _) run.environment run.region env
    run.environmentLength run.decoded run.decode_environment region
  exact decoded

/-- Code-end, tail parsing/delivery and final worker retirement preserve the
function array and captured tables produced by submission. -/
theorem compiler_driver_after_submission {A S : Type} (ops : runtime.platform.Alloc A)
    {source : stream.Source S} {id state env environmentLength before after}
    (run : StreamRun.Remaining source
      (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
      id state env environmentLength before after) :
    after = {run.submitted with completed := after.completed, tail := some run.tail} := by
  have ended : run.ended = run.submitted := by
    have same := congrArg Prod.snd (Result.ok_injective run.end_call)
    exact same.symm
  have region : run.region = run.ended := (Result.ok_injective run.region_call).symm
  have decoded := metadata.validate_tail_with.accepted_invariant
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops).metadataModuleVisitorInst
    (fun scheduler => scheduler = run.region) (compiler_custom_preserves ops _) run.tailBytes 0#usize env
    run.region run.tail run.decodedTail run.decode_tail rfl
  have ready : run.ready = {run.decodedTail with tail := some run.tail} := by
    have same := congrArg Prod.snd (Result.ok_injective run.ready_call)
    exact same.symm
  have drained := compiler_drain_frame ops id run.ready after run.pending run.remaining run.drain_call
  simpa only [ready, decoded, region, ended] using drained

/-- Actual environment preparation supplies the exact canonical signature and
parameter tables and the empty source-indexed result array. -/
theorem compiler_driver_configured {A S : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {source : stream.Source S} {id state before after env}
    (run : StreamRun.Accepted source
      (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
      id state before after env)
    (emptyTypes : before.signatures.val = []) (emptySlots : before.func_param_slots.val = [])
    (emptyFunctions : before.functions.val = []) :
    SignatureSequence run.remaining.configured.signatures.val env.types.val ∧
      run.remaining.configured.func_param_slots.val.map (fun word => word.val) =
        env.func_types.val.map (fun ft => signatureSlots ft.params.val) ∧
      run.remaining.configured.functions.val = List.replicate env.func_type_indices.val.length none ∧
      run.remaining.configured.code_start = before.code_start := by
  have decoded := compiler_driver_decoded ops run
  have prepared := compiler_environment_ready_sequence ops law run.decoded env
    (by simpa only [decoded] using emptyTypes) (by simpa only [decoded] using emptySlots)
    (by simpa only [decoded] using emptyFunctions)
  have configured := run.remaining.configured_call
  change runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready ops run.decoded env =
    .ok (.Ok run.remaining.config, run.remaining.configured) at configured
  rw [configured, WP.spec_ok] at prepared
  obtain ⟨signatures, widths, functions⟩ := prepared _ rfl
  have frame := compiler_environment_frame ops run.decoded run.remaining.configured env run.remaining.config
    run.remaining.configured_call
  have origin := congrArg (fun fields => fields.2.2) frame
  exact ⟨signatures, widths, functions, by simpa only [schedulerFrame, decoded] using origin⟩
end Itasca.Runtime.Compiler

end
