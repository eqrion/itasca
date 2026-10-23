import Exec.Theorems.Composition.Supported.ChosenSupportedMeasure
import Exec.Theorems.Composition.Supported.SupportedChosenHeadHostDispatch
import Exec.Interp.Relations.ErasedChosen
import Exec.Theorems.Composition.Supported.SupportedBranchTableChosenExecution
import Exec.Contracts
import Exec.Theorems.Composition.Supported.SupportedScalarChosenExecution
import Exec.Theorems.Composition.Supported.SupportedStatefulChosenExecution
import Exec.Theorems.Composition.Supported.SupportedIndirectChosenExecution
import Exec.Code.Local.Relations.Common.ScalarEmission
import Exec.Code.Local.Control.Common.Structured
import Exec.Code.Local.Control.Common.StructuredComposition
import Exec.Code.Local.Control.Common.StructuredLabels
import Exec.Interp.Control.StructuredPoint
import Exec.Abs.ModuleBindingsExtension
import Exec.Interp.Relations.SuspendedPoint
import Exec.Interp.Relations.FrameStoreMetadata
import Exec.Interp.Machines.Slice.SliceExecution
import Exec.Abs.Core.Typing
import Exec.Abs.Core
import Exec.Abs.Ownership.Core
import Exec.Interp.Core.Mutation
import Exec.Interp.Relations.SourceCallCause
import Exec.Interp.State.GlobalMutationStep
import Exec.Interp.Control.PendingJump
import Exec.Interp.StructuredMachine.SupportedHeadCoverage
import Exec.Interp.Relations.ReferenceTransfers
import Exec.Interp.Relations.SourceClosure
import Exec.Interp.Core.Linear
import Exec.Interp.Relations.PrefixDispatch
import Exec.Abs.Core.Correct
import Exec.Interp.Relations.ControlPoint
import Exec.Interp.Numeric.Integer.NumericFetch
import Exec.Interp.Numeric.Integer.NumericCodePoint
import Exec.Abs.Numeric.TransitionSimulation
import Exec.Abs.Core.Bound
import Exec.Code.Local.Control.Table.StructuredCodeTableExclusion
import Exec.Interp.StructuredMachine.Execution
import Exec.Interp.StructuredMachine.OrdinaryExecution
import Exec.Interp.StructuredMachine.OrdinaryStack
import Exec.Interp.StructuredMachine.StackPreservation
import Exec.Interp.Relations.StackPreservation
import Exec.Interp.Relations.PrefixEffect
import Exec.Interp.Control.SkipStack
import Exec.Abs.Core.Step
import Exec.Abs.Numeric.Effect
import Exec.Abs.StepSafety
import Exec.Abs.Core.Pure
import Exec.Spec.Extend
import Exec.Interp.Core.OwnershipClosure
import Exec.Interp.Core.LocalInversion
import Exec.Interp.Relations.LocalCodePoint
import Exec.Interp.Relations.Fetch
import Exec.Interp.Relations.ValueLookup
import Exec.Interp.Relations.LocalCapacity
import Exec.Interp.Relations.Capacity
import Exec.Interp.Core.LocalPrefix
import Exec.Interp.Machines.Core.CoreOwnership
import Exec.Interp.Core.BoundClosure
import Exec.Abs.Numeric.Decode
import Exec.Interp.Control.BranchNoCopy
import Exec.Interp.Control.BranchConditionStep
import Exec.Interp.Relations.TypedOperands
import Exec.Interp.Relations.ControlEntry
import Exec.Interp.Control.LoopHead
import Exec.Interp.Machines.Core.CoreIntegerConstantPoint
import Exec.Interp.Machines.Core.CoreIntegerConstantSlots
import Exec.Interp.Machines.Slice.SliceOpcode
import Exec.Interp.State.GlobalCoreStep
import Exec.Interp.State.GlobalCoreOperands
import Exec.Code.Local.Capacity.GlobalCapacity
import Exec.Interp.Machines.Core.CoreFloatConstantPoint
import Exec.Interp.Machines.Core.CoreFloatConstantSlots
import Exec.Interp.Relations.SelectSlots
import Exec.Interp.Machines.Core.CoreSelectOperands
import Exec.Interp.Memory.MemoryCoreTransition
import Exec.Interp.Memory.MemoryCoreOperandBounds
import Exec.Interp.Memory.MemoryCoreEmission
import Exec.Interp.Memory.MemoryCoreStep
import Exec.Interp.Memory.MemoryCoreResult
import Exec.Interp.Memory.MemoryLoadStepFootprint
import Exec.Abs.Bound
import Exec.Abs.Numeric.Transition
import Exec.Abs.ReferenceBounds
import Exec.Interp.Machines.Core.CoreFunctionTyping
import Exec.Abs.CallSafety
import Exec.Interp.Calls.CallStack
import Exec.Code.Local.Relations.Common.CoreFunction
import Exec.Interp.Calls.CallRefinement
import Exec.Abs.Results
import Exec.Interp.Calls.ReturnRefinement
import Exec.Interp.Calls.ReturnResult
import Exec.Interp.Machines.Core.CoreUnreachableExecution
import Exec.Interp.Relations.StackRelation
import Exec.Interp.Relations.Epilogue
import Exec.Interp.Relations.Normalization
import Exec.Interp.Core.EmptyInversion
import Exec.Interp.Control.LabelCompletion
import Exec.Interp.Core.Erased
import Exec.Interp.Control.NormalizeClosure
import Exec.Interp.Control.NormalizeCompose
import Exec.Interp.Machines.Slice.SliceMeasure
import Exec.Store.Api.GlobalWriteExtension
import Exec.Interp.Memory.MemoryMutation
import Exec.Theorems.Composition.Core.CoreContents
import Exec.Representation.Collection
import Exec.Store.Invariant.FunctionTables
import Exec.Interp.Relations.CompiledFunctions
import Exec.Code.Local.Relations.Common.CoreFunctionContext
import Exec.Store.Invariant.CoreTypingExtension
import Exec.Store.Invariant.ObjectExtension
import Exec.Theorems.Composition.GlobalMutationShape
import Exec.Theorems.Composition.Core.CoreOwnership
import Exec.Spec.Mutation
import Exec.Store.Invariant.InstantiationCode
import Exec.Store.Initialization.SegmentObjectMetadata
import Exec.Theorems.Composition.Supported.SupportedSimdChosenExecution
import Exec.Theorems.Composition.Supported.SupportedTypedSelectChosenExecution
import Exec.Interp.StructuredMachine.EpilogueChosenExecution
import Exec.Interp.StructuredMachine.SupportedBoundarySemantics
import Exec.Theorems.Composition.Supported.ChosenNormalizeOutcome
import Exec.Interp.StructuredMachine.NormalizeExecution
import Exec.Interp.StructuredMachine.PendingChosenExecution
import Exec.Interp.StructuredMachine.SupportedControlSemantics
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
theorem step_ready_supported_chosen_host_site {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric=Spec.firstNumericChoice) (vector : choices.vector=Spec.firstVectorChoice) (occurrence : Nat)
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (compatible : GrowthChoicesCompatible memory allocator view choices)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (last : index.val+1 = exec.frames.length) (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (small : ∀ object ∈ store.globals.val, object.ty.valtype = .I32 ∨ object.ty.valtype = .F32 → object.lo.val < 2^32)
    (point : StructuredMachine.FramePoint (Store.decodeStore view code store) raw f compiled C targets next output)
    (expected : List valtype)
    (machine : StructuredMachine.Execution view code store exec ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ expected raw.pc.val false)
    (ready : ReadySource f)
    (shaped : Store.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store)
    (compiledFunctions : StructuredMachine.CompiledFunctions code store) (functionTyping : CoreFunctionsTyped view code store)
    (owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store) ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩) :
    StructuredHostSite view code exec store expected raw.pc.val false ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      ChosenSupportedStepOutcome choices occurrence allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ out ⦄ := by
  cases source : f.code with
  | nil =>
    apply Or.inr
    have labels : f.labels=[] := by simpa only [ReadySource,source] using ready
    have same : {f with code:=[],labels:=[]}=f := by rw [←source,←labels]
    apply WP.spec_mono (StructuredMachine.step_function_end_chosen_execution admissible vector occurrence memory hooks floats allocator view code exec store platform index raw inst compiled
      C targets next output ambient f rest last hf hi hc program slots (by simpa only [same] using point) expected (by simpa only [same] using machine))
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,nextSource,fresh,simulation,ownership,ambientEq,bounded⟩ := effect
    apply ChosenSupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status
    exact ⟨pc,false,nextSource,fresh,by simpa only [same] using simulation,by simpa only [same] using ownership,ambientEq,by simpa only [same] using bounded⟩
  | cons op after =>
    have same : {f with code:=op::after}=f := by rw [←source]
    have head := StructuredMachine.frame_head_coverage point ready op after source
    have result := step_head_supported_chosen_host_site admissible numericChoice vector occurrence memory hooks floats allocator correct allocation interrupts view laws code compatible exec store platform index raw inst compiled C targets next output
      ambient f rest op after head last hf hi hc program slots moduleEq small (by simpa only [same] using point) expected
      (by simpa only [same] using machine) shaped sourceSyntax bounds compiledFunctions functionTyping (by simpa only [same] using owned)
    simpa only [same] using result

theorem step_frame_supported_chosen_host_site {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric=Spec.firstNumericChoice) (vector : choices.vector=Spec.firstVectorChoice) (occurrence : Nat)
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (compatible : GrowthChoicesCompatible memory allocator view choices)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (last : index.val+1 = exec.frames.length) (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (small : ∀ object ∈ store.globals.val, object.ty.valtype = .I32 ∨ object.ty.valtype = .F32 → object.lo.val < 2^32)
    (pending : Bool)
    (point : StructuredMachine.ControlPoint (Store.decodeStore view code store) raw f compiled C targets next output pending)
    (expected : List valtype)
    (machine : StructuredMachine.Execution view code store exec ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ expected raw.pc.val pending)
    (shaped : Store.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store)
    (compiledFunctions : StructuredMachine.CompiledFunctions code store) (functionTyping : CoreFunctionsTyped view code store)
    (owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store) ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩) :
    StructuredHostSite view code exec store expected raw.pc.val pending ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      ChosenSupportedStepOutcome choices occurrence allocator hooks view code exec store platform expected compiled.code.length raw.pc.val pending
        ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ out ⦄ := by
  cases point with
  | jump target fetched continuation =>
    apply Or.inr
    apply WP.spec_mono (StructuredMachine.step_pending_chosen_execution occurrence memory hooks floats allocator platform index view code exec store raw inst compiled
      ambient f rest C targets next output hi slots last hf hc program (.jump target fetched continuation) expected machine)
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,retained,simulation⟩ := effect
    exact ChosenSupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status ⟨pc.val,false,_,retained,simulation,fun _ h=>h,rfl,fun _ h=>h⟩
  | ready point =>
    obtain ⟨count,g,labels,stop,types,chain,bound,represented,continuation,retained,metadata,done⟩ :=
      StructuredMachine.normalize_execution view code store exec raw index compiled C targets next output ambient f rest
        last hf program slots point expected machine
    obtain ⟨sourceCount,sourcePrefix,sourceBound⟩ := chain.chosen admissible vector occurrence
      (Store.decodeStore view code store) ambient rest machine.typed.typed
    have nextProgram : FrameProgram store raw compiled (g.locals.map Code.valueType) g.resultTypes C.FUNCS := program.reposition raw.pc metadata
    rcases done with skip | ready
    · obtain ⟨target,forward,fetched,tail⟩ := skip
      apply Or.inr
      apply WP.spec_mono (StructuredMachine.step_forward_jump memory hooks floats allocator view code exec store platform index raw inst compiled
        ambient g rest expected C labels stop types target last hf hi hc forward fetched represented tail retained nextProgram)
      intro out effect
      have outcome := ChosenSupportedStepOutcome.unchanged_success (choices:=choices) (occurrence:=occurrence+sourceCount) (allocator:=allocator) (hooks:=hooks) (exec:=exec) (platform:=platform)
        shaped sourceSyntax bounds effect.2.1 effect.1
        ⟨target.val,false,_,effect.2.2.2.2.1,Or.inl ⟨rfl,dispatchMeasure_forward _ _ _ _ forward tail.code.current.entry_bound⟩,fun _ h=>h,rfl,fun _ h=>h⟩
      exact outcome.prepend_normalization admissible chain sourcePrefix sourceBound
    · have nextModule : g.module=Store.decodeInstance store inst := metadata.module.trans moduleEq
      rcases step_ready_supported_chosen_host_site admissible numericChoice vector (occurrence+sourceCount) memory hooks floats allocator correct allocation interrupts view laws code compatible exec store platform index raw inst compiled
        C labels stop types ambient g rest last hf hi hc nextProgram represented nextModule small continuation expected retained ready shaped sourceSyntax bounds compiledFunctions functionTyping (chain.ownership.stateful owned) with host | operation
      · exact Or.inl (.normalize chain host)
      · apply Or.inr
        apply WP.spec_mono operation
        intro out outcome
        exact outcome.prepend_normalization admissible chain sourcePrefix sourceBound

theorem step_supported_chosen_host_site {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric=Spec.firstNumericChoice) (vector : choices.vector=Spec.firstVectorChoice) (occurrence : Nat)
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (compatible : GrowthChoicesCompatible memory allocator view choices)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (source : Abs.AState) (expected : List valtype) (pc : Nat) (pending : Bool)
    (decoded : source.store = Store.decodeStore view code store)
    (shaped : Store.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store)
    (compiledFunctions : StructuredMachine.CompiledFunctions code store) (functionTyping : CoreFunctionsTyped view code store)
    (owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store) source)
    (invariant : StructuredMachine.Execution view code store exec source expected pc pending)
    (active : 0 < exec.frames.length) :
    StructuredHostSite view code exec store expected pc pending source ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      ChosenSupportedStepOutcome choices occurrence allocator hooks view code exec store platform expected U32.max pc pending source out ⦄ := by
  have small : ∀ object ∈ store.globals.val, object.ty.valtype=.I32 ∨ object.ty.valtype=.F32 → object.lo.val<2^32 := by
    intro object member ty
    have shape := shaped.globals object member
    rcases ty with ty | ty <;> simp only [Store.GlobalShape,ty] at shape <;> exact shape.1
  rcases source with ⟨s, ambient, frames, results⟩
  cases frames with
  | nil =>
    have stack := invariant.stack
    cases stack with
    | empty empty => simp only [alloc.vec.Vec.length, empty, List.length_nil] at active; omega
  | cons f rest =>
    have noResults := invariant.typed.typed.activeResults (by simp)
    change results = [] at noResults
    subst results
    obtain ⟨raw, compiled, C, targets, next, output, top, position, program, point⟩ := invariant.cursor
    obtain ⟨inst, hi, hc, functionTable⟩ := program.lookup
    have bound : exec.frames.length - 1 ≤ Usize.max := (Nat.sub_le _ _).trans exec.frames.property
    have encoded : exec.frames.length - 1 < 2 ^ UScalarTy.Usize.numBits := by scalar_tac
    let index : Usize := UScalar.ofNatCore (exec.frames.length - 1) encoded
    have indexVal : index.val = exec.frames.length - 1 := UScalar.ofNatCore_val_eq encoded
    have last : index.val + 1 = exec.frames.length := by omega
    have hf : exec.frames.val[index.val]? = some raw := by
      rw [indexVal]
      simpa only [List.getLast?_eq_getElem?] using top
    have current := invariant.stack.top raw top
    have moduleEq := current.binding.module_lookup inst hi
    change s = Store.decodeStore view code store at decoded
    subst s
    rcases step_frame_supported_chosen_host_site admissible numericChoice vector occurrence memory hooks floats allocator correct allocation interrupts view laws code compatible exec store platform
      index raw inst compiled C targets next output ambient f rest
      last hf hi hc program current.slots moduleEq small pending point expected (by simpa only [position] using invariant) shaped sourceSyntax bounds compiledFunctions functionTyping owned with host | operation
    · exact Or.inl (by simpa only [position] using host)
    · apply Or.inr
      apply WP.spec_mono operation
      intro out outcome
      simpa only [position] using outcome.widen program.fetchBound

end Exec.Theorems
