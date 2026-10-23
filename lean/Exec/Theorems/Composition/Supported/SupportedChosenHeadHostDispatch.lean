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
import Exec.Interp.StructuredMachine.OrdinaryChosenAdvance
import Exec.Interp.StructuredMachine.NumericChosenExecutionOwned
import Exec.Interp.StructuredMachine.GlobalChosenExecution
import Exec.Interp.StructuredMachine.FloatConstantChosenExecutionOwned
import Exec.Interp.StructuredMachine.SelectChosenExecutionOwned
import Exec.Interp.StructuredMachine.MemoryChosenExecutionOwned
import Exec.Interp.StructuredMachine.CallChosenExecution
import Exec.Interp.StructuredMachine.ReturnChosenExecution
import Exec.Interp.StructuredMachine.UnreachableChosenExecution
import Exec.Interp.StructuredMachine.ControlChosenExecution
import Exec.Theorems.Composition.Supported.ChosenSupportedOutcome
import Exec.Theorems.Composition.StructuredHostSite
import Exec.Theorems.Composition.Supported.SupportedExecutionOutcome
import Exec.Theorems.Composition.StoreMutationFacts
import Exec.Interp.StructuredMachine.GlobalMutation
import Exec.Interp.StructuredMachine.OrdinaryAdvance
import Exec.Interp.StructuredMachine.NumericExecutionOwned
import Exec.Interp.StructuredMachine.GlobalExecutionOwned
import Exec.Interp.StructuredMachine.FloatConstantExecutionOwned
import Exec.Interp.StructuredMachine.SelectExecutionOwned
import Exec.Interp.StructuredMachine.MemoryExecutionOwned
import Exec.Interp.StructuredMachine.CallExecution
import Exec.Interp.StructuredMachine.ReturnExecution
import Exec.Interp.StructuredMachine.UnreachableExecution
import Exec.Abs.Cumulative.Step
import Exec.Code.Local.Relations.Common.StatefulEmission
import Exec.Code.Local.Control.Common.CumulativeFunctionContext
import Exec.Interp.StructuredMachine.CompiledFunctions
import Exec.Code.Body.Control.Table.CumulativeTableExclusion
import Exec.Code.Local.Control.Table.StructuredCodePoint
import Exec.Interp.StructuredMachine.SupportedControlSemantics
import Exec.Interp.StructuredMachine.SupportedBoundarySemantics
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
theorem step_head_supported_chosen_host_site {choices : Spec.SourceChoices} (admissible : choices.Admissible)
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
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (op : instr) (after : List instr)
    (head : DispatchHead op)
    (last : index.val+1 = exec.frames.length) (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (small : ∀ object ∈ store.globals.val, object.ty.valtype = .I32 ∨ object.ty.valtype = .F32 → object.lo.val < 2^32)
    (point : StructuredMachine.FramePoint (Store.decodeStore view code store) raw {f with code := op::after} compiled C targets next output)
    (expected : List valtype)
    (machine : StructuredMachine.Execution view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := op::after}::rest,[]⟩ expected raw.pc.val false)
    (shaped : Store.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store)
    (compiledFunctions : StructuredMachine.CompiledFunctions code store) (functionTyping : CoreFunctionsTyped view code store)
    (owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store)
      ⟨Store.decodeStore view code store,ambient,{f with code := op::after}::rest,[]⟩) :
    StructuredHostSite view code exec store expected raw.pc.val false ⟨Store.decodeStore view code store,ambient,{f with code:=op::after}::rest,[]⟩ ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      ChosenSupportedStepOutcome choices occurrence allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨Store.decodeStore view code store,ambient,{f with code:=op::after}::rest,[]⟩ out ⦄ := by
  cases head with
  | ordinary operation =>
    apply Or.inr
    apply WP.spec_mono (StructuredMachine.step_ordinary_advance_chosen admissible vector occurrence memory hooks floats allocator view code exec store platform index raw inst compiled
      C targets next output ambient f rest operation after last hf hi hc program slots point expected machine)
    intro out effect
    exact ChosenSupportedStepOutcome.unchanged_success shaped sourceSyntax bounds effect.2.1 effect.1 effect.2.2.2
  | numeric operation =>
    apply Or.inr
    apply WP.spec_mono (StructuredMachine.step_numeric_chosen_execution_owned admissible occurrence memory hooks floats allocator view code exec store platform index raw inst compiled
      C targets next output ambient f rest operation after last hf hi hc program slots point expected machine)
    intro out effect
    obtain ⟨sameStore,samePlatform,success | trapped⟩ := effect
    · obtain ⟨status,pc,g,machine,simulation,ownership,bounded⟩ := success
      exact ChosenSupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status (StructuredMachine.ChosenAdvance.of_frame machine simulation ownership rfl bounded)
    · obtain ⟨trap,status,kind,count,positive,steps⟩ := trapped
      apply ChosenSupportedStepOutcome.failure (by rw [sameStore]; exact .refl_of_shape shaped sourceSyntax bounds) status (by simp only [sameStore])
      exact Or.inl ⟨⟨trap,rfl,Or.inl (by rcases kind with rfl | rfl <;> simp [FloatCoreTrap])⟩,count,positive,steps⟩
  | loop bt body =>
    apply Or.inr
    apply WP.spec_mono (StructuredMachine.step_loop_execution_chosen memory hooks floats allocator admissible vector occurrence interrupts platform index view code exec store raw inst compiled
      ambient f rest bt body after C targets next output hi slots last hf hc program point expected machine)
    intro out effect
    obtain ⟨sameStore,success | stopped⟩ := effect
    · obtain ⟨status,pc,g,pending,machine,simulation,ownership,bounded⟩ := success
      exact ChosenSupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status (StructuredMachine.ChosenAdvance.of_frame machine simulation ownership rfl bounded)
    · apply ChosenSupportedStepOutcome.failure (by rw [sameStore]; exact .refl_of_shape shaped sourceSyntax bounds) stopped.1 (by simp only [sameStore])
      exact Or.inr (Or.inl ⟨rfl,_,stopped.2⟩)
  | call functionIndex =>
    rcases StructuredMachine.step_call_chosen_execution admissible vector occurrence memory hooks floats allocator allocation interrupts view code exec store platform index raw inst compiled
      C targets next output ambient f rest functionIndex after compiledFunctions functionTyping last hf hi hc slots program point expected machine with host | operation
    · obtain ⟨address,function,host,offset,fetched,mapped,issued,hostCode⟩ := host
      exact Or.inl (.ready ⟨index,raw,inst,compiled,C,targets,next,output,last,hf,hi,hc,program,slots,moduleEq,point,machine,owned.values⟩ (Or.inl ⟨functionIndex,offset,address,function,host,rfl,fetched,mapped,issued,hostCode⟩))
    · apply Or.inr
      apply WP.spec_mono operation
      intro out effect
      obtain ⟨sameStore,success,rejected⟩ := effect
      cases status : out.1 with
      | Ok unit =>
        cases unit
        obtain ⟨pc,source,machine,simulation,ownership,ambientEq,bounded⟩ := success status
        exact ChosenSupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status ⟨pc,false,source,machine,simulation,ownership,ambientEq,bounded⟩
      | Err error =>
        apply ChosenSupportedStepOutcome.failure (by rw [sameStore]; exact .refl_of_shape shaped sourceSyntax bounds) status (by simp only [sameStore])
        exact Or.inr (Or.inr ⟨index,raw,inst,compiled,last,hf,hi,hc,Or.inl (rejected error status)⟩)
  | return_ =>
    apply Or.inr
    apply WP.spec_mono (StructuredMachine.step_return_chosen_execution admissible vector occurrence memory hooks floats allocator view code exec store platform index raw inst compiled
      C targets next output ambient f rest after last hf hi hc program slots point expected machine)
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,source,machine,simulation,ownership,ambientEq,bounded⟩ := effect
    exact ChosenSupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status ⟨pc,false,source,machine,simulation,ownership,ambientEq,bounded⟩
  | unreachable =>
    apply Or.inr
    apply WP.spec_mono (StructuredMachine.Unreachable.step_unreachable_chosen_core_execution_owned admissible occurrence memory hooks floats allocator exec store platform index raw inst compiled
      C targets next output view code ambient f rest after last hf hi hc slots point expected machine program)
    intro out effect
    obtain ⟨sameStore,samePlatform,pc,frames,success | trapped⟩ := effect
    · obtain ⟨status,machine,simulation,ownership⟩ := success
      exact ChosenSupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status (StructuredMachine.ChosenAdvance.of_frame machine simulation ownership rfl (fun _ h => h))
    · apply ChosenSupportedStepOutcome.failure (by rw [sameStore]; exact .refl_of_shape shaped sourceSyntax bounds) trapped.1 (by simp only [sameStore])
      exact Or.inl ⟨⟨.Unreachable,rfl,Or.inl (by simp [FloatCoreTrap])⟩,trapped.2⟩
  | float32 bits =>
    apply Or.inr
    apply WP.spec_mono (StructuredMachine.FloatConstant.step_float32_execution_owned_chosen occurrence memory hooks floats allocator exec store platform index raw inst compiled
      C targets next output view code ambient f rest (Builtins.floatOfBits 32 bits.val) after last hf hi hc slots point expected machine program)
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,g,machine,simulation,ownership,bounded⟩ := effect
    exact ChosenSupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status (StructuredMachine.ChosenAdvance.of_frame machine simulation ownership rfl bounded)
  | float64 bits =>
    apply Or.inr
    apply WP.spec_mono (StructuredMachine.FloatConstant.step_float64_execution_owned_chosen occurrence memory hooks floats allocator exec store platform index raw inst compiled
      C targets next output view code ambient f rest (Builtins.floatOfBits 64 bits.val) after last hf hi hc slots point expected machine program)
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,g,machine,simulation,ownership,bounded⟩ := effect
    exact ChosenSupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status (StructuredMachine.ChosenAdvance.of_frame machine simulation ownership rfl bounded)
  | select =>
    apply Or.inr
    apply WP.spec_mono (StructuredMachine.Select.step_select_core_execution_owned_chosen admissible vector occurrence memory hooks floats allocator exec store platform index raw inst compiled
      C targets next output view code ambient f rest after last hf hi hc slots point expected machine program)
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,g,machine,simulation,ownership,bounded⟩ := effect
    exact ChosenSupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status (StructuredMachine.ChosenAdvance.of_frame machine simulation ownership rfl bounded)
  | globalGet globalIndex =>
    apply Or.inr
    apply WP.spec_mono (StructuredMachine.Global.step_globalGet_chosen_execution_owned admissible vector occurrence memory hooks floats allocator platform index view code exec store raw inst compiled
      ambient f rest after globalIndex.val C targets next output hi moduleEq slots last hf hc program small point expected machine)
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,g,machine,simulation,ownership,bounded⟩ := effect
    exact ChosenSupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status (StructuredMachine.ChosenAdvance.of_frame machine simulation ownership rfl bounded)
  | globalSet globalIndex =>
    apply Or.inr
    have pcBound : raw.pc.val < U32.max := by
      rcases StructuredMachine.Global.corePoint_globalSet_head globalIndex.val after point.code with ⟨target,forward,fetch,tail⟩ | operation
      · exact program.fetched_bound _ fetch
      · obtain ⟨ty,idx,src,front,indexEq,lookup,values,position,fetch,tail⟩ := operation
        exact program.fetched_bound _ fetch
    have mutation := StructuredMachine.Global.coreFramePoint_globalSet_store_mutation memory hooks floats allocator platform index view code exec store raw inst compiled
      ambient f rest after globalIndex.val C targets next output hi moduleEq slots last hf hc pcBound point machine.typed
    obtain ⟨out,run,effect⟩ := WP.spec_imp_exists (StructuredMachine.Global.step_globalSet_chosen_execution_owned admissible vector occurrence memory hooks floats allocator platform index view code exec store raw inst compiled
      ambient f rest after globalIndex.val C targets next output hi moduleEq slots last hf hc program point expected machine)
    rw [run,WP.spec_ok] at mutation ⊢
    obtain ⟨status,samePlatform,metadata,extension,pc,g,machine,simulation,ownership,bounded⟩ := effect
    exact ChosenSupportedStepOutcome.success (core_mutation_cumulative_of_shape view code store _ _ shaped sourceSyntax bounds owned.core mutation) status (StructuredMachine.ChosenAdvance.of_frame machine simulation ownership rfl bounded)
  | load operation argument =>
    apply Or.inr
    apply WP.spec_mono (StructuredMachine.Memory.step_memory_load_execution_owned_chosen admissible vector occurrence memory hooks floats allocator platform index view laws code exec store raw inst compiled
      ambient f rest after operation argument C targets next output hi moduleEq slots last hf hc point expected machine program)
    intro out effect
    obtain ⟨samePlatform,changed,metadata,extension,success | trapped⟩ := effect
    · have mutation : CoreStoreMutation view ⟨Store.decodeStore view code store,ambient,{f with code := operation.source argument::after}::rest,[]⟩ store out.2.2.1 := by
        rcases changed with same | ⟨address,object,issued,mutation⟩
        · rw [same]; exact .unchanged
        · exact .memory issued mutation
      obtain ⟨status,pc,g,machine,simulation,ownership,bounded⟩ := success
      exact ChosenSupportedStepOutcome.success (core_mutation_cumulative_of_shape view code store _ _ shaped sourceSyntax bounds owned.core mutation) status (StructuredMachine.ChosenAdvance.of_frame machine simulation ownership rfl bounded)
    · have mutation : CoreStoreMutation view ⟨Store.decodeStore view code store,ambient,{f with code := operation.source argument::after}::rest,[]⟩ store out.2.2.1 := by
        rcases changed with same | ⟨address,object,issued,mutation⟩
        · rw [same]; exact .unchanged
        · exact .memory issued mutation
      apply ChosenSupportedStepOutcome.failure (core_mutation_cumulative_of_shape view code store _ _ shaped sourceSyntax bounds owned.core mutation) trapped.1 trapped.2.1
      exact Or.inl ⟨⟨.MemoryOutOfBounds,rfl,Or.inl (by simp [FloatCoreTrap])⟩,trapped.2.2⟩
  | store operation argument =>
    apply Or.inr
    apply WP.spec_mono (StructuredMachine.Memory.step_memory_store_execution_owned_chosen admissible vector occurrence memory hooks floats allocator platform index view laws code exec store raw inst compiled
      ambient f rest after operation argument C targets next output hi moduleEq slots last hf hc point expected machine program)
    intro out effect
    obtain ⟨samePlatform,changed,metadata,extension,success | trapped⟩ := effect
    · have mutation : CoreStoreMutation view ⟨Store.decodeStore view code store,ambient,{f with code := operation.source argument::after}::rest,[]⟩ store out.2.2.1 := by
        rcases changed with same | ⟨address,object,issued,mutation⟩
        · rw [same]; exact .unchanged
        · exact .memory issued mutation
      obtain ⟨status,pc,g,machine,simulation,ownership,bounded⟩ := success
      exact ChosenSupportedStepOutcome.success (core_mutation_cumulative_of_shape view code store _ _ shaped sourceSyntax bounds owned.core mutation) status (StructuredMachine.ChosenAdvance.of_frame machine simulation ownership rfl bounded)
    · have mutation : CoreStoreMutation view ⟨Store.decodeStore view code store,ambient,{f with code := operation.source argument::after}::rest,[]⟩ store out.2.2.1 := by
        rcases changed with same | ⟨address,object,issued,mutation⟩
        · rw [same]; exact .unchanged
        · exact .memory issued mutation
      apply ChosenSupportedStepOutcome.failure (core_mutation_cumulative_of_shape view code store _ _ shaped sourceSyntax bounds owned.core mutation) trapped.1 trapped.2.1
      exact Or.inl ⟨⟨.MemoryOutOfBounds,rfl,Or.inl (by simp [FloatCoreTrap])⟩,trapped.2.2⟩
  | float operation =>
    apply Or.inr
    apply WP.spec_mono (step_scalar_supported_chosen_execution admissible numericChoice occurrence memory hooks floats allocator correct exec store platform index raw inst compiled C targets next output
      view code ambient f rest operation after last hf hi hc slots point expected machine program shaped sourceSyntax bounds)
    intro out result
    exact result.2.2
  | stateful operation =>
    apply Or.inr
    exact stateful_chosen_execution_supported admissible vector occurrence memory hooks floats allocator allocation view laws code compatible exec store platform index raw inst compiled C targets next output
      ambient f rest after operation last hf hi hc moduleEq slots point expected machine program shaped sourceSyntax bounds owned
  | indirect table type =>
    rcases step_indirect_supported_chosen_execution admissible vector occurrence memory hooks floats allocator allocation interrupts view code exec store platform index raw inst compiled C targets next output
      ambient f rest table type after last hf hi hc moduleEq program slots point expected machine shaped compiledFunctions functionTyping with host | operation
    · exact Or.inl (.ready ⟨index,raw,inst,compiled,C,targets,next,output,last,hf,hi,hc,program,slots,moduleEq,point,machine,owned.values⟩ (Or.inr ⟨table,type,rfl,host⟩))
    · apply Or.inr
      apply WP.spec_mono operation
      intro out result
      cases status : out.1 with
      | Ok unit =>
        cases unit
        exact ChosenSupportedStepOutcome.unchanged_success shaped sourceSyntax bounds result.1 status (result.2.1 status)
      | Err error =>
        apply ChosenSupportedStepOutcome.failure (by rw [result.1];exact .refl_of_shape shaped sourceSyntax bounds) status (by simp only [result.1])
        rcases result.2.2 error status with ⟨⟨trap,errorEq,kind⟩,steps⟩ | cause
        · exact Or.inl ⟨⟨trap,errorEq,Or.inr kind⟩,steps⟩
        · exact Or.inr (Or.inr ⟨index,raw,inst,compiled,last,hf,hi,hc,Or.inr ⟨code,cause⟩⟩)
  | simd operation =>
    apply Or.inr
    exact step_simd_supported_chosen_execution admissible vector occurrence memory hooks floats allocator view code laws correct exec store platform raw index inst compiled
      C targets next output ambient f rest op after expected last hf hi hc program slots point operation machine shaped sourceSyntax bounds
  | typedSelect declared =>
    apply Or.inr
    exact step_typed_select_supported_execution_chosen admissible vector occurrence memory hooks floats allocator exec store platform index raw inst compiled C targets next output
      view code ambient f rest declared after last hf hi hc slots point expected machine program shaped sourceSyntax bounds
  | branchTable depths fallback =>
    apply Or.inr
    exact step_branch_table_supported_chosen admissible vector occurrence memory hooks floats allocator view code exec store platform
      index raw inst compiled C targets next output ambient f rest after depths fallback expected last hf hi hc
      program slots point machine shaped sourceSyntax bounds

end Exec.Theorems
