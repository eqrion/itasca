import Exec.Theorems.Composition.Supported.SupportedExecutionOutcome
import Exec.Theorems.Composition.StoreMutationFacts
import Exec.Interp.StructuredMachine.GlobalMutation
import Exec.Interp.Machines.Core.CoreHeadCoverage
import Exec.Interp.StructuredMachine.OrdinaryAdvance
import Exec.Interp.StructuredMachine.NumericExecutionOwned
import Exec.Interp.StructuredMachine.GlobalExecutionOwned
import Exec.Interp.StructuredMachine.FloatConstantExecutionOwned
import Exec.Interp.StructuredMachine.SelectExecutionOwned
import Exec.Interp.StructuredMachine.MemoryExecutionOwned
import Exec.Interp.StructuredMachine.CallExecution
import Exec.Interp.StructuredMachine.ReturnExecution
import Exec.Interp.StructuredMachine.UnreachableExecution
import Exec.Interp.Cumulative.Certificates
import Exec.Interp.StructuredMachine.SupportedControlSemantics
import Exec.Interp.StructuredMachine.SupportedBoundarySemantics

namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

theorem step_head_supported_base {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}
    [∀ compiled, StructuredMachine.FloatHeads (emission compiled)]
    [∀ compiled, StructuredMachine.OrdinaryHeads (emission compiled)]
    (language : Abs.Supported.Language allowed) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (op : instr) (after : List instr)
    (head : CoreDispatchHead op)
    (last : index.val+1 = exec.frames.length) (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (small : ∀ object ∈ store.globals.val, object.ty.valtype = .I32 ∨ object.ty.valtype = .F32 → object.lo.val < 2^32)
    (point : StructuredMachine.FramePoint emission (Store.decodeStore view code store) raw {f with code := op::after} compiled C targets next output)
    (expected : List valtype)
    (machine : StructuredMachine.Execution emission (Abs.SupportedState allowed) view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := op::after}::rest,[]⟩ expected raw.pc.val false)
    (shaped : Store.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store)
    (compiledFunctions : StructuredMachine.CompiledFunctions emission code store)
    (functionTyping : CoreFunctionsTyped view code store)
    (owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store)
      ⟨Store.decodeStore view code store,ambient,{f with code := op::after}::rest,[]⟩) :
    CoreHostBoundary exec store ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SupportedStepOutcome emission allowed allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨Store.decodeStore view code store,ambient,{f with code := op::after}::rest,[]⟩ out ⦄ := by
  cases head with
  | pure pureHead =>
    cases pureHead with
    | ordinary operation =>
      apply Or.inr
      apply WP.spec_mono (StructuredMachine.step_ordinary_advance (StructuredMachine.supportedControlSemantics language) memory hooks floats allocator view code exec store platform index raw inst compiled
        C targets next output ambient f rest operation after last hf hi hc program slots point expected machine)
      intro out effect
      exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds effect.2.1 effect.1 effect.2.2.2
    | numeric operation =>
      apply Or.inr
      apply WP.spec_mono (StructuredMachine.step_numeric_execution_owned (StructuredMachine.supportedControlSemantics language) memory hooks floats allocator view code exec store platform index raw inst compiled
        C targets next output ambient f rest operation after last hf hi hc program slots point expected machine)
      intro out effect
      obtain ⟨sameStore,samePlatform,success | trapped⟩ := effect
      · obtain ⟨status,pc,g,machine,simulation,ownership,bounded⟩ := success
        exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status (StructuredMachine.Advance.of_frame machine simulation ownership rfl bounded)
      · obtain ⟨trap,status,kind,count,positive,steps⟩ := trapped
        apply SupportedStepOutcome.failure (by rw [sameStore]; exact .refl_of_shape shaped sourceSyntax bounds) status (by simp only [sameStore])
        exact Or.inl ⟨⟨trap,rfl,Or.inl (by rcases kind with rfl | rfl <;> simp [FloatCoreTrap])⟩,count,positive,steps⟩
    | loop bt body =>
      apply Or.inr
      apply WP.spec_mono (StructuredMachine.step_loop_execution memory hooks floats allocator (StructuredMachine.supportedControlSemantics language) interrupts platform index view code exec store raw inst compiled
        ambient f rest bt body after C targets next output hi slots last hf hc program point expected machine)
      intro out effect
      obtain ⟨sameStore,success | stopped⟩ := effect
      · obtain ⟨status,pc,g,pending,machine,simulation,ownership,bounded⟩ := success
        exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status (StructuredMachine.Advance.of_frame machine simulation ownership rfl bounded)
      · apply SupportedStepOutcome.failure (by rw [sameStore]; exact .refl_of_shape shaped sourceSyntax bounds) stopped.1 (by simp only [sameStore])
        exact Or.inr (Or.inl ⟨rfl,_,stopped.2⟩)
    | call functionIndex =>
      rcases StructuredMachine.step_call_execution (StructuredMachine.supportedCallSemantics language) memory hooks floats allocator allocation interrupts view code exec store platform index raw inst compiled
        C targets next output ambient f rest functionIndex after compiledFunctions functionTyping last hf hi hc slots program point expected machine with host | operation
      · obtain ⟨address,function,host,offset,fetched,mapped,issued,hostCode⟩ := host
        exact Or.inl ⟨index,raw,inst,compiled,functionIndex,offset,address,function,host,last,hf,hi,hc,fetched,mapped,issued,hostCode⟩
      · apply Or.inr
        apply WP.spec_mono operation
        intro out effect
        obtain ⟨sameStore,success,rejected⟩ := effect
        cases status : out.1 with
        | Ok unit =>
          cases unit
          obtain ⟨pc,source,machine,simulation,ownership,ambientEq,bounded⟩ := success status
          exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status ⟨pc,false,source,machine,simulation,ownership,ambientEq,bounded⟩
        | Err error =>
          apply SupportedStepOutcome.failure (by rw [sameStore]; exact .refl_of_shape shaped sourceSyntax bounds) status (by simp only [sameStore])
          exact Or.inr (Or.inr ⟨index,raw,inst,compiled,last,hf,hi,hc,Or.inl (rejected error status)⟩)
    | return_ =>
      apply Or.inr
      apply WP.spec_mono (StructuredMachine.step_return_execution StructuredMachine.supportedReturnSemantics memory hooks floats allocator view code exec store platform index raw inst compiled
        C targets next output ambient f rest after last hf hi hc program slots point expected machine)
      intro out effect
      obtain ⟨status,sameStore,samePlatform,pc,source,machine,simulation,ownership,ambientEq,bounded⟩ := effect
      exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status ⟨pc,false,source,machine,simulation,ownership,ambientEq,bounded⟩
    | unreachable =>
      apply Or.inr
      apply WP.spec_mono (StructuredMachine.Unreachable.step_unreachable_core_execution_owned memory hooks floats allocator exec store platform index raw inst compiled
        C targets next output view code ambient f rest after last hf hi hc slots point expected machine program)
      intro out effect
      obtain ⟨sameStore,samePlatform,pc,frames,success | trapped⟩ := effect
      · obtain ⟨status,machine,simulation,ownership⟩ := success
        exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status (StructuredMachine.Advance.of_frame machine simulation ownership rfl (fun _ h => h))
      · apply SupportedStepOutcome.failure (by rw [sameStore]; exact .refl_of_shape shaped sourceSyntax bounds) trapped.1 (by simp only [sameStore])
        exact Or.inl ⟨⟨.Unreachable,rfl,Or.inl (by simp [FloatCoreTrap])⟩,trapped.2⟩
  | float32 bits =>
    apply Or.inr
    apply WP.spec_mono (StructuredMachine.FloatConstant.step_float32_execution_owned (StructuredMachine.supportedControlSemantics language) memory hooks floats allocator exec store platform index raw inst compiled
      C targets next output view code ambient f rest (Builtins.floatOfBits 32 bits.val) after last hf hi hc slots point expected machine program)
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,g,machine,simulation,ownership,bounded⟩ := effect
    exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status (StructuredMachine.Advance.of_frame machine simulation ownership rfl bounded)
  | float64 bits =>
    apply Or.inr
    apply WP.spec_mono (StructuredMachine.FloatConstant.step_float64_execution_owned (StructuredMachine.supportedControlSemantics language) memory hooks floats allocator exec store platform index raw inst compiled
      C targets next output view code ambient f rest (Builtins.floatOfBits 64 bits.val) after last hf hi hc slots point expected machine program)
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,g,machine,simulation,ownership,bounded⟩ := effect
    exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status (StructuredMachine.Advance.of_frame machine simulation ownership rfl bounded)
  | select =>
    apply Or.inr
    apply WP.spec_mono (StructuredMachine.Select.step_select_core_execution_owned (StructuredMachine.supportedControlSemantics language) memory hooks floats allocator exec store platform index raw inst compiled
      C targets next output view code ambient f rest after last hf hi hc slots point expected machine program)
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,g,machine,simulation,ownership,bounded⟩ := effect
    exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status (StructuredMachine.Advance.of_frame machine simulation ownership rfl bounded)
  | globalGet globalIndex =>
    apply Or.inr
    apply WP.spec_mono (StructuredMachine.Global.step_globalGet_core_execution_owned (StructuredMachine.supportedControlSemantics language) memory hooks floats allocator platform index view code exec store raw inst compiled
      ambient f rest after globalIndex.val C targets next output hi moduleEq slots last hf hc program small point expected machine)
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,g,machine,simulation,ownership,bounded⟩ := effect
    exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status (StructuredMachine.Advance.of_frame machine simulation ownership rfl bounded)
  | globalSet globalIndex =>
    apply Or.inr
    have pcBound : raw.pc.val < U32.max := by
      rcases StructuredMachine.Global.corePoint_globalSet_head globalIndex.val after point.code with ⟨target,forward,fetch,tail⟩ | operation
      · exact program.fetched_bound _ fetch
      · obtain ⟨ty,idx,src,front,indexEq,lookup,values,position,fetch,tail⟩ := operation
        exact program.fetched_bound _ fetch
    have mutation := StructuredMachine.Global.coreFramePoint_globalSet_store_mutation memory hooks floats allocator platform index view code exec store raw inst compiled
      ambient f rest after globalIndex.val C targets next output hi moduleEq slots last hf hc pcBound point machine.typed
    obtain ⟨out,run,effect⟩ := WP.spec_imp_exists (StructuredMachine.Global.step_globalSet_core_execution_owned (StructuredMachine.supportedControlSemantics language) memory hooks floats allocator platform index view code exec store raw inst compiled
      ambient f rest after globalIndex.val C targets next output hi moduleEq slots last hf hc program point expected machine)
    rw [run,WP.spec_ok] at mutation ⊢
    obtain ⟨status,samePlatform,metadata,extension,pc,g,machine,simulation,ownership,bounded⟩ := effect
    exact SupportedStepOutcome.success (core_mutation_cumulative_of_shape view code store _ _ shaped sourceSyntax bounds owned.core mutation) status (StructuredMachine.Advance.of_frame machine simulation ownership rfl bounded)
  | load operation argument =>
    apply Or.inr
    apply WP.spec_mono (StructuredMachine.Memory.step_memory_load_execution_owned (StructuredMachine.supportedControlSemantics language) memory hooks floats allocator platform index view laws code exec store raw inst compiled
      ambient f rest after operation argument C targets next output hi moduleEq slots last hf hc point expected machine program)
    intro out effect
    obtain ⟨samePlatform,changed,metadata,extension,success | trapped⟩ := effect
    · have mutation : CoreStoreMutation view ⟨Store.decodeStore view code store,ambient,{f with code := operation.source argument::after}::rest,[]⟩ store out.2.2.1 := by
        rcases changed with same | ⟨address,object,issued,mutation⟩
        · rw [same]; exact .unchanged
        · exact .memory issued mutation
      obtain ⟨status,pc,g,machine,simulation,ownership,bounded⟩ := success
      exact SupportedStepOutcome.success (core_mutation_cumulative_of_shape view code store _ _ shaped sourceSyntax bounds owned.core mutation) status (StructuredMachine.Advance.of_frame machine simulation ownership rfl bounded)
    · have mutation : CoreStoreMutation view ⟨Store.decodeStore view code store,ambient,{f with code := operation.source argument::after}::rest,[]⟩ store out.2.2.1 := by
        rcases changed with same | ⟨address,object,issued,mutation⟩
        · rw [same]; exact .unchanged
        · exact .memory issued mutation
      apply SupportedStepOutcome.failure (core_mutation_cumulative_of_shape view code store _ _ shaped sourceSyntax bounds owned.core mutation) trapped.1 trapped.2.1
      exact Or.inl ⟨⟨.MemoryOutOfBounds,rfl,Or.inl (by simp [FloatCoreTrap])⟩,trapped.2.2⟩
  | store operation argument =>
    apply Or.inr
    apply WP.spec_mono (StructuredMachine.Memory.step_memory_store_execution_owned (StructuredMachine.supportedControlSemantics language) memory hooks floats allocator platform index view laws code exec store raw inst compiled
      ambient f rest after operation argument C targets next output hi moduleEq slots last hf hc point expected machine program)
    intro out effect
    obtain ⟨samePlatform,changed,metadata,extension,success | trapped⟩ := effect
    · have mutation : CoreStoreMutation view ⟨Store.decodeStore view code store,ambient,{f with code := operation.source argument::after}::rest,[]⟩ store out.2.2.1 := by
        rcases changed with same | ⟨address,object,issued,mutation⟩
        · rw [same]; exact .unchanged
        · exact .memory issued mutation
      obtain ⟨status,pc,g,machine,simulation,ownership,bounded⟩ := success
      exact SupportedStepOutcome.success (core_mutation_cumulative_of_shape view code store _ _ shaped sourceSyntax bounds owned.core mutation) status (StructuredMachine.Advance.of_frame machine simulation ownership rfl bounded)
    · have mutation : CoreStoreMutation view ⟨Store.decodeStore view code store,ambient,{f with code := operation.source argument::after}::rest,[]⟩ store out.2.2.1 := by
        rcases changed with same | ⟨address,object,issued,mutation⟩
        · rw [same]; exact .unchanged
        · exact .memory issued mutation
      apply SupportedStepOutcome.failure (core_mutation_cumulative_of_shape view code store _ _ shaped sourceSyntax bounds owned.core mutation) trapped.1 trapped.2.1
      exact Or.inl ⟨⟨.MemoryOutOfBounds,rfl,Or.inl (by simp [FloatCoreTrap])⟩,trapped.2.2⟩
end Exec.Theorems
