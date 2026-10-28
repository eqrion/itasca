import Exec.Platform.Laws
import Exec.Theorems.Composition.StructuredHostSite
import Exec.Theorems.Composition.Supported.SupportedExecutionOutcome
import Exec.Theorems.Composition.StoreMutationFacts
import Exec.Interp.StructuredMachine.GlobalMutation
import Exec.Interp.StructuredMachine.SupportedHeadCoverage
import Exec.Interp.StructuredMachine.OrdinaryAdvance
import Exec.Interp.StructuredMachine.NumericExecutionOwned
import Exec.Interp.StructuredMachine.GlobalExecutionOwned
import Exec.Interp.StructuredMachine.FloatConstantExecutionOwned
import Exec.Interp.StructuredMachine.SelectExecutionOwned
import Exec.Interp.StructuredMachine.MemoryExecutionOwned
import Exec.Interp.StructuredMachine.CallExecution
import Exec.Interp.StructuredMachine.ReturnExecution
import Exec.Interp.StructuredMachine.UnreachableExecution
import Exec.Interp.StructuredMachine.Execution
import Exec.Abs.Cumulative.Step
import Exec.Code.Local.Relations.Common.StatefulEmission
import Exec.Interp.Relations.CompiledFunctions
import Exec.Code.Local.Control.Common.CumulativeFunctionContext
import Exec.Interp.StructuredMachine.CompiledFunctions
import Exec.Code.Body.Control.Table.CumulativeTableExclusion
import Exec.Code.Local.Control.Common.Structured
import Exec.Code.Local.Control.Common.StructuredComposition
import Exec.Code.Local.Control.Table.StructuredCodePoint
import Exec.Interp.StructuredMachine.SupportedControlSemantics
import Exec.Interp.StructuredMachine.SupportedBoundarySemantics
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
theorem step_head_supported_host_site
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view) (code : Store.CodeInterpretation)
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
      SupportedStepOutcome allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨Store.decodeStore view code store,ambient,{f with code:=op::after}::rest,[]⟩ out ⦄ := by
  cases head with
  | ordinary operation =>
    apply Or.inr
    apply WP.spec_mono (StructuredMachine.step_ordinary_advance memory hooks floats allocator view code exec store platform index raw inst compiled
      C targets next output ambient f rest operation after last hf hi hc program slots point expected machine)
    intro out effect
    exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds effect.2.1 effect.1 effect.2.2.2
  | numeric operation =>
    apply Or.inr
    apply WP.spec_mono (StructuredMachine.step_numeric_execution_owned memory hooks floats allocator view code exec store platform index raw inst compiled
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
    apply WP.spec_mono (StructuredMachine.step_loop_execution memory hooks floats allocator laws.interruptsReturn platform index view code exec store raw inst compiled
      ambient f rest bt body after C targets next output hi slots last hf hc program point expected machine)
    intro out effect
    obtain ⟨sameStore,success | stopped⟩ := effect
    · obtain ⟨status,pc,g,pending,machine,simulation,ownership,bounded⟩ := success
      exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status (StructuredMachine.Advance.of_frame machine simulation ownership rfl bounded)
    · apply SupportedStepOutcome.failure (by rw [sameStore]; exact .refl_of_shape shaped sourceSyntax bounds) stopped.1 (by simp only [sameStore])
      exact Or.inr (Or.inl ⟨rfl,_,stopped.2⟩)
  | call functionIndex =>
    rcases StructuredMachine.step_call_execution memory hooks floats allocator laws.allocCorrect laws.interruptsReturn view code exec store platform index raw inst compiled
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
        exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status ⟨pc,false,source,machine,simulation,ownership,ambientEq,bounded⟩
      | Err error =>
        apply SupportedStepOutcome.failure (by rw [sameStore]; exact .refl_of_shape shaped sourceSyntax bounds) status (by simp only [sameStore])
        exact Or.inr (Or.inr ⟨index,raw,inst,compiled,last,hf,hi,hc,Or.inl (rejected error status)⟩)
  | return_ =>
    apply Or.inr
    apply WP.spec_mono (StructuredMachine.step_return_execution memory hooks floats allocator view code exec store platform index raw inst compiled
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
    apply WP.spec_mono (StructuredMachine.FloatConstant.step_float32_execution_owned memory hooks floats allocator exec store platform index raw inst compiled
      C targets next output view code ambient f rest (Builtins.floatOfBits 32 bits.val) after last hf hi hc slots point expected machine program)
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,g,machine,simulation,ownership,bounded⟩ := effect
    exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status (StructuredMachine.Advance.of_frame machine simulation ownership rfl bounded)
  | float64 bits =>
    apply Or.inr
    apply WP.spec_mono (StructuredMachine.FloatConstant.step_float64_execution_owned memory hooks floats allocator exec store platform index raw inst compiled
      C targets next output view code ambient f rest (Builtins.floatOfBits 64 bits.val) after last hf hi hc slots point expected machine program)
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,g,machine,simulation,ownership,bounded⟩ := effect
    exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status (StructuredMachine.Advance.of_frame machine simulation ownership rfl bounded)
  | select =>
    apply Or.inr
    apply WP.spec_mono (StructuredMachine.Select.step_select_core_execution_owned memory hooks floats allocator exec store platform index raw inst compiled
      C targets next output view code ambient f rest after last hf hi hc slots point expected machine program)
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,g,machine,simulation,ownership,bounded⟩ := effect
    exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status (StructuredMachine.Advance.of_frame machine simulation ownership rfl bounded)
  | globalGet globalIndex =>
    apply Or.inr
    apply WP.spec_mono (StructuredMachine.Global.step_globalGet_core_execution_owned memory hooks floats allocator platform index view code exec store raw inst compiled
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
    obtain ⟨out,run,effect⟩ := WP.spec_imp_exists (StructuredMachine.Global.step_globalSet_core_execution_owned memory hooks floats allocator platform index view code exec store raw inst compiled
      ambient f rest after globalIndex.val C targets next output hi moduleEq slots last hf hc program point expected machine)
    rw [run,WP.spec_ok] at mutation ⊢
    obtain ⟨status,samePlatform,metadata,extension,pc,g,machine,simulation,ownership,bounded⟩ := effect
    exact SupportedStepOutcome.success (core_mutation_cumulative_of_shape view code store _ _ shaped sourceSyntax bounds owned.core mutation) status (StructuredMachine.Advance.of_frame machine simulation ownership rfl bounded)
  | load operation argument =>
    apply Or.inr
    apply WP.spec_mono (StructuredMachine.Memory.step_memory_load_execution_owned memory hooks floats allocator platform index view laws.memoryLaws code exec store raw inst compiled
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
    apply WP.spec_mono (StructuredMachine.Memory.step_memory_store_execution_owned memory hooks floats allocator platform index view laws.memoryLaws code exec store raw inst compiled
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
  | float operation =>
    apply Or.inr
    apply WP.spec_mono (step_scalar_supported_execution memory hooks floats allocator laws.floatsCorrect exec store platform index raw inst compiled C targets next output
      view code ambient f rest operation after last hf hi hc slots point expected machine program shaped sourceSyntax bounds)
    intro out result
    exact result.2.2
  | stateful operation =>
    apply Or.inr
    exact stateful_execution_supported memory hooks floats allocator laws.allocCorrect view laws.memoryLaws code exec store platform index raw inst compiled C targets next output
      ambient f rest after operation last hf hi hc moduleEq slots point expected machine program shaped sourceSyntax bounds owned
  | indirect table type =>
    rcases step_indirect_supported_execution memory hooks floats allocator laws.allocCorrect laws.interruptsReturn view code exec store platform index raw inst compiled C targets next output
      ambient f rest table type after last hf hi hc moduleEq program slots point expected machine shaped compiledFunctions functionTyping with host | operation
    · exact Or.inl (.ready ⟨index,raw,inst,compiled,C,targets,next,output,last,hf,hi,hc,program,slots,moduleEq,point,machine,owned.values⟩ (Or.inr ⟨table,type,rfl,host⟩))
    · apply Or.inr
      apply WP.spec_mono operation
      intro out result
      cases status : out.1 with
      | Ok unit =>
        cases unit
        exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds result.1 status (result.2.1 status)
      | Err error =>
        apply SupportedStepOutcome.failure (by rw [result.1];exact .refl_of_shape shaped sourceSyntax bounds) status (by simp only [result.1])
        rcases result.2.2 error status with ⟨⟨trap,errorEq,kind⟩,steps⟩ | cause
        · exact Or.inl ⟨⟨trap,errorEq,Or.inr kind⟩,steps⟩
        · exact Or.inr (Or.inr ⟨index,raw,inst,compiled,last,hf,hi,hc,Or.inr ⟨code,cause⟩⟩)
  | simd operation =>
    apply Or.inr
    exact step_simd_supported_execution memory hooks floats allocator view code laws.memoryLaws laws.floatsCorrect exec store platform raw index inst compiled
      C targets next output ambient f rest op after expected last hf hi hc program slots point operation machine shaped sourceSyntax bounds
  | typedSelect declared =>
    apply Or.inr
    exact step_typed_select_supported_execution memory hooks floats allocator exec store platform index raw inst compiled C targets next output
      view code ambient f rest declared after last hf hi hc slots point expected machine program shaped sourceSyntax bounds
  | branchTable depths fallback =>
    apply Or.inr
    exact step_branch_table_supported memory hooks floats allocator view code exec store platform
      index raw inst compiled C targets next output ambient f rest after depths fallback expected last hf hi hc
      program slots point machine shaped sourceSyntax bounds

theorem step_ready_supported_host_site
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view) (code : Store.CodeInterpretation)
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
      SupportedStepOutcome allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ out ⦄ := by
  cases source : f.code with
  | nil =>
    apply Or.inr
    have labels : f.labels=[] := by simpa only [ReadySource,source] using ready
    have same : {f with code:=[],labels:=[]}=f := by rw [←source,←labels]
    apply WP.spec_mono (StructuredMachine.step_function_end_execution memory hooks floats allocator view code exec store platform index raw inst compiled
      C targets next output ambient f rest last hf hi hc program slots (by simpa only [same] using point) expected (by simpa only [same] using machine))
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,nextSource,fresh,simulation,ownership,ambientEq,bounded⟩ := effect
    apply SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status
    exact ⟨pc,false,nextSource,fresh,by simpa only [same] using simulation,by simpa only [same] using ownership,ambientEq,by simpa only [same] using bounded⟩
  | cons op after =>
    have same : {f with code:=op::after}=f := by rw [←source]
    have head := StructuredMachine.frame_head_coverage point ready op after source
    have result := step_head_supported_host_site memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output
      ambient f rest op after head last hf hi hc program slots moduleEq small (by simpa only [same] using point) expected
      (by simpa only [same] using machine) shaped sourceSyntax bounds compiledFunctions functionTyping (by simpa only [same] using owned)
    simpa only [same] using result

theorem step_frame_supported_host_site
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view) (code : Store.CodeInterpretation)
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
      SupportedStepOutcome allocator hooks view code exec store platform expected compiled.code.length raw.pc.val pending
        ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ out ⦄ := by
  cases point with
  | jump target fetched continuation =>
    apply Or.inr
    apply WP.spec_mono (StructuredMachine.step_pending_execution memory hooks floats allocator platform index view code exec store raw inst compiled
      ambient f rest C targets next output hi slots last hf hc program (.jump target fetched continuation) expected machine)
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,retained,simulation⟩ := effect
    exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status ⟨pc.val,false,_,retained,simulation,fun _ h=>h,rfl,fun _ h=>h⟩
  | ready point =>
    obtain ⟨count,g,labels,stop,types,chain,bound,represented,continuation,retained,metadata,done⟩ :=
      StructuredMachine.normalize_execution view code store exec raw index compiled C targets next output ambient f rest
        last hf program slots point expected machine
    have nextProgram : FrameProgram store raw compiled (g.locals.map Code.valueType) g.resultTypes C.FUNCS := program.reposition raw.pc metadata
    rcases done with skip | ready
    · obtain ⟨target,forward,fetched,tail⟩ := skip
      apply Or.inr
      apply WP.spec_mono (StructuredMachine.step_forward_jump memory hooks floats allocator view code exec store platform index raw inst compiled
        ambient g rest expected C labels stop types target last hf hi hc forward fetched represented tail retained nextProgram)
      intro out effect
      have outcome := SupportedStepOutcome.unchanged_success (allocator:=allocator) (hooks:=hooks) (exec:=exec) (platform:=platform)
        shaped sourceSyntax bounds effect.2.1 effect.1
        ⟨target.val,false,_,effect.2.2.2.2.1,effect.2.2.2.2.2,fun _ h=>h,rfl,fun _ h=>h⟩
      exact outcome.prepend_normalization chain machine.typed.typed
    · have nextModule : g.module=Store.decodeInstance store inst := metadata.module.trans moduleEq
      rcases step_ready_supported_host_site memory hooks floats allocator view laws code exec store platform index raw inst compiled
        C labels stop types ambient g rest last hf hi hc nextProgram represented nextModule small continuation expected retained ready shaped sourceSyntax bounds compiledFunctions functionTyping (chain.ownership.stateful owned) with host | operation
      · exact Or.inl (.normalize chain host)
      · apply Or.inr
        apply WP.spec_mono operation
        intro out outcome
        exact outcome.prepend_normalization chain machine.typed.typed

theorem step_supported_host_site
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view) (code : Store.CodeInterpretation)
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
      SupportedStepOutcome allocator hooks view code exec store platform expected U32.max pc pending source out ⦄ := by
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
    rcases step_frame_supported_host_site memory hooks floats allocator view laws code exec store platform
      index raw inst compiled C targets next output ambient f rest
      last hf hi hc program current.slots moduleEq small pending point expected (by simpa only [position] using invariant) shaped sourceSyntax bounds compiledFunctions functionTyping owned with host | operation
    · exact Or.inl (by simpa only [position] using host)
    · apply Or.inr
      apply WP.spec_mono operation
      intro out outcome
      simpa only [position] using outcome.widen program.fetchBound


end Exec.Theorems
