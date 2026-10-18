import Exec.Interp.Core.Outcome
import Exec.Interp.Core.GlobalMutation
import Exec.Interp.Machines.Core.CoreHeadCoverage
import Exec.Interp.Machines.Core.CoreOrdinaryAdvance
import Exec.Interp.Core.NumericExecutionOwned
import Exec.Interp.Core.GlobalExecutionOwned
import Exec.Interp.Machines.Core.CoreFloatConstantExecutionOwned
import Exec.Interp.Machines.Core.CoreSelectExecutionOwned
import Exec.Interp.Memory.MemoryCoreExecutionOwned
import Exec.Interp.Machines.Core.CoreCallExecutionOwned
import Exec.Interp.Machines.Core.CoreReturnExecutionOwned
import Exec.Interp.Machines.Core.CoreUnreachableExecutionOwned
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt

theorem step_head_core {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.Instance)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (op : instr) (after : List instr)
    (head : CoreDispatchHead op)
    (compiledFunctions : CoreCompiledFunctions code store) (functionTyping : CoreFunctionsTyped view code store)
    (last : index.val+1 = exec.frames.length) (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (small : ∀ object ∈ store.globals.val, object.ty.valtype = .I32 ∨ object.ty.valtype = .F32 → object.lo.val < 2^32)
    (point : CoreFramePoint (Store.decodeStore view code store) raw {f with code := op::after} compiled C targets next output)
    (expected : List valtype)
    (machine : CoreExecution view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := op::after}::rest,[]⟩ expected raw.pc.val false) :
    CoreHostBoundary exec store ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      CoreOutcome allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨Store.decodeStore view code store,ambient,{f with code := op::after}::rest,[]⟩ out ⦄ := by
  cases head with
  | pure pureHead =>
    cases pureHead with
    | ordinary operation =>
      apply Or.inr
      apply WP.spec_mono (step_ordinary_core_advance memory hooks floats allocator view code exec store platform index raw inst compiled
        C targets next output ambient f rest operation after last hf hi hc program slots point expected machine)
      intro out effect
      exact CoreOutcome.unchanged_success effect.2.1 effect.1 effect.2.2.2
    | numeric operation =>
      apply Or.inr
      apply WP.spec_mono (step_numeric_core_execution_owned memory hooks floats allocator view code exec store platform index raw inst compiled
        C targets next output ambient f rest operation after last hf hi hc program slots point expected machine)
      intro out effect
      obtain ⟨sameStore,samePlatform,success | trapped⟩ := effect
      · obtain ⟨status,pc,g,machine,simulation,ownership,bounded⟩ := success
        exact CoreOutcome.unchanged_success sameStore status (.of_frame machine simulation ownership rfl bounded)
      · obtain ⟨trap,status,kind,count,positive,steps⟩ := trapped
        apply CoreOutcome.failure (by rw [sameStore]; exact .unchanged) status (by simp only [sameStore])
        exact Or.inl ⟨⟨trap,rfl,by rcases kind with rfl | rfl <;> simp [CoreTrap]⟩,count,positive,steps⟩
    | loop bt body =>
      apply Or.inr
      apply WP.spec_mono (step_loop_core_execution_owned memory hooks floats allocator interrupts platform index view code exec store raw inst compiled
        ambient f rest bt body after C targets next output hi slots last hf hc program point expected machine)
      intro out effect
      obtain ⟨sameStore,success | stopped⟩ := effect
      · obtain ⟨status,pc,g,pending,machine,simulation,ownership,bounded⟩ := success
        exact CoreOutcome.unchanged_success sameStore status (.of_frame machine simulation ownership rfl bounded)
      · apply CoreOutcome.failure (by rw [sameStore]; exact .unchanged) stopped.1 (by simp only [sameStore])
        exact Or.inr (Or.inl ⟨rfl,_,stopped.2⟩)
    | call functionIndex =>
      rcases step_call_core_execution_owned memory hooks floats allocator allocation interrupts view code exec store platform index raw inst compiled
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
          exact CoreOutcome.unchanged_success sameStore status ⟨pc,false,source,machine,simulation,ownership,ambientEq,bounded⟩
        | Err error =>
          apply CoreOutcome.failure (by rw [sameStore]; exact .unchanged) status (by simp only [sameStore])
          exact Or.inr (Or.inr ⟨index,raw,inst,compiled,last,hf,hi,hc,rejected error status⟩)
    | return_ =>
      apply Or.inr
      apply WP.spec_mono (step_return_core_execution_owned memory hooks floats allocator view code exec store platform index raw inst compiled
        C targets next output ambient f rest after last hf hi hc program slots point expected machine)
      intro out effect
      obtain ⟨status,sameStore,samePlatform,pc,source,machine,simulation,ownership,ambientEq,bounded⟩ := effect
      exact CoreOutcome.unchanged_success sameStore status ⟨pc,false,source,machine,simulation,ownership,ambientEq,bounded⟩
    | unreachable =>
      apply Or.inr
      apply WP.spec_mono (step_unreachable_core_execution_owned memory hooks floats allocator exec store platform index raw inst compiled
        C targets next output view code ambient f rest after last hf hi hc slots point expected machine program)
      intro out effect
      obtain ⟨sameStore,samePlatform,pc,frames,success | trapped⟩ := effect
      · obtain ⟨status,machine,simulation,ownership⟩ := success
        exact CoreOutcome.unchanged_success sameStore status (.of_frame machine simulation ownership rfl (fun _ h => h))
      · apply CoreOutcome.failure (by rw [sameStore]; exact .unchanged) trapped.1 (by simp only [sameStore])
        exact Or.inl ⟨⟨.Unreachable,rfl,by simp [CoreTrap]⟩,trapped.2⟩
  | float32 bits =>
    apply Or.inr
    apply WP.spec_mono (FloatConstant.step_float32_execution_owned memory hooks floats allocator exec store platform index raw inst compiled
      C targets next output view code ambient f rest (Builtins.floatOfBits 32 bits.val) after last hf hi hc slots point expected machine program)
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,g,machine,simulation,ownership,bounded⟩ := effect
    exact CoreOutcome.unchanged_success sameStore status (.of_frame machine simulation ownership rfl bounded)
  | float64 bits =>
    apply Or.inr
    apply WP.spec_mono (FloatConstant.step_float64_execution_owned memory hooks floats allocator exec store platform index raw inst compiled
      C targets next output view code ambient f rest (Builtins.floatOfBits 64 bits.val) after last hf hi hc slots point expected machine program)
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,g,machine,simulation,ownership,bounded⟩ := effect
    exact CoreOutcome.unchanged_success sameStore status (.of_frame machine simulation ownership rfl bounded)
  | select =>
    apply Or.inr
    apply WP.spec_mono (step_select_core_execution_owned memory hooks floats allocator exec store platform index raw inst compiled
      C targets next output view code ambient f rest after last hf hi hc slots point expected machine program)
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,g,machine,simulation,ownership,bounded⟩ := effect
    exact CoreOutcome.unchanged_success sameStore status (.of_frame machine simulation ownership rfl bounded)
  | globalGet globalIndex =>
    apply Or.inr
    apply WP.spec_mono (step_globalGet_core_execution_owned memory hooks floats allocator platform index view code exec store raw inst compiled
      ambient f rest after globalIndex.val C targets next output hi moduleEq slots last hf hc program small point expected machine)
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,g,machine,simulation,ownership,bounded⟩ := effect
    exact CoreOutcome.unchanged_success sameStore status (.of_frame machine simulation ownership rfl bounded)
  | globalSet globalIndex =>
    apply Or.inr
    have pcBound : raw.pc.val < U32.max := by
      rcases corePoint_globalSet_head globalIndex.val after point.code with ⟨target,forward,fetch,tail⟩ | operation
      · exact program.fetched_bound _ fetch
      · obtain ⟨ty,idx,src,front,indexEq,lookup,values,position,fetch,tail⟩ := operation
        exact program.fetched_bound _ fetch
    have mutation := coreFramePoint_globalSet_store_mutation memory hooks floats allocator platform index view code exec store raw inst compiled
      ambient f rest after globalIndex.val C targets next output hi moduleEq slots last hf hc pcBound point machine.typed
    obtain ⟨out,run,effect⟩ := WP.spec_imp_exists (step_globalSet_core_execution_owned memory hooks floats allocator platform index view code exec store raw inst compiled
      ambient f rest after globalIndex.val C targets next output hi moduleEq slots last hf hc program point expected machine)
    rw [run,WP.spec_ok] at mutation ⊢
    obtain ⟨status,samePlatform,metadata,extension,pc,g,machine,simulation,ownership,bounded⟩ := effect
    exact CoreOutcome.success mutation status (.of_frame machine simulation ownership rfl bounded)
  | load operation argument =>
    apply Or.inr
    apply WP.spec_mono (MemoryDescriptor.step_memory_load_execution_owned memory hooks floats allocator platform index view laws code exec store raw inst compiled
      ambient f rest after operation argument C targets next output hi moduleEq slots last hf hc point expected machine program)
    intro out effect
    obtain ⟨samePlatform,changed,metadata,extension,success | trapped⟩ := effect
    · have mutation : CoreStoreMutation view ⟨Store.decodeStore view code store,ambient,{f with code := operation.source argument::after}::rest,[]⟩ store out.2.2.1 := by
        rcases changed with same | ⟨address,object,issued,mutation⟩
        · rw [same]; exact .unchanged
        · exact .memory issued mutation
      obtain ⟨status,pc,g,machine,simulation,ownership,bounded⟩ := success
      exact CoreOutcome.success mutation status (.of_frame machine simulation ownership rfl bounded)
    · have mutation : CoreStoreMutation view ⟨Store.decodeStore view code store,ambient,{f with code := operation.source argument::after}::rest,[]⟩ store out.2.2.1 := by
        rcases changed with same | ⟨address,object,issued,mutation⟩
        · rw [same]; exact .unchanged
        · exact .memory issued mutation
      apply CoreOutcome.failure mutation trapped.1 trapped.2.1
      exact Or.inl ⟨⟨.MemoryOutOfBounds,rfl,by simp [CoreTrap]⟩,trapped.2.2⟩
  | store operation argument =>
    apply Or.inr
    apply WP.spec_mono (MemoryDescriptor.step_memory_store_execution_owned memory hooks floats allocator platform index view laws code exec store raw inst compiled
      ambient f rest after operation argument C targets next output hi moduleEq slots last hf hc point expected machine program)
    intro out effect
    obtain ⟨samePlatform,changed,metadata,extension,success | trapped⟩ := effect
    · have mutation : CoreStoreMutation view ⟨Store.decodeStore view code store,ambient,{f with code := operation.source argument::after}::rest,[]⟩ store out.2.2.1 := by
        rcases changed with same | ⟨address,object,issued,mutation⟩
        · rw [same]; exact .unchanged
        · exact .memory issued mutation
      obtain ⟨status,pc,g,machine,simulation,ownership,bounded⟩ := success
      exact CoreOutcome.success mutation status (.of_frame machine simulation ownership rfl bounded)
    · have mutation : CoreStoreMutation view ⟨Store.decodeStore view code store,ambient,{f with code := operation.source argument::after}::rest,[]⟩ store out.2.2.1 := by
        rcases changed with same | ⟨address,object,issued,mutation⟩
        · rw [same]; exact .unchanged
        · exact .memory issued mutation
      apply CoreOutcome.failure mutation trapped.1 trapped.2.1
      exact Or.inl ⟨⟨.MemoryOutOfBounds,rfl,by simp [CoreTrap]⟩,trapped.2.2⟩
end Exec.Interp
