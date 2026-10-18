import Exec.Theorems.Composition.Uniform.UniformSupportedHeadHostSite
import Exec.Theorems.Composition.Uniform.UniformSupportedTransport
import Exec.Theorems.Composition.Uniform.UniformSupportedStateful
import Exec.Theorems.Composition.Uniform.UniformSupportedIndirect
import Exec.Theorems.Composition.Uniform.UniformSupportedSimdExecution
import Exec.Theorems.Composition.Uniform.UniformSupportedTypedSelect
import Exec.Theorems.Composition.Uniform.UniformSupportedBranchTable
import Exec.Interp.StructuredMachine.EpilogueUniform
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
theorem step_head_supported_cumulative_host_site_uniform {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}
    [∀ compiled, StructuredMachine.FloatHeads (emission compiled)]
    [∀ compiled, StructuredMachine.OrdinaryHeads (emission compiled)]
    [∀ compiled, StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.IndirectProjection (emission compiled) compiled.indirect.val]
    (language : Abs.Supported.Language allowed) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.Instance)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (op : instr) (after : List instr)
    (head : CumulativeDispatchHead op)
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
    (compiledFunctions : StructuredMachine.CompiledFunctions emission code store) (functionTyping : CoreFunctionsTyped view code store)
    (owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store)
      ⟨Store.decodeStore view code store,ambient,{f with code := op::after}::rest,[]⟩) :
    StructuredHostSite emission allowed view code exec store expected raw.pc.val false ⟨Store.decodeStore view code store,ambient,{f with code:=op::after}::rest,[]⟩ ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      UniformSupportedStepOutcome emission allowed allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨Store.decodeStore view code store,ambient,{f with code:=op::after}::rest,[]⟩ out ⦄ := by
  cases head with
  | core head =>
    rcases step_head_supported_base_site_uniform language memory hooks floats allocator allocation interrupts view laws code exec store platform index raw inst compiled C targets next output
      ambient f rest op after head last hf hi hc program slots moduleEq small point expected machine shaped sourceSyntax bounds compiledFunctions functionTyping owned with host | result
    · exact Or.inl (.ready ⟨index,raw,inst,compiled,C,targets,next,output,last,hf,hi,hc,program,slots,moduleEq,point,machine,owned.values⟩ (Or.inl host))
    · exact Or.inr result
  | scalar operation =>
    apply Or.inr
    apply WP.spec_mono (step_scalar_supported_execution_uniform language memory hooks floats allocator correct exec store platform index raw inst compiled C targets next output
      view code ambient f rest operation after last hf hi hc slots point expected machine program shaped sourceSyntax bounds)
    intro out result
    exact result.2.2
  | stateful operation =>
    apply Or.inr
    exact stateful_execution_supported_uniform language memory hooks floats allocator allocation view laws code exec store platform index raw inst compiled C targets next output
      ambient f rest after operation last hf hi hc moduleEq slots point expected machine program shaped sourceSyntax bounds owned
  | indirect table type =>
    rcases step_indirect_supported_execution_uniform language memory hooks floats allocator allocation interrupts view code exec store platform index raw inst compiled C targets next output
      ambient f rest table type after last hf hi hc moduleEq program slots point expected machine shaped compiledFunctions functionTyping with host | operation
    · exact Or.inl (.ready ⟨index,raw,inst,compiled,C,targets,next,output,last,hf,hi,hc,program,slots,moduleEq,point,machine,owned.values⟩ (Or.inr ⟨table,type,rfl,host⟩))
    · apply Or.inr
      apply WP.spec_mono operation
      intro out result
      cases status : out.1 with
      | Ok unit =>
        cases unit
        exact UniformSupportedStepOutcome.unchanged_success shaped sourceSyntax bounds result.1 status (result.2.1 status)
      | Err error =>
        apply UniformSupportedStepOutcome.failure (by rw [result.1];exact .refl_of_shape shaped sourceSyntax bounds) status (by simp only [result.1])
        rcases result.2.2 error status with ⟨⟨trap,errorEq,kind⟩,steps⟩ | cause
        · exact Or.inl ⟨⟨trap,errorEq,Or.inr kind⟩,steps⟩
        · exact Or.inr (Or.inr ⟨index,raw,inst,compiled,last,hf,hi,hc,Or.inr ⟨code,cause⟩⟩)

theorem step_head_supported_host_site_uniform {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}
    [∀ compiled, StructuredMachine.FloatHeads (emission compiled)]
    [∀ compiled, StructuredMachine.OrdinaryHeads (emission compiled)]
    [∀ compiled, StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.IndirectProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.SimdProjection (emission compiled) compiled.simd.val compiled.v128_pool.val]
    [∀ compiled, StructuredMachine.TypedSelectHeads (emission compiled)]
    (language : Abs.Supported.Language allowed) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.Instance)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (op : instr) (after : List instr)
    (head : SupportedDispatchHead op)
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
    (compiledFunctions : StructuredMachine.CompiledFunctions emission code store) (functionTyping : CoreFunctionsTyped view code store)
    (owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store)
      ⟨Store.decodeStore view code store,ambient,{f with code := op::after}::rest,[]⟩) :
    StructuredHostSite emission allowed view code exec store expected raw.pc.val false ⟨Store.decodeStore view code store,ambient,{f with code:=op::after}::rest,[]⟩ ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      UniformSupportedStepOutcome emission allowed allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨Store.decodeStore view code store,ambient,{f with code:=op::after}::rest,[]⟩ out ⦄ := by
  cases head with
  | cumulative original =>
    exact step_head_supported_cumulative_host_site_uniform language memory hooks floats allocator correct allocation interrupts view laws code exec store platform
      index raw inst compiled C targets next output ambient f rest op after original last hf hi hc program slots moduleEq small point expected machine
      shaped sourceSyntax bounds compiledFunctions functionTyping owned
  | simd operation =>
    apply Or.inr
    exact step_simd_supported_execution_uniform memory hooks floats allocator view code laws correct exec store platform raw index inst compiled
      C targets next output ambient f rest op after expected last hf hi hc program slots point operation machine shaped sourceSyntax bounds
  | typedSelect declared =>
    apply Or.inr
    exact step_typed_select_supported_execution_uniform memory hooks floats allocator exec store platform index raw inst compiled C targets next output
      view code ambient f rest declared after last hf hi hc slots point expected machine program shaped sourceSyntax bounds
  | branchTable depths fallback =>
    apply Or.inr
    exact step_branch_table_supported_uniform language memory hooks floats allocator view code exec store platform
      index raw inst compiled C targets next output ambient f rest after depths fallback expected last hf hi hc
      program slots point machine shaped sourceSyntax bounds

theorem step_ready_supported_host_site_uniform {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}
    [∀ compiled, StructuredMachine.FloatHeads (emission compiled)]
    [∀ compiled, StructuredMachine.OrdinaryHeads (emission compiled)]
    [∀ compiled, StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.IndirectProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.SimdProjection (emission compiled) compiled.simd.val compiled.v128_pool.val]
    [∀ compiled, StructuredMachine.TypedSelectHeads (emission compiled)]
    [∀ compiled, StructuredMachine.SupportedHeads (emission compiled)]
    (language : Abs.Supported.Language allowed) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.Instance)
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
    (point : StructuredMachine.FramePoint emission (Store.decodeStore view code store) raw f compiled C targets next output)
    (expected : List valtype)
    (machine : StructuredMachine.Execution emission (Abs.SupportedState allowed) view code store exec ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ expected raw.pc.val false)
    (ready : ReadySource f)
    (shaped : Store.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store)
    (compiledFunctions : StructuredMachine.CompiledFunctions emission code store) (functionTyping : CoreFunctionsTyped view code store)
    (owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store) ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩) :
    StructuredHostSite emission allowed view code exec store expected raw.pc.val false ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      UniformSupportedStepOutcome emission allowed allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ out ⦄ := by
  cases source : f.code with
  | nil =>
    apply Or.inr
    have labels : f.labels=[] := by simpa only [ReadySource,source] using ready
    have same : {f with code:=[],labels:=[]}=f := by rw [←source,←labels]
    apply WP.spec_mono (StructuredMachine.step_function_end_execution_uniform StructuredMachine.supportedReturnSemantics memory hooks floats allocator view code exec store platform index raw inst compiled
      C targets next output ambient f rest last hf hi hc program slots (by simpa only [same] using point) expected (by simpa only [same] using machine))
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,nextSource,fresh,simulation,uniform,ownership,ambientEq,bounded⟩ := effect
    apply UniformSupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status
    exact ⟨pc,false,nextSource,fresh,by simpa only [same] using simulation,by simpa only [same] using uniform,by simpa only [same] using ownership,ambientEq,by simpa only [same] using bounded⟩
  | cons op after =>
    have same : {f with code:=op::after}=f := by rw [←source]
    have head := StructuredMachine.frame_head_coverage point ready op after source
    have result := step_head_supported_host_site_uniform language memory hooks floats allocator correct allocation interrupts view laws code exec store platform index raw inst compiled C targets next output
      ambient f rest op after head last hf hi hc program slots moduleEq small (by simpa only [same] using point) expected
      (by simpa only [same] using machine) shaped sourceSyntax bounds compiledFunctions functionTyping (by simpa only [same] using owned)
    simpa only [same] using result

theorem step_frame_supported_host_site_uniform {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}
    [∀ compiled, StructuredMachine.FloatHeads (emission compiled)]
    [∀ compiled, StructuredMachine.OrdinaryHeads (emission compiled)]
    [∀ compiled, StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.IndirectProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.SimdProjection (emission compiled) compiled.simd.val compiled.v128_pool.val]
    [∀ compiled, StructuredMachine.TypedSelectHeads (emission compiled)]
    [∀ compiled, StructuredMachine.SupportedHeads (emission compiled)]
    [∀ compiled, StructuredMachine.ErasedHeads (emission compiled)]
    (language : Abs.Supported.Language allowed) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.Instance)
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
    (point : StructuredMachine.ControlPoint emission (Store.decodeStore view code store) raw f compiled C targets next output pending)
    (expected : List valtype)
    (machine : StructuredMachine.Execution emission (Abs.SupportedState allowed) view code store exec ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ expected raw.pc.val pending)
    (shaped : Store.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store)
    (compiledFunctions : StructuredMachine.CompiledFunctions emission code store) (functionTyping : CoreFunctionsTyped view code store)
    (owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store) ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩) :
    StructuredHostSite emission allowed view code exec store expected raw.pc.val pending ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      UniformSupportedStepOutcome emission allowed allocator hooks view code exec store platform expected compiled.code.length raw.pc.val pending
        ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ out ⦄ := by
  cases point with
  | jump target fetched continuation =>
    apply Or.inr
    apply WP.spec_mono (StructuredMachine.step_pending_execution memory hooks floats allocator platform index view code exec store raw inst compiled
      ambient f rest C targets next output hi slots last hf hc program (.jump target fetched continuation) expected machine)
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,retained,simulation⟩ := effect
    exact UniformSupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status ⟨pc.val,false,_,retained,simulation,UniformConcreteSim.pending _ _ _,fun _ h=>h,rfl,fun _ h=>h⟩
  | ready point =>
    obtain ⟨count,g,labels,stop,types,chain,bound,represented,continuation,retained,metadata,done⟩ :=
      StructuredMachine.normalize_execution (StructuredMachine.supportedControlSemantics language) view code store exec raw index compiled C targets next output ambient f rest
        last hf program slots point expected machine
    have nextProgram : FrameProgram store raw compiled (g.locals.map Code.valueType) g.resultTypes C.FUNCS := program.reposition raw.pc metadata
    rcases done with skip | ready
    · obtain ⟨target,forward,fetched,tail⟩ := skip
      apply Or.inr
      apply WP.spec_mono (StructuredMachine.step_forward_jump memory hooks floats allocator view code exec store platform index raw inst compiled
        ambient g rest expected C labels stop types target last hf hi hc forward fetched represented tail retained nextProgram)
      intro out effect
      have outcome := UniformSupportedStepOutcome.unchanged_success (allocator:=allocator) (hooks:=hooks) (exec:=exec) (platform:=platform)
        shaped sourceSyntax bounds effect.2.1 effect.1
        ⟨target.val,false,_,effect.2.2.2.2.1,effect.2.2.2.2.2,effect.2.2.2.2.2.uniform_forward forward (by scalar_tac),fun _ h=>h,rfl,fun _ h=>h⟩
      exact outcome.prepend_normalization chain machine.typed.typed
    · have nextModule : g.module=Store.decodeInstance store inst := metadata.module.trans moduleEq
      rcases step_ready_supported_host_site_uniform language memory hooks floats allocator correct allocation interrupts view laws code exec store platform index raw inst compiled
        C labels stop types ambient g rest last hf hi hc nextProgram represented nextModule small continuation expected retained ready shaped sourceSyntax bounds compiledFunctions functionTyping (chain.ownership.stateful owned) with host | operation
      · exact Or.inl (.normalize chain host)
      · apply Or.inr
        apply WP.spec_mono operation
        intro out outcome
        exact outcome.prepend_normalization chain machine.typed.typed

theorem step_supported_host_site_uniform {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}
    [∀ compiled, StructuredMachine.FloatHeads (emission compiled)]
    [∀ compiled, StructuredMachine.OrdinaryHeads (emission compiled)]
    [∀ compiled, StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.IndirectProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.SimdProjection (emission compiled) compiled.simd.val compiled.v128_pool.val]
    [∀ compiled, StructuredMachine.TypedSelectHeads (emission compiled)]
    [∀ compiled, StructuredMachine.SupportedHeads (emission compiled)]
    [∀ compiled, StructuredMachine.ErasedHeads (emission compiled)]
    (language : Abs.Supported.Language allowed) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (source : Abs.AState) (expected : List valtype) (pc : Nat) (pending : Bool)
    (decoded : source.store = Store.decodeStore view code store)
    (shaped : Store.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store)
    (compiledFunctions : StructuredMachine.CompiledFunctions emission code store) (functionTyping : CoreFunctionsTyped view code store)
    (owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store) source)
    (invariant : StructuredMachine.Execution emission (Abs.SupportedState allowed) view code store exec source expected pc pending)
    (active : 0 < exec.frames.length) :
    StructuredHostSite emission allowed view code exec store expected pc pending source ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      UniformSupportedStepOutcome emission allowed allocator hooks view code exec store platform expected U32.max pc pending source out ⦄ := by
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
    rcases step_frame_supported_host_site_uniform language memory hooks floats allocator correct allocation interrupts view laws code exec store platform
      index raw inst compiled C targets next output ambient f rest
      last hf hi hc program current.slots moduleEq small pending point expected (by simpa only [position] using invariant) shaped sourceSyntax bounds compiledFunctions functionTyping owned with host | operation
    · exact Or.inl (by simpa only [position] using host)
    · apply Or.inr
      apply WP.spec_mono operation
      intro out outcome
      simpa only [position] using outcome.widen program.fetchBound


end Exec.Theorems
