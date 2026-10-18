import Exec.Theorems.Composition.Supported.SupportedReady
import Exec.Theorems.Composition.Supported.SupportedNormalizeOutcome
import Exec.Interp.StructuredMachine.NormalizeExecution
import Exec.Interp.StructuredMachine.PendingExecution
import Exec.Interp.StructuredMachine.SupportedControlSemantics
import Exec.Interp.StructuredMachine.ErasedHeads
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
theorem step_frame_supported {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}
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
    (compiledFunctions : StructuredMachine.CompiledFunctions emission code store) (functionTyping : CoreFunctionsTyped view code store) (free : CoreHostFree store)
    (owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store) ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SupportedStepOutcome emission allowed allocator hooks view code exec store platform expected compiled.code.length raw.pc.val pending
        ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ out ⦄ := by
  cases point with
  | jump target fetched continuation =>
    apply WP.spec_mono (StructuredMachine.step_pending_execution memory hooks floats allocator platform index view code exec store raw inst compiled
      ambient f rest C targets next output hi slots last hf hc program (.jump target fetched continuation) expected machine)
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,retained,simulation⟩ := effect
    exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status ⟨pc.val,false,_,retained,simulation,fun _ h=>h,rfl,fun _ h=>h⟩
  | ready point =>
    obtain ⟨count,g,labels,stop,types,chain,bound,represented,continuation,retained,metadata,done⟩ :=
      StructuredMachine.normalize_execution (StructuredMachine.supportedControlSemantics language) view code store exec raw index compiled C targets next output ambient f rest
        last hf program slots point expected machine
    have nextProgram : FrameProgram store raw compiled (g.locals.map Code.valueType) g.resultTypes C.FUNCS := program.reposition raw.pc metadata
    rcases done with skip | ready
    · obtain ⟨target,forward,fetched,tail⟩ := skip
      apply WP.spec_mono (StructuredMachine.step_forward_jump memory hooks floats allocator view code exec store platform index raw inst compiled
        ambient g rest expected C labels stop types target last hf hi hc forward fetched represented tail retained nextProgram)
      intro out effect
      have outcome := SupportedStepOutcome.unchanged_success (allocator:=allocator) (hooks:=hooks) (exec:=exec) (platform:=platform)
        shaped sourceSyntax bounds effect.2.1 effect.1
        ⟨target.val,false,_,effect.2.2.2.2.1,effect.2.2.2.2.2,fun _ h=>h,rfl,fun _ h=>h⟩
      exact outcome.prepend_normalization chain machine.typed.typed
    · have nextModule : g.module=Store.decodeInstance store inst := metadata.module.trans moduleEq
      apply WP.spec_mono (step_ready_supported language memory hooks floats allocator correct allocation interrupts view laws code exec store platform index raw inst compiled
        C labels stop types ambient g rest last hf hi hc nextProgram represented nextModule small continuation expected retained ready shaped sourceSyntax bounds compiledFunctions functionTyping free (chain.ownership.stateful owned))
      intro out outcome
      exact outcome.prepend_normalization chain machine.typed.typed
end Exec.Theorems
