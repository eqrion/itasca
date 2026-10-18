import Exec.Theorems.Composition.Supported.SupportedBranchTableExecution
import Exec.Theorems.Composition.Supported.SupportedCumulativeDispatch
import Exec.Theorems.Composition.Supported.SupportedSimdExecution
import Exec.Theorems.Composition.Supported.SupportedTypedSelectExecution
import Exec.Interp.StructuredMachine.SupportedHead
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
theorem step_head_supported {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}
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
    (compiledFunctions : StructuredMachine.CompiledFunctions emission code store) (functionTyping : CoreFunctionsTyped view code store) (free : CoreHostFree store)
    (owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store)
      ⟨Store.decodeStore view code store,ambient,{f with code := op::after}::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SupportedStepOutcome emission allowed allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨Store.decodeStore view code store,ambient,{f with code:=op::after}::rest,[]⟩ out ⦄ := by
  cases head with
  | cumulative original =>
    exact step_head_supported_cumulative language memory hooks floats allocator correct allocation interrupts view laws code exec store platform
      index raw inst compiled C targets next output ambient f rest op after original last hf hi hc program slots moduleEq small point expected machine
      shaped sourceSyntax bounds compiledFunctions functionTyping free owned
  | simd operation =>
    exact step_simd_supported_execution memory hooks floats allocator view code laws correct exec store platform raw index inst compiled
      C targets next output ambient f rest op after expected last hf hi hc program slots point operation machine shaped sourceSyntax bounds
  | typedSelect declared =>
    exact step_typed_select_supported_execution memory hooks floats allocator exec store platform index raw inst compiled C targets next output
      view code ambient f rest declared after last hf hi hc slots point expected machine program shaped sourceSyntax bounds
  | branchTable depths fallback =>
    exact step_branch_table_supported language memory hooks floats allocator view code exec store platform
      index raw inst compiled C targets next output ambient f rest after depths fallback expected last hf hi hc
      program slots point machine shaped sourceSyntax bounds
end Exec.Theorems
