import Exec.Theorems.Composition.Supported.SupportedFrameStep
import Exec.Theorems.Composition.Supported.SupportedMeasure

namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

/-- Every active supported iteration returns normally. Successful steps
preserve the full execution invariant; errors retain precise causes. The fixed
U32 code bound is shared across all callees and resumed callers. -/
theorem step_supported {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}
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
    (compiledFunctions : StructuredMachine.CompiledFunctions emission code store) (functionTyping : CoreFunctionsTyped view code store) (free : CoreHostFree store)
    (owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store) source)
    (invariant : StructuredMachine.Execution emission (Abs.SupportedState allowed) view code store exec source expected pc pending)
    (active : 0 < exec.frames.length) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SupportedStepOutcome emission allowed allocator hooks view code exec store platform expected U32.max pc pending source out ⦄ := by
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
    apply WP.spec_mono (step_frame_supported language memory hooks floats allocator correct allocation interrupts view laws code exec store platform
      index raw inst compiled C targets next output ambient f rest
      last hf hi hc program current.slots moduleEq small pending point expected (by simpa only [position] using invariant) shaped sourceSyntax bounds compiledFunctions functionTyping free owned)
    intro out outcome
    simpa only [position] using outcome.widen program.fetchBound

end Exec.Theorems
