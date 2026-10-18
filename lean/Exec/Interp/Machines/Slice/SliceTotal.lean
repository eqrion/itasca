import Exec.Interp.Machines.Slice.SliceStep
import Exec.Interp.Machines.Slice.SliceMeasure

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Every active integer-slice iteration returns normally. Successful steps
preserve the full execution invariant; errors retain precise causes. The fixed
U32 code bound is shared across all callees and resumed callers. -/
theorem step_slice {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (source : Abs.AState) (expected : List valtype) (pc : Nat) (pending : Bool)
    (decoded : source.store = Store.decodeStore view code store)
    (compiledFunctions : CompiledFunctions code store)
    (invariant : SliceExecution store exec source expected pc pending)
    (active : 0 < exec.frames.length) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SliceOutcome allocator hooks exec store platform expected U32.max pc pending source out ⦄ := by
  rcases source with ⟨s, ambient, frames, results⟩
  cases frames with
  | nil =>
    have stack := invariant.stack
    cases stack with
    | empty empty => simp only [alloc.vec.Vec.length, empty, List.length_nil] at active; omega
  | cons f rest =>
    have noResults := invariant.typed.activeResults (by simp)
    change results = [] at noResults
    subst results
    obtain ⟨raw, compiled, functions, targets, next, output, top, position, program, point⟩ := invariant.cursor
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
    apply WP.spec_mono (step_slice_frame memory hooks floats allocator allocation interrupts view code exec store platform
      index raw inst compiled functions targets next output s ambient f rest expected decoded compiledFunctions
      last hf hi hc program current.binding current.slots pending point invariant.typed invariant.slice invariant.result invariant.stack)
    intro out outcome
    simpa only [position] using outcome.widen program.fetchBound

end Exec.Interp
