import Itasca.Runtime.Compiler.Local.Capacity.SimdCapacity
import Itasca.Runtime.Interp.Relations.Capacity

/-!
Frame-capacity bounds for SIMD operands and results.

Main declarations: `simd_frame_capacity`. A direct consumer is `Interp.Simd.Execution.FrameRetention`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem simd_frame_capacity (slots : Slice U64) (base : Usize) (count a dst wa wb wc wr : U32)
    (frame : base.val + count.val ≤ slots.length)
    (input : a.val + wa.val + wb.val + wc.val ≤ count.val)
    (output : dst.val + wr.val ≤ count.val) :
    base.val + a.val + wa.val + wb.val ≤ Usize.max ∧
    (wc = 2#u32 → base.val + a.val + wa.val + wb.val < Usize.max) ∧
    base.val + dst.val + wr.val ≤ slots.length := by
  refine ⟨?_,?_,?_⟩
  · scalar_tac
  · intro two; scalar_tac
  · omega
end Itasca.Runtime.Interp
