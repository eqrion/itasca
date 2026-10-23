import Exec.Interp.Relations.SourceValueCauses
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Actual allocator refusals at entry retain source-bounded request sizes. -/
theorem CallCause.source_allocation {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {base : Usize}
    {compiled : runtime.bytecode.CompiledFunction} {words : Nat}
    (bound : compiled.slot_count.val ≤ words)
    (cause : CallCause allocator hooks exec store platform base compiled (.Exhausted .Allocation)) :
    (∃ n : Usize, n.val ≤ base.val + words ∧ allocator.reserve exec.slots n = .ok (false, exec.slots)) ∨
      allocator.reserve exec.frames 1#usize = .ok (false, exec.frames) := by
  rcases cause with ⟨needed, n, amount, refused⟩ | refused
  · exact Or.inl ⟨n, by omega, refused⟩
  · exact Or.inr refused

end Exec.Interp
