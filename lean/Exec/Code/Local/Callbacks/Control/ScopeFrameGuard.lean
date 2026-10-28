import Exec.Code.Local.Callbacks.Control.ScopeFramePatch
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Resolving another frame's IF guard preserves this scope's entry instruction. -/
theorem ScopeEntryCode.set_guard {code scope} (entry : ScopeEntryCode code scope)
    (guard : Usize) (condition old target : U32)
    (found : code[guard.val]? = some (.JumpIfZero condition old))
    (distinct : scope.guardPosition ≠ some guard.val) :
    ScopeEntryCode (code.set guard.val (.JumpIfZero condition target)) scope := by
  unfold ScopeEntryCode at *
  split at entry <;> try simp_all only
  · intro live
    have atEntry := entry live
    have away : guard.val ≠ scope.entry := by
      intro equal
      rw [equal, atEntry] at found
      cases found
    rw [List.getElem?_set_ne away]
    exact atEntry
  · intro live
    have away : guard.val ≠ scope.entry := by
      intro equal
      apply distinct
      simp_all [SourceScope.guardPosition]
    rw [List.getElem?_set_ne away]
    exact entry live

end Itasca.Runtime.Code
