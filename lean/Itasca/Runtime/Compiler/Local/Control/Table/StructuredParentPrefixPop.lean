import Itasca.Runtime.Compiler.Local.Control.Table.StructuredPrefixZipper
namespace Itasca.Runtime.Compiler

/-- Closing the current source scope exposes exactly its suspended parent and
the unchanged remainder of the source zipper. -/
theorem StructuredParentPrefixes.pop {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals code parents parent label labels child}
    (saved : StructuredParentPrefixes (jumpTables := jumpTables) emit types functions returns locals code (parents ++ [parent]) (label :: labels) child) :
    StructuredParentPrefixes (jumpTables := jumpTables) emit types functions returns locals code parents labels parent ∧
      ScopeLabel parent label ∧ child.entry ≤ code.length ∧
      StructuredParentPrefix (jumpTables := jumpTables) emit types functions returns locals code (label :: labels) parent child := by
  generalize physical : parents ++ [parent] = scopes at saved
  cases saved with
  | @push earlier outer previous prior inner current shape bound held =>
    have size : parents.length = earlier.length := by
      have lengths := congrArg List.length physical
      simp only [List.length_append, List.length_singleton] at lengths
      omega
    obtain ⟨sameParents, sameParent⟩ := List.append_inj physical size
    simp only [List.cons.injEq, and_true] at sameParent
    subst earlier previous
    exact ⟨prior, shape, bound, held⟩

end Itasca.Runtime.Compiler

