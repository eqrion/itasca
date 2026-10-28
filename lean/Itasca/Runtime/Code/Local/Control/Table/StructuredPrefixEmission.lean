import Itasca.Runtime.Code.Local.Control.Table.StructuredPrefix
import Itasca.Runtime.Code.Local.Relations.Common.Prefix
import Itasca.Runtime.Code.Local.Relations.Common.ResolvedPrefix
namespace Itasca.Runtime.Code
open Aeneas.Std

theorem StructuredPrefix.emit {jumpTables : List U32} {emission types functions returns locals code labels initial source start stack instruction emitted output}
    (prior : StructuredPrefix (jumpTables := jumpTables) emission types functions returns locals code labels initial source start code.length stack)
    (head : emission stack instruction emitted output)
    (ordinary : ∀ depths fallback, instruction ≠ .BR_TABLE depths fallback) :
    StructuredPrefix (jumpTables := jumpTables) emission types functions returns locals (code ++ emitted) labels initial (source ++ [instruction])
      start (code ++ emitted).length output := by
  have fragment : Segment (code ++ emitted) code.length emitted (code ++ emitted).length :=
    ⟨code, [], by simp, rfl, by simp⟩
  exact (prior.extend emitted).append (StructuredPrefix.linear head ordinary fragment)

/-- The prefix component of the compiler invariant, with physical open fixups
resolved through explicit future static targets. Control-frame/source-zipper
alignment is a separate component, not assumed by this record. -/
structure StructuredResolvedInv (jumpTables : List U32) (emission : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (labels : List LabelTarget) (groups : List FixupTarget)
    (initial : List valtype) (source : List instr) (start : Nat) (stack : List valtype) : Prop where
  localsEq : compilerLocals compiler = locals
  layout : CompilerLayout compiler stack
  inside : FixupsInside groups compiler.function.code.val.length
  code : StructuredPrefix (jumpTables := jumpTables) emission types functions returns locals (resolvedCode compiler.function.code.val groups)
    labels initial source start compiler.function.code.val.length stack

/-- Every checked ordinary callback extends the resolved structured prefix.
This consumes its literal emission theorem and typed slot operands. -/
theorem Lowered.structured_resolved_advance {jumpTables : List U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emission types functions returns locals labels groups initial source start stack instruction emitted output}
    (lowered : Lowered before after emitted output)
    (invariant : StructuredResolvedInv jumpTables emission before types functions returns locals labels groups initial source start stack)
    (head : emission stack instruction [emitted] output)
    (ordinary : ∀ depths fallback, instruction ≠ .BR_TABLE depths fallback) :
    StructuredResolvedInv jumpTables emission after types functions returns locals labels groups initial (source ++ [instruction]) start output := by
  refine ⟨lowered.2.2.1.trans invariant.localsEq, lowered.2.1, ?_, ?_⟩
  · intro group member site atSite
    have old := invariant.inside group member site atSite
    simp only [lowered.1, List.length_append, List.length_singleton]
    omega
  · have resolved := resolvedCode_append_code before.function.code.val [emitted] groups invariant.inside
    have sourceCode : StructuredPrefix (jumpTables := jumpTables) emission types functions returns locals (resolvedCode before.function.code.val groups)
        labels initial source start (resolvedCode before.function.code.val groups).length stack := by
      simpa only [resolvedCode_length] using invariant.code
    have advanced := sourceCode.emit head ordinary
    simpa only [lowered.1, resolved, List.length_append, resolvedCode_length] using advanced

end Itasca.Runtime.Code

