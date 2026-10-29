import Itasca.Runtime.Compiler.Local.Control.Table.StructuredUniversalPrefix
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalPrefix
namespace Itasca.Runtime.Code
open Aeneas.Std

theorem StructuredPrefix.emit_call {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals code labels initial source start front params results}
    (prior : StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals code labels initial source start code.length (front ++ params))
    (index base : U32)
    (signature : functions[index.val]? = some ⟨.mk_list params, .mk_list results⟩)
    (arguments : base.val = slots locals + slots front) :
    StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals (code ++ [runtime.bytecode.Instr.Call index base]) labels initial
      (source ++ [.CALL (.mk_uN index.val)]) start (code ++ [runtime.bytecode.Instr.Call index base]).length (front ++ results) := by
  have fetched : (code ++ [runtime.bytecode.Instr.Call index base])[code.length]? = some (runtime.bytecode.Instr.Call index base) := by simp
  simpa only [List.length_append, List.length_singleton] using
    (prior.extend [runtime.bytecode.Instr.Call index base]).append (StructuredPrefix.call signature arguments fetched)

theorem Lowered.structured_resolved_call {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals labels groups initial source start front params results index base}
    (lowered : Lowered before after (.Call index base) (front ++ results))
    (invariant : StructuredResolvedInv (jumpTables := jumpTables) emit before types functions returns locals labels groups initial source start (front ++ params))
    (signature : functions[index.val]? = some ⟨.mk_list params, .mk_list results⟩)
    (arguments : base.val = slots locals + slots front) :
    StructuredResolvedInv (jumpTables := jumpTables) emit after types functions returns locals labels groups initial
      (source ++ [.CALL (.mk_uN index.val)]) start (front ++ results) := by
  refine ⟨lowered.2.2.1.trans invariant.localsEq, lowered.2.1, ?_, ?_⟩
  · intro group member site atSite
    have old := invariant.inside group member site atSite
    simp only [lowered.1, List.length_append, List.length_singleton]
    omega
  · have resolved := resolvedCode_append_code before.function.code.val [runtime.bytecode.Instr.Call index base] groups invariant.inside
    have prior : StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals (resolvedCode before.function.code.val groups)
        labels initial source start (resolvedCode before.function.code.val groups).length (front ++ params) := by
      simpa only [resolvedCode_length] using invariant.code
    have advanced := prior.emit_call index base signature arguments
    simpa only [lowered.1, resolved, List.length_append, resolvedCode_length] using advanced

/-- A direct-call callback advances every pending source/control prefix using
only the source signature and actual argument-base coordinate. -/
theorem Lowered.structured_universal_call {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current front params results index base}
    (lowered : Lowered before after (.Call index base) (front ++ results))
    (frames : after.frames = before.frames)
    (invariant : StructuredUniversalPrefix (jumpTables := jumpTables) emit before types functions returns locals parents current (front ++ params))
    (signature : functions[index.val]? = some ⟨.mk_list params, .mk_list results⟩)
    (arguments : base.val = slots locals + slots front) :
    StructuredUniversalPrefix (jumpTables := jumpTables) emit after types functions returns locals parents
      (current.advance (.CALL (.mk_uN index.val))) (front ++ results) := by
  have codeEq := lowered.1
  have lengthOrder : before.function.code.val.length ≤ after.function.code.val.length := by simp [codeEq]
  refine ⟨lowered.2.2.1.trans invariant.localsEq, lowered.2.1, ?_, ?_⟩
  · intro frame member
    rw [frames] at member
    simpa only [codeEq] using (invariant.sites frame member).extend [runtime.bytecode.Instr.Call index base]
  · intro label labels groups plans shape parentShapes
    have oldPlans : FramePlans before.function.code.val.length locals before.frames.val (label :: labels) groups := by
      rw [← frames]
      exact plans.before lengthOrder
    have oldShape : ScopeLabel current label :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    have old := invariant.resolved oldPlans oldShape parentShapes
    have next := lowered.structured_resolved_call old signature arguments
    have saved := (invariant.prefixes label labels groups oldPlans oldShape parentShapes).1
    have resolved := resolvedCode_append_code before.function.code.val [runtime.bytecode.Instr.Call index base] groups old.inside
    refine ⟨?_, next.code⟩
    simpa only [codeEq, resolved] using
      (saved.extend [runtime.bytecode.Instr.Call index base]).advance_current (.CALL (.mk_uN index.val))

end Itasca.Runtime.Code

