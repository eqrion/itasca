import Exec.Code.Local.Source.SourceFunctionTyping
import Exec.Store.Invariant.FunctionTables
import Exec.Store.Invariant.Syntax
namespace Exec.Store
open Aeneas Aeneas.Std Itasca

theorem decodeNameChars_source (bytes : List U8) :
    decodeNameChars bytes = ModuleBinary.decodeChars bytes := by
  induction bytes using decodeNameChars.induct <;>
    (try simp only [decodeNameChars, ModuleBinary.decodeChars]) <;>
    (try simp_all only [ite_false])
  all_goals
    unfold decodeNameChars ModuleBinary.decodeChars
    simp_all only [ite_true, ite_false]

theorem decodeName_source (bytes : List U8) :
    decodeName bytes = ModuleBinary.nameOfBytes bytes := by
  simp only [decodeName, ModuleBinary.nameOfBytes, decodeNameChars_source]

/-- Canonical source typing supplies the syntax for an installed instance. -/
theorem instance_syntax_source (oldCode : CodeInterpretation) (fresh : Nat)
    (inst : runtime.store.Instance) (raw : ModuleBinary.Module)
    (elaborates : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw))
    (typed : Module_ok (ModuleElaboration.moduleOf raw))
    (matched : ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw) :
    InstanceSyntax (installCode oldCode fresh (Code.sourceFunctions raw)) fresh inst := by
  constructor
  · intro entry member
    rw [decodeName_source]
    have exports := congrArg ModuleBinary.Module.exports matched.1
    simp only [ModuleElaboration.fromEnv] at exports
    exact Code.source_export_name_wf elaborates typed (ModuleEnv.rawExport entry)
      (by rw [exports]; exact List.mem_map.mpr ⟨entry, member, rfl⟩)
  · intro function bound
    have functions := congrArg ModuleBinary.Module.functions matched.1
    simp only [ModuleElaboration.fromEnv] at functions
    have length : (Code.sourceFunctions raw).length = raw.functions.length := by
      simp only [Code.sourceFunctions, List.length_zipWith, elaborates.code_count, Nat.min_self]
    have sourceBound : function < (Code.sourceFunctions raw).length := by
      rw [length, functions]; exact bound
    let source := (Code.sourceFunctions raw)[function]
    have found : (Code.sourceFunctions raw)[function]? = some source :=
      List.getElem?_eq_some_iff.mpr ⟨sourceBound, rfl⟩
    rw [installCode_lookup oldCode fresh _ inst.module function source found]
    exact Code.source_functions_wf elaborates typed source (List.mem_of_getElem? found)

/-- Changing instance maps leaves its source syntax unchanged. -/
theorem InstanceSyntax.module_eq {code : CodeInterpretation} {index : Nat}
    {before after : runtime.store.Instance} (hsyntax : InstanceSyntax code index before)
    (same : after.module = before.module) : InstanceSyntax code index after := by
  exact ⟨by simpa only [same] using hsyntax.exportNames,
    by simpa only [same] using hsyntax.functionCodes⟩

/-- Reinterpreting only fresh instance keys preserves all old syntax. -/
theorem StoreSyntax.code_agrees {M : Type} {store : runtime.store.Store M}
    {before after : CodeInterpretation} (hsyntax : StoreSyntax before store)
    (agrees : CodeAgreesOn store before after) : StoreSyntax after store := by
  intro index inst found
  exact ⟨(hsyntax index inst found).exportNames, fun function bound => by
    rw [agrees index inst found function]
    exact (hsyntax index inst found).functionCodes function bound⟩

/-- Publishing one instance preserves the syntax of every existing instance. -/
theorem StoreSyntax.publish {M : Type} {before after : runtime.store.Store M}
    {oldCode newCode : CodeInterpretation} (prior : StoreSyntax oldCode before)
    (agrees : CodeAgreesOn before oldCode newCode) (inst : runtime.store.Instance)
    (appended : after.instances.val = before.instances.val ++ [inst])
    (fresh : InstanceSyntax newCode before.instances.length inst) :
    StoreSyntax newCode after := by
  have old := prior.code_agrees agrees
  intro index value found
  by_cases bound : index < before.instances.length
  · have retained : before.instances.val[index]? = some value := by
      simpa only [appended, List.getElem?_append_left bound] using found
    exact old index value retained
  · have selected : index = before.instances.length := by
      have inbounds := (List.getElem?_eq_some_iff.mp found).1
      simp only [appended, List.length_append, List.length_singleton] at inbounds
      change index < before.instances.length + 1 at inbounds
      omega
    subst index
    have equal : value = inst := by
      simpa [appended] using found.symm
    subst value
    exact fresh

/-- Store content updates do not affect the retained source syntax. -/
theorem StoreSyntax.instances_eq {M : Type} {before after : runtime.store.Store M}
    {code : CodeInterpretation} (prior : StoreSyntax code before)
    (same : after.instances = before.instances) : StoreSyntax code after := by
  simpa only [StoreSyntax, same] using prior

/-- Staging may update the fresh instance's maps while old instances remain
an exact prefix. Source syntax depends only on the retained module. -/
theorem StoreSyntax.staged {M : Type} {before after : runtime.store.Store M}
    {oldCode newCode : CodeInterpretation} (prior : StoreSyntax oldCode before)
    (agrees : CodeAgreesOn before oldCode newCode) (retained : StagedPrefix before after)
    (count : after.instances.length ≤ before.instances.length + 1)
    (fresh : ∀ inst, after.instances.val[before.instances.length]? = some inst →
      InstanceSyntax newCode before.instances.length inst) : StoreSyntax newCode after := by
  intro index inst found
  by_cases bound : index < before.instances.length
  · have same := congrArg (fun values : List runtime.store.Instance => values[index]?) retained.instances
    have oldFound : before.instances.val[index]? = some inst := by
      simpa only [List.getElem?_take, if_pos bound, found] using same.symm
    exact prior.code_agrees agrees index inst oldFound
  · have room := (List.getElem?_eq_some_iff.mp found).1
    change index < after.instances.length at room
    have equal : index = before.instances.length := by omega
    subst index
    exact fresh inst found

end Exec.Store
