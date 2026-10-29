import Itasca.Module.Elab.TypingInversion
import Itasca.Runtime.Compiler.Local.Source.SourceSlice
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Generated function typing also supplies the runtime function-code syntax.
The two generated datatypes use the same source fields. -/
theorem function_code_wf {C index locals body type}
    (typed : Func_ok C (.FUNC index locals body) type) :
    wf_funccode (.FUNC index locals body) := by
  have wfSource : wf_func (.FUNC index locals body) := by cases typed; assumption
  cases wfSource
  constructor <;> assumption

/-- The independently decoded module determines each defined source function's
actual type. This is a projection of generated module typing. -/
theorem source_function_typed {raw : ModuleBinary.Module}
    (elaborates : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw))
    (typed : Module_ok (ModuleElaboration.moduleOf raw))
    (position : Nat) (index : U32) (entry : ModuleBinary.Code)
    (indexFound : raw.functions[position]? = some index)
    (entryFound : raw.codes[position]? = some entry) :
    Func_ok (ModuleElaboration.contextOf raw) (CodeEntry.function index entry)
      (ModuleElaboration.functionType raw.types index) := by
  have paired := (ModuleElaboration.sections_of_typing elaborates typed).functions
  have left := (List.getElem?_eq_some_iff.mp indexFound).1
  have right := (List.getElem?_eq_some_iff.mp entryFound).1
  have result := paired.get left right
  simpa only [List.get_eq_getElem, (List.getElem?_eq_some_iff.mp indexFound).2,
    (List.getElem?_eq_some_iff.mp entryFound).2] using result

/-- Every export name of a typed source module has generated Unicode syntax. -/
theorem source_export_name_wf {raw : ModuleBinary.Module}
    (elaborates : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw))
    (typed : Module_ok (ModuleElaboration.moduleOf raw))
    (entry : ModuleBinary.Export) (member : entry ∈ raw.exports) :
    wf_name (ModuleBinary.nameOfBytes entry.name) := by
  obtain ⟨ty, checked⟩ := (ModuleElaboration.sections_of_typing elaborates typed).exports entry member
  have wfExport : wf_export (ModuleElaboration.exportDecl entry) := by cases checked; assumption
  cases wfExport
  assumption

/-- Every retained source function has the generated typing derivation selected
by the independent module's type-index vector. -/
theorem source_functions_typed {raw : ModuleBinary.Module}
    (elaborates : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw))
    (typed : Module_ok (ModuleElaboration.moduleOf raw)) :
    ∀ source ∈ sourceFunctions raw, ∃ index locals body type,
      source = .FUNC index locals body ∧ Func_ok (ModuleElaboration.contextOf raw) (.FUNC index locals body) type := by
  have all : ∀ {indices entries}, List.Forall₂
      (fun index entry => Func_ok (ModuleElaboration.contextOf raw) (CodeEntry.function index entry)
        (ModuleElaboration.functionType raw.types index)) indices entries →
      ∀ source ∈ List.zipWith CodeEntry.function indices entries,
        ∃ type, Func_ok (ModuleElaboration.contextOf raw) source type := by
    intro indices entries paired
    induction paired with
    | nil => simp
    | cons first rest ih =>
      intro source member
      simp only [List.zipWith_cons_cons, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨_, first⟩
      · exact ih source member
  intro source member
  rw [sourceFunctions_eq] at member
  obtain ⟨function, found, rfl⟩ := List.mem_map.mp member
  obtain ⟨type, checked⟩ := all (ModuleElaboration.sections_of_typing elaborates typed).functions function found
  cases function with
  | FUNC index locals body => exact ⟨index, locals, body, type, rfl, checked⟩

theorem source_functions_wf {raw : ModuleBinary.Module}
    (elaborates : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw))
    (typed : Module_ok (ModuleElaboration.moduleOf raw)) :
    Forall wf_funccode (sourceFunctions raw) := by
  intro source member
  obtain ⟨index, locals, body, type, rfl, checked⟩ := source_functions_typed elaborates typed source member
  exact function_code_wf checked

end Itasca.Runtime.Code
