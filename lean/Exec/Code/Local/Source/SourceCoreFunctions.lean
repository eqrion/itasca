import Exec.Code.Local.Source.SourceCore
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem source_functions_core {raw : ModuleBinary.Module} (supported : ModuleCore raw) :
    ∀ source ∈ sourceFunctions raw, match source with
      | .HOST _ => False
      | .FUNC _ _ body => Forall Abs.CoreInstr body := by
  have all : ∀ (indices : List U32) (entries : List ModuleBinary.Code),
      (∀ entry ∈ entries, Forall Abs.CoreInstr entry.body) →
      ∀ source ∈ List.zipWith sourceFunctionCode indices entries, match source with
        | .HOST _ => False
        | .FUNC _ _ body => Forall Abs.CoreInstr body := by
    intro indices
    induction indices with
    | nil => simp
    | cons index indices ih =>
      intro entries known source member
      cases entries with
      | nil => simp at member
      | cons entry entries =>
        simp only [List.zipWith_cons_cons, List.mem_cons] at member
        rcases member with rfl | member
        · exact known entry (by simp)
        · exact ih entries (fun e he => known e (by simp [he])) source member
  exact all raw.functions raw.codes supported
end Exec.Code
