import Exec.Abs.Slice
import Itasca.Module.Soundness
import Itasca.Profile.BinaryUnique
import Itasca.Profile.EntrySound
import Exec.Code.Local.Source.SourceSlice
import Exec.Abs.FloatCoreState
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
def ModuleFloatCore (raw : ModuleBinary.Module) : Prop :=
  ∀ entry ∈ raw.codes, Forall Abs.FloatCoreInstr entry.body

/-- Exact input bytes admit an independent module grammar whose defined
function bodies belong to the supported slice. No compiler callback occurs. -/
def SourceFloatCore (profile : ValidationProfile) (bytes : Slice U8) : Prop :=
  ∃ raw, ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile ∧ ModuleFloatCore raw

theorem SourceFloatCore.decoded {profile bytes raw}
    (supported : SourceFloatCore profile bytes)
    (encoded : ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile) :
    ModuleFloatCore raw := by
  obtain ⟨source, encoding, subset⟩ := supported
  have same := Profile.module_unique encoding encoded
  simpa only [same] using subset

theorem SourceFloatCore.validated {profile bytes decoded}
    (supported : SourceFloatCore profile bytes)
    (validated : ModuleSound.Validated bytes decoded profile) :
    ∃ raw, ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile ∧
      ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw) ∧
      ModuleElaboration.Matches decoded.env decoded.tail raw ∧ Module_ok (ModuleElaboration.moduleOf raw) ∧
      ModuleElaboration.Profile raw profile ∧ ModuleElaboration.AccessorTypes decoded.env raw ∧ ModuleFloatCore raw := by
  obtain ⟨raw, encoded, elaborated, matched, typed, restrictions, accessors⟩ := validated
  exact ⟨raw, encoded, elaborated, matched, typed, restrictions, accessors, supported.decoded encoded⟩

end Exec.Code
