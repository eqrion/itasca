import Exec.Abs.Slice
import Itasca.Module.Soundness
import Itasca.Profile.BinaryUnique
import Itasca.Profile.EntrySound
import Exec.Code.Local.Source.SourceSlice
import Exec.Abs.Cumulative
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
def ModuleCumulative (raw : ModuleBinary.Module) : Prop :=
  ∀ entry ∈ raw.codes, Forall Abs.CumulativeInstr entry.body

/-- Exact input bytes admit an independent module grammar whose defined
function bodies belong to the supported slice. No compiler callback occurs. -/
def SourceCumulative (profile : ValidationProfile) (bytes : Slice U8) : Prop :=
  ∃ raw, ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile ∧ ModuleCumulative raw

theorem SourceCumulative.decoded {profile bytes raw}
    (supported : SourceCumulative profile bytes)
    (encoded : ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile) :
    ModuleCumulative raw := by
  obtain ⟨source, encoding, subset⟩ := supported
  have same := Profile.module_unique encoding encoded
  simpa only [same] using subset

theorem SourceCumulative.validated {profile bytes decoded}
    (supported : SourceCumulative profile bytes)
    (validated : ModuleSound.Validated bytes decoded profile) :
    ∃ raw, ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile ∧
      ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw) ∧
      ModuleElaboration.Matches decoded.env decoded.tail raw ∧ Module_ok (ModuleElaboration.moduleOf raw) ∧
      ModuleElaboration.Profile raw profile ∧ ModuleElaboration.AccessorTypes decoded.env raw ∧ ModuleCumulative raw := by
  obtain ⟨raw, encoded, elaborated, matched, typed, restrictions, accessors⟩ := validated
  exact ⟨raw, encoded, elaborated, matched, typed, restrictions, accessors, supported.decoded encoded⟩

end Exec.Code
