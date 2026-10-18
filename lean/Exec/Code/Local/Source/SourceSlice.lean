import Exec.Abs.Slice
import Itasca.Module.Soundness
import Itasca.Profile.BinaryUnique
import Itasca.Profile.EntrySound
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- The supported source subset is a predicate on independently decoded code
entries, including every nested instruction through `SliceInstr`. -/
def ModuleSlice (raw : ModuleBinary.Module) : Prop :=
  ∀ entry ∈ raw.codes, Forall Abs.SliceInstr entry.body

/-- Exact input bytes admit an independent module grammar whose defined
function bodies belong to the supported slice. No compiler callback occurs. -/
def SourceSlice (profile : ValidationProfile) (bytes : Slice U8) : Prop :=
  ∃ raw, ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile ∧ ModuleSlice raw

/-- The store's code constructor for one independently decoded function. -/
def sourceFunctionCode (index : U32) (entry : ModuleBinary.Code) : funccode :=
  .FUNC (.mk_uN index.val) (entry.declared.map (fun ty => .LOCAL (Translate.valueType ty))) entry.body

def sourceFunctions (raw : ModuleBinary.Module) : List funccode :=
  List.zipWith sourceFunctionCode raw.functions raw.codes

/-- Conversion retains all source fields; the SpecTec module and store use
separate inductive constructor types. -/
def functionCode : func → funccode
  | .FUNC index locals body => .FUNC index locals body

@[simp] theorem functionCode_entry (index : U32) (entry : ModuleBinary.Code) :
    functionCode (CodeEntry.function index entry) = sourceFunctionCode index entry := rfl

theorem sourceFunctions_eq (raw : ModuleBinary.Module) :
    sourceFunctions raw = (List.zipWith CodeEntry.function raw.functions raw.codes).map functionCode := by
  simp [sourceFunctions, List.map_zipWith, Function.comp_def]

/-- Binary uniqueness selects the same source module as accepted validation. -/
theorem SourceSlice.decoded {profile bytes raw}
    (supported : SourceSlice profile bytes)
    (encoded : ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile) :
    ModuleSlice raw := by
  obtain ⟨source, encoding, subset⟩ := supported
  have same := Profile.module_unique encoding encoded
  simpa only [same] using subset

theorem SourceSlice.validated {profile bytes decoded}
    (supported : SourceSlice profile bytes)
    (validated : ModuleSound.Validated bytes decoded profile) :
    ∃ raw, ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile ∧
      ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw) ∧
      ModuleElaboration.Matches decoded.env decoded.tail raw ∧ Module_ok (ModuleElaboration.moduleOf raw) ∧
      ModuleElaboration.Profile raw profile ∧ ModuleElaboration.AccessorTypes decoded.env raw ∧ ModuleSlice raw := by
  obtain ⟨raw, encoded, elaborated, matched, typed, restrictions, accessors⟩ := validated
  exact ⟨raw, encoded, elaborated, matched, typed, restrictions, accessors, supported.decoded encoded⟩

/-- The accepted module's canonical environment supplies the profile's
signature restriction, including Wasm 1's single-result bound. -/
theorem validated_type_profile {bytes decoded profile}
    (validated : ModuleSound.Validated bytes decoded profile) :
    ∀ ft ∈ decoded.env.types.val, Profile.FuncType profile ft := by
  obtain ⟨raw, _, _, matched, _, restrictions, _⟩ := validated
  have types := congrArg ModuleBinary.Module.types matched.1
  simp only [ModuleElaboration.fromEnv] at types
  simpa only [types] using restrictions.arity

theorem witness_type_profile {V : Type} {visitor : code.OpVisitor V}
    {data env index start finish before after profile}
    (w : CodeEntry.Witness visitor data env index start finish before after profile)
    (types : ∀ ft ∈ env.types.val, Profile.FuncType profile ft) : Profile.FuncType profile w.ft := by
  apply types
  rw [← w.function_type]
  exact List.getElem_mem _

/-- The actual entry's size/local framing and canonical parser soundness
recover the exact independently encoded body and local declaration groups. -/
theorem witness_source_entry {V : Type} {visitor : code.OpVisitor V}
    {data env index start finish before after profile}
    (w : CodeEntry.Witness visitor data env index start finish before after profile)
    (types : ∀ ft ∈ env.types.val, Profile.FuncType profile ft)
    (entry : ModuleBinary.Code)
    (encoded : ModuleBinary.At (Profile.CodeEncoding profile) data start entry finish) :
    w.groups = entry.locals ∧ Profile.BodyEncoding profile w.body entry.body := by
  have lookup : env.types.val[w.typeIdx.val]? = some w.ft := by
    simp only [List.getElem?_eq_getElem w.type_lt, w.function_type]
  obtain ⟨ft, source, _, _, body, _⟩ := CodeEntry.runBody.sound visitor profile w.body env w.ctx w.typeIdx w.ft
    w.startedState after lookup w.context_results (witness_type_profile w types) w.body_accepted
  have actual := Profile.codeEncoding_of_parts w.header w.extent w.locals_bytes w.body_bytes body
  obtain ⟨bytes, encoding, span⟩ := encoded
  obtain ⟨actualBytes, actualEncoding, actualSpan⟩ := actual
  have same : (⟨w.groups, source⟩ : ModuleBinary.Code) = entry :=
    (Profile.code_prefix_unique profile actualEncoding encoding (actualSpan.suffix.symm.trans span.suffix)).1
  have groups := congrArg ModuleBinary.Code.locals same
  have instructions := congrArg ModuleBinary.Code.body same
  exact ⟨groups, instructions ▸ body⟩

end Exec.Code
