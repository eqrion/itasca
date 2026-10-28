import Exec.Abs.PureHead
import Itasca.Module.Soundness
import Itasca.Results.Unique
import Itasca.Profile.EntrySound
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

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

theorem witness_type_profile {V : Type} {visitor : code.OpVisitor V}
    {data env index start finish before after profile}
    (w : CodeEntry.Witness visitor data env index start finish before after profile)
    (types : ∀ ft ∈ env.types.val, Profile.FuncType profile ft) : Profile.FuncType profile w.ft := by
  apply types
  rw [← w.function_type]
  exact List.getElem_mem _

end Itasca.Runtime.Code
