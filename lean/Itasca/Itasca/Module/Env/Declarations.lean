import Itasca.Module.Definitions
import Itasca.Results.Definitions.Validation
import Itasca.Module.Sections.Headers
import Itasca.Module.Env.Externals

/-! ## TypeBounds -/

section

/-!
# Function type parameter bounds

A function type's parameter vector is bounded by the number of bytes that encode it. The
`func_type_vector_params_bound` lemmas give this for decoded type vectors, and `SignatureBounded`
packages the bound for the types of an environment so that parameter counts stay within the
byte cursor.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary

theorem Rep.value_types_length {values bytes} (h : Rep ValueTypeEncoding values bytes) :
    bytes.length = values.length := by
  induction h with
  | nil => rfl
  | cons he _ ih => simp_all [ValueTypeEncoding.reader_bytes]

theorem FuncTypeEncoding.params_bound {ty bytes} (h : FuncTypeEncoding ty bytes) :
    ty.params.val.length ≤ bytes.length := by
  obtain ⟨params, results, ⟨count, entries, _, hp, rfl⟩, _, rfl⟩ := FuncTypeEncoding.reader_parts.mp h
  have he := Rep.value_types_length hp
  simp only [List.length_cons, List.length_append]
  omega

theorem Rep.func_types_params_bound {types bytes} (h : Rep FuncTypeEncoding types bytes) :
    ∀ ty ∈ types, ty.params.val.length ≤ bytes.length := by
  induction h with
  | nil => simp
  | cons he _ ih =>
    intro ty hm
    rcases List.mem_cons.mp hm with rfl | hm
    · have := he.params_bound
      simp only [List.length_append]
      omega
    · have := ih ty hm
      simp only [List.length_append]
      omega

/-- Every function type in a decoded type vector has at most as many parameters as the end
position of the vector. -/
theorem At.func_type_vector_params_bound {data start types next}
    (h : At (VecEncoding FuncTypeEncoding) data start types next) :
    ∀ ty ∈ types, ty.params.val.length ≤ next.val := by
  obtain ⟨bytes, ⟨count, entries, _, he, rfl⟩, hs⟩ := h
  intro ty hm
  have := Rep.func_types_params_bound he ty hm
  have := hs.length
  simp only [List.length_append] at this
  omega

end Itasca.Binary

namespace Itasca.Module.Environment

/-- Every function type in the environment has at most `limit` parameters. Parameter vectors are
nested inside the type list, so they need their own size bound unlike the index-space caches. -/
def SignatureBounded (env : metadata.CodeMetadata) (limit : Nat) : Prop :=
  ∀ ft ∈ env.types.val, ft.params.val.length ≤ limit

theorem SignatureBounded.mono {env limit next} (h : SignatureBounded env limit) (hle : limit ≤ next) :
    SignatureBounded env next := by
  intro ft hf
  have := h ft hf
  omega

/-- Appending the types decoded by a type section keeps the signature bound at the cursor after
the section. -/
theorem SignatureBounded.of_types_added {env result added data start next}
    (h : SignatureBounded env start.val)
    (hadd : Module.Sections.TypesAdded env result added)
    (hbytes : Binary.At (Binary.VecEncoding Binary.FuncTypeEncoding)
      data start added next) : SignatureBounded result next.val := by
  intro ft hf
  rw [hadd.2] at hf
  rcases List.mem_append.mp hf with hf | hf
  · exact h.mono hbytes.span.1 ft hf
  · exact hbytes.func_type_vector_params_bound ft hf

end Itasca.Module.Environment

end

/-! ## Declarations -/

section

/-!
# Declaration prefixes

`Declarations` is the ghost record of the sections decoded before the code section, keeping the
section boundaries that the environment's merged caches lose. `Phase` constrains it by the last
section seen, `Represents` relates it to decoded prefix metadata, and `PrefixEncoding` is the independent
byte grammar of the whole prefix, including custom sections.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Environment

/-- The raw module with declarations `decls` and the given code and data sections. -/
def Declarations.module (decls : Declarations) (codes : List Binary.Code)
    (data : List Binary.Data) : Binary.Module :=
  ⟨decls.types, decls.imports, decls.functions, decls.tables, decls.memories,
    decls.globals, decls.exports, decls.start, decls.elements, decls.dataCount, codes, data⟩

/-- `bytes` is the module header followed by the canonical encoding of `value`, ending just before
the code or data section and including all custom sections before that point. -/
def PrefixEncoding (value : Declarations) (bytes : List U8) : Prop :=
  ∃ types imports functions tables memories globals exports start elements dataCount customs,
    Binary.PaddedEncoding 1#u8 (Binary.VecEncoding Binary.FuncTypeEncoding)
      [] value.types types ∧
    Binary.PaddedEncoding 2#u8 (Binary.VecEncoding Binary.ImportEncoding)
      [] value.imports imports ∧
    Binary.PaddedEncoding 3#u8 (Binary.VecEncoding Binary.IndexEncoding)
      [] value.functions functions ∧
    Binary.PaddedEncoding 4#u8 (Binary.VecEncoding Binary.TableTypeEncoding)
      [] value.tables tables ∧
    Binary.PaddedEncoding 5#u8 (Binary.VecEncoding Binary.MemTypeEncoding)
      [] value.memories memories ∧
    Binary.PaddedEncoding 6#u8 (Binary.VecEncoding Binary.GlobalEncoding)
      [] value.globals globals ∧
    Binary.PaddedEncoding 7#u8 (Binary.VecEncoding Binary.ExportEncoding)
      [] value.exports exports ∧
    Binary.PaddedEncoding 8#u8 Binary.StartEncoding none value.start start ∧
    Binary.PaddedEncoding 9#u8 (Binary.VecEncoding Binary.ElementEncoding)
      [] value.elements elements ∧
    Binary.DataCountSectionEncoding value.dataCount dataCount ∧
    Binary.CustomsEncoding customs ∧
    bytes = Binary.magicVersion ++ types ++ imports ++ functions ++ tables ++ memories ++
      globals ++ exports ++ start ++ elements ++ dataCount ++ customs

end Itasca.Module.Environment

end
