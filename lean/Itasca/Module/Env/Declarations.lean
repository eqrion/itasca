import Itasca.Module.Sections.ElementHeader
import Itasca.Module.Env.Basic

/-!
Sections, each formerly its own module: TypeBounds, Declarations.
-/

/-! ## TypeBounds -/

section

/-!
# Function type parameter bounds

A function type's parameter vector is bounded by the number of bytes that encode it. The
`funcTypeVector_params_bound` lemmas give this for decoded type vectors, and `SignatureBounded`
packages the bound for the types of an environment so that parameter counts stay within the
byte cursor.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

theorem Rep.valueTypes_length {values bytes} (h : Rep ValueTypeEncoding values bytes) :
    bytes.length = values.length := by
  induction h with
  | nil => rfl
  | cons he _ ih => simp_all [ValueTypeEncoding]

theorem FuncTypeEncoding.params_bound {ty bytes} (h : FuncTypeEncoding ty bytes) :
    ty.params.val.length ≤ bytes.length := by
  obtain ⟨params, results, ⟨count, entries, _, hp, rfl⟩, _, rfl⟩ := h
  have he := hp.valueTypes_length
  simp only [List.length_cons, List.length_append]
  omega

theorem Rep.funcTypes_params_bound {types bytes} (h : Rep FuncTypeEncoding types bytes) :
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
theorem At.funcTypeVector_params_bound {data start types next}
    (h : At (VecEncoding FuncTypeEncoding) data start types next) :
    ∀ ty ∈ types, ty.params.val.length ≤ next.val := by
  obtain ⟨bytes, ⟨count, entries, _, he, rfl⟩, hs⟩ := h
  intro ty hm
  have := he.funcTypes_params_bound ty hm
  have := hs.length
  simp only [List.length_append] at this
  omega

end Itasca.ModuleBinary

namespace Itasca.ModuleEnv

/-- Every function type in the environment has at most `limit` parameters. Parameter vectors are
nested inside the type list, so they need their own size bound unlike the index-space caches. -/
def SignatureBounded (env : metadata.Env) (limit : Nat) : Prop :=
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
    (hadd : ModuleSections.TypesAdded env result added)
    (hbytes : ModuleBinary.At (ModuleBinary.VecEncoding ModuleBinary.FuncTypeEncoding)
      data start added next) : SignatureBounded result next.val := by
  intro ft hf
  rw [hadd.2] at hf
  rcases List.mem_append.mp hf with hf | hf
  · exact h.mono hbytes.span.1 ft hf
  · exact hbytes.funcTypeVector_params_bound ft hf

end Itasca.ModuleEnv

end

/-! ## Declarations -/

section

/-!
# Declaration prefixes

`Declarations` is the ghost record of the sections decoded before the code section, keeping the
section boundaries that the environment's merged caches lose. `Phase` constrains it by the last
section seen, `Represents` relates it to a `metadata.Env`, and `PrefixEncoding` is the independent
byte grammar of the whole prefix, including custom sections.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

/-- The declared contents of each pre-code section, kept apart rather than merged with imports. -/
structure Declarations where
  types : List wasm_types.FuncType := []
  imports : List ModuleBinary.Import := []
  functions : List U32 := []
  tables : List _root_.Itasca.wasm_types.TableType := []
  memories : List _root_.Itasca.wasm_types.MemType := []
  globals : List metadata.Global := []
  exports : List ModuleBinary.Export := []
  start : Option U32 := none
  elements : List ModuleBinary.Element := []
  dataCount : Option U32 := none

/-- Sections ranked after `last` are still empty, which excludes duplicate and misordered
sections. -/
def Phase (last : Nat) (decls : Declarations) : Prop :=
  (last < 1 → decls.types = []) ∧
  (last < 2 → decls.imports = []) ∧
  (last < 3 → decls.functions = []) ∧
  (last < 4 → decls.tables = []) ∧
  (last < 5 → decls.memories = []) ∧
  (last < 6 → decls.globals = []) ∧
  (last < 7 → decls.exports = []) ∧
  (last < 8 → decls.start = none) ∧
  (last < 9 → decls.elements = []) ∧
  (last < 10 → decls.dataCount = none)

/-- The independent grammar's import corresponding to an extracted import. -/
def rawImport (entry : metadata.Import) : ModuleBinary.Import :=
  ⟨entry.module.val, entry.name.val, entry.desc⟩

/-- The independent grammar's export corresponding to an extracted export. -/
def rawExport (entry : metadata.Export) : ModuleBinary.Export := ⟨entry.name.val, entry.desc⟩

/-- The independent grammar's element segment corresponding to an extracted element. -/
def rawElement (entry : metadata.Element) : ModuleBinary.Element :=
  ⟨entry.elem, entry.mode, entry.init.val⟩

/-- The environment `env` stores exactly the declarations `decls`, and its caches are the merged
index spaces of `decls`. -/
structure Represents (env : metadata.Env) (decls : Declarations) : Prop where
  types : decls.types = env.types.val
  imports : decls.imports = env.imports.val.map rawImport
  functions : decls.functions = env.func_type_indices.val
  globals : decls.globals = env.globals.val
  exports : decls.exports = env.exports.val.map rawExport
  start : decls.start = env.start
  elements : decls.elements = env.elements.val.map rawElement
  dataCount : decls.dataCount = env.data_count
  cache : Cache env decls.tables decls.memories

/-- The raw module with declarations `decls` and the given code and data sections. -/
def Declarations.module (decls : Declarations) (codes : List ModuleBinary.Code)
    (data : List ModuleBinary.Data) : ModuleBinary.Module :=
  ⟨decls.types, decls.imports, decls.functions, decls.tables, decls.memories,
    decls.globals, decls.exports, decls.start, decls.elements, decls.dataCount, codes, data⟩

/-- `bytes` is the module header followed by the canonical encoding of `value`, ending just before
the code or data section and including all custom sections before that point. -/
def PrefixEncoding (value : Declarations) (bytes : List U8) : Prop :=
  ∃ types imports functions tables memories globals exports start elements dataCount customs,
    ModuleBinary.PaddedEncoding 1#u8 (ModuleBinary.VecEncoding ModuleBinary.FuncTypeEncoding)
      [] value.types types ∧
    ModuleBinary.PaddedEncoding 2#u8 (ModuleBinary.VecEncoding ModuleBinary.ImportEncoding)
      [] value.imports imports ∧
    ModuleBinary.PaddedEncoding 3#u8 (ModuleBinary.VecEncoding ModuleBinary.IndexEncoding)
      [] value.functions functions ∧
    ModuleBinary.PaddedEncoding 4#u8 (ModuleBinary.VecEncoding ModuleBinary.TableTypeEncoding)
      [] value.tables tables ∧
    ModuleBinary.PaddedEncoding 5#u8 (ModuleBinary.VecEncoding ModuleBinary.MemTypeEncoding)
      [] value.memories memories ∧
    ModuleBinary.PaddedEncoding 6#u8 (ModuleBinary.VecEncoding ModuleBinary.GlobalEncoding)
      [] value.globals globals ∧
    ModuleBinary.PaddedEncoding 7#u8 (ModuleBinary.VecEncoding ModuleBinary.ExportEncoding)
      [] value.exports exports ∧
    ModuleBinary.PaddedEncoding 8#u8 ModuleBinary.StartEncoding none value.start start ∧
    ModuleBinary.PaddedEncoding 9#u8 (ModuleBinary.VecEncoding (ModuleBinary.ElementEncodingFor))
      [] value.elements elements ∧
    ModuleBinary.DataCountSectionEncoding value.dataCount dataCount ∧
    ModuleBinary.CustomsEncoding customs ∧
    bytes = ModuleBinary.magicVersion ++ types ++ imports ++ functions ++ tables ++ memories ++
      globals ++ exports ++ start ++ elements ++ dataCount ++ customs

end Itasca.ModuleEnv

end
