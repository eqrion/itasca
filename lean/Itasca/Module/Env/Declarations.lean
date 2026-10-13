import Itasca.Module.Env.Basic

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

/-- The declaration prefix retains section boundaries that the runtime caches merge. -/
structure Declarations where
  types : List types.FuncType := []
  imports : List ModuleBinary.Import := []
  functions : List U32 := []
  tables : List _root_.Itasca.types.TableType := []
  memories : List _root_.Itasca.types.MemType := []
  globals : List module.Global := []
  exports : List ModuleBinary.Export := []
  start : Option U32 := none
  elements : List ModuleBinary.Element := []
  dataCount : Option U32 := none

/-- This phase condition excludes duplicate sections and keeps future raw fields empty. -/
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


def rawImport (entry : module.Import) : ModuleBinary.Import :=
  ⟨entry.module.val, entry.name.val, entry.desc⟩

def rawExport (entry : module.Export) : ModuleBinary.Export := ⟨entry.name.val, entry.desc⟩

def rawElement (entry : module.Element) : ModuleBinary.Element :=
  ⟨entry.elem, entry.mode, entry.init.val⟩

structure Represents (env : module.Env) (decls : Declarations) : Prop where
  types : decls.types = env.types.val
  imports : decls.imports = env.imports.val.map rawImport
  functions : decls.functions = env.func_type_indices.val
  globals : decls.globals = env.globals.val
  exports : decls.exports = env.exports.val.map rawExport
  start : decls.start = env.start
  elements : decls.elements = env.elements.val.map rawElement
  dataCount : decls.dataCount = env.data_count
  cache : Cache env decls.tables decls.memories

def Declarations.module (decls : Declarations) (codes : List ModuleBinary.Code)
    (data : List ModuleBinary.Data) : ModuleBinary.Module :=
  ⟨decls.types, decls.imports, decls.functions, decls.tables, decls.memories,
    decls.globals, decls.exports, decls.start, decls.elements, decls.dataCount, codes, data⟩


/-- The independently encoded prefix ends immediately before code/data, with
all custom sections encountered before that boundary included. -/
def PrefixEncoding (value : Declarations) (bytes : List U8)
    (profile : ValidationProfile := .Wasm1) : Prop :=
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
    ModuleBinary.PaddedEncoding 9#u8 (ModuleBinary.VecEncoding (ModuleBinary.ElementEncodingFor profile))
      [] value.elements elements ∧
    ModuleBinary.DataCountSectionEncoding profile value.dataCount dataCount ∧
    ModuleBinary.CustomsEncoding customs ∧
    bytes = ModuleBinary.magicVersion ++ types ++ imports ++ functions ++ tables ++ memories ++
      globals ++ exports ++ start ++ elements ++ dataCount ++ customs ∧
    ModuleBinary.ModuleTypesAllowed profile (value.module [] [])


theorem PrefixEncoding.allowed {profile value bytes} (h : PrefixEncoding value bytes profile) :
    ModuleBinary.ModuleTypesAllowed profile (value.module [] []) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ha⟩ := h
  exact ha

end Itasca.ModuleEnv
