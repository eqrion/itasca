import Itasca.Module.ModuleEnv

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

def rawImport (entry : module.Import) : ModuleBinary.Import :=
  ⟨entry.module.val, entry.name.val, entry.desc⟩

def rawExport (entry : module.Export) : ModuleBinary.Export := ⟨entry.name.val, entry.desc⟩

def rawElement (entry : module.Element) : ModuleBinary.Element :=
  ⟨entry.table_idx, entry.offset, entry.init.val⟩

structure Represents (env : module.Env) (decls : Declarations) : Prop where
  types : decls.types = env.types.val
  imports : decls.imports = env.imports.val.map rawImport
  functions : decls.functions = env.func_type_indices.val
  globals : decls.globals = env.globals.val
  exports : decls.exports = env.exports.val.map rawExport
  start : decls.start = env.start
  elements : decls.elements = env.elements.val.map rawElement
  cache : Cache env decls.tables decls.memories

/-- The independently encoded prefix ends immediately before code/data, with
all custom sections encountered before that boundary included. -/
def PrefixEncoding (value : Declarations) (bytes : List U8) : Prop :=
  ∃ types imports functions tables memories globals exports start elements customs,
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
    ModuleBinary.PaddedEncoding 9#u8 (ModuleBinary.VecEncoding ModuleBinary.ElementEncoding)
      [] value.elements elements ∧
    ModuleBinary.CustomsEncoding customs ∧
    bytes = ModuleBinary.magicVersion ++ types ++ imports ++ functions ++ tables ++ memories ++
      globals ++ exports ++ start ++ elements ++ customs

def Declarations.module (decls : Declarations) (codes : List ModuleBinary.Code)
    (data : List ModuleBinary.Data) : ModuleBinary.Module :=
  ⟨decls.types, decls.imports, decls.functions, decls.tables, decls.memories,
    decls.globals, decls.exports, decls.start, decls.elements, codes, data⟩

end Itasca.ModuleEnv
