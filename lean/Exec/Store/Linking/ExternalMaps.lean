import Exec.Store.Linking.LinkMaps
namespace Exec.Store
open Aeneas Aeneas.Std

def decodeExternal : runtime.Extern → externaddr
  | .Func address => .FUNC address.index.val
  | .Table address => .TABLE address.index.val
  | .Memory address => .MEM address.index.val
  | .Global address => .GLOBAL address.index.val

def externalFunctions (externals : List runtime.Extern) : List runtime.FuncAddr :=
  externals.filterMap (fun external => match external with | .Func a => some a | _ => none)
def externalTables (externals : List runtime.Extern) : List runtime.TableAddr :=
  externals.filterMap (fun external => match external with | .Table a => some a | _ => none)
def externalMemories (externals : List runtime.Extern) : List runtime.MemoryAddr :=
  externals.filterMap (fun external => match external with | .Memory a => some a | _ => none)
def externalGlobals (externals : List runtime.Extern) : List runtime.GlobalAddr :=
  externals.filterMap (fun external => match external with | .Global a => some a | _ => none)

/-- Exact address subsequences of the caller's external list, including ownership
bits. This complements the signature-indexed import map. -/
structure ExternalMaps (externals : List runtime.Extern) (inst : runtime.store.ModuleInst) : Prop where
  funcs : inst.funcs.val = externalFunctions externals
  tables : inst.tables.val = externalTables externals
  memories : inst.memories.val = externalMemories externals
  globals : inst.globals.val = externalGlobals externals

theorem LinkedStep.external_maps {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {before after : runtime.store.ModuleInst} {desc external externals}
    (effect : LinkedStep view store before desc external after)
    (maps : ExternalMaps externals before) : ExternalMaps (externals ++ [external]) after := by
  cases effect <;> constructor <;>
    simp_all [externalFunctions, externalTables, externalMemories, externalGlobals,
      maps.funcs, maps.tables, maps.memories, maps.globals]

theorem external_functions (externals : List runtime.Extern) :
    fun_funcs (externals.map decodeExternal)
      ((externalFunctions externals).map (fun a => a.index.val)) := by
  induction externals with
  | nil => exact .fun_funcs_case_0
  | cons external rest ih =>
    cases external <;> simp only [List.map_cons, externalFunctions, List.filterMap_cons,
      List.map_cons,
      decodeExternal] at *
    · exact .fun_funcs_case_1 _ _ _ ih
    all_goals exact .fun_funcs_case_2 _ _ _ ih

theorem external_globals (externals : List runtime.Extern) :
    fun_globals (externals.map decodeExternal)
      ((externalGlobals externals).map (fun a => a.index.val)) := by
  induction externals with
  | nil => exact .fun_globals_case_0
  | cons external rest ih =>
    cases external <;> simp only [List.map_cons, externalGlobals, List.filterMap_cons,
      List.map_cons,
      decodeExternal] at *
    all_goals first
      | exact .fun_globals_case_1 _ _ _ ih
      | exact .fun_globals_case_2 _ _ _ ih

theorem external_tables (externals : List runtime.Extern) :
    fun_tables (externals.map decodeExternal)
      ((externalTables externals).map (fun a => a.index.val)) := by
  induction externals with
  | nil => exact .fun_tables_case_0
  | cons external rest ih =>
    cases external <;> simp only [List.map_cons, externalTables, List.filterMap_cons,
      List.map_cons,
      decodeExternal] at *
    all_goals first
      | exact .fun_tables_case_1 _ _ _ ih
      | exact .fun_tables_case_2 _ _ _ ih

theorem external_memories (externals : List runtime.Extern) :
    fun_mems (externals.map decodeExternal)
      ((externalMemories externals).map (fun a => a.index.val)) := by
  induction externals with
  | nil => exact .fun_mems_case_0
  | cons external rest ih =>
    cases external <;> simp only [List.map_cons, externalMemories, List.filterMap_cons,
      List.map_cons,
      decodeExternal] at *
    all_goals first
      | exact .fun_mems_case_1 _ _ _ ih
      | exact .fun_mems_case_2 _ _ _ ih
end Exec.Store
