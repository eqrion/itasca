import Itasca.Support.EnvTranslation

/-!
# Import projections and validity translation

`funcs`, `globals`, `tables` and `mems` project the function, global, table and memory types out of
a list of external types, matching the generated `fun_funcsxt`, `fun_globalsxt`, `fun_tablesxt` and
`fun_memsxt` relations (`funcs_spec` and `funcs_unique` and their analogues). `LimitsValid` and the
`_valid` theorems turn byte-level limit checks into the generated `Limits_ok`, `Tabletype_ok`,
`Memtype_ok` and `Functype_ok`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleTranslation

/-- The function types among the external types, in order. -/
def funcs : List externtype → List functype
  | [] => []
  | .FUNC t :: rest => t :: funcs rest
  | _ :: rest => funcs rest

/-- `funcs` satisfies the generated `fun_funcsxt` relation. -/
theorem funcs_spec (xs : List externtype) : fun_funcsxt xs (funcs xs) := by
  induction xs with
  | nil => exact .fun_funcsxt_case_0
  | cons x xs ih =>
      cases x with
      | FUNC t => exact .fun_funcsxt_case_1 t xs _ ih
      | GLOBAL t => exact .fun_funcsxt_case_2 t xs _ ih
      | TABLE t => exact .fun_funcsxt_case_3 t xs _ ih
      | MEM t => exact .fun_funcsxt_case_4 t xs _ ih

/-- The generated `fun_funcsxt` relation determines `funcs`. -/
theorem funcs_unique {xs result} (h : fun_funcsxt xs result) : result = funcs xs := by
  induction h <;> simp_all [funcs]

/-- The global types among the external types, in order. -/
def globals : List externtype → List globaltype
  | [] => []
  | .GLOBAL t :: rest => t :: globals rest
  | _ :: rest => globals rest

/-- `globals` satisfies the generated `fun_globalsxt` relation. -/
theorem globals_spec (xs : List externtype) : fun_globalsxt xs (globals xs) := by
  induction xs with
  | nil => exact .fun_globalsxt_case_0
  | cons x xs ih =>
      cases x with
      | GLOBAL t => exact .fun_globalsxt_case_1 t xs _ ih
      | FUNC t => exact .fun_globalsxt_case_2 t xs _ ih
      | TABLE t => exact .fun_globalsxt_case_3 t xs _ ih
      | MEM t => exact .fun_globalsxt_case_4 t xs _ ih

/-- The generated `fun_globalsxt` relation determines `globals`. -/
theorem globals_unique {xs result} (h : fun_globalsxt xs result) : result = globals xs := by
  induction h <;> simp_all [globals]

/-- The table types among the external types, in order. -/
def tables : List externtype → List tabletype
  | [] => []
  | .TABLE t :: rest => t :: tables rest
  | _ :: rest => tables rest

/-- `tables` satisfies the generated `fun_tablesxt` relation. -/
theorem tables_spec (xs : List externtype) : fun_tablesxt xs (tables xs) := by
  induction xs with
  | nil => exact .fun_tablesxt_case_0
  | cons x xs ih =>
      cases x with
      | TABLE t => exact .fun_tablesxt_case_1 t xs _ ih
      | FUNC t => exact .fun_tablesxt_case_2 t xs _ ih
      | GLOBAL t => exact .fun_tablesxt_case_3 t xs _ ih
      | MEM t => exact .fun_tablesxt_case_4 t xs _ ih

/-- The generated `fun_tablesxt` relation determines `tables`. -/
theorem tables_unique {xs result} (h : fun_tablesxt xs result) : result = tables xs := by
  induction h <;> simp_all [tables]

/-- The memory types among the external types, in order. -/
def mems : List externtype → List memtype
  | [] => []
  | .MEM t :: rest => t :: mems rest
  | _ :: rest => mems rest

/-- `mems` satisfies the generated `fun_memsxt` relation. -/
theorem mems_spec (xs : List externtype) : fun_memsxt xs (mems xs) := by
  induction xs with
  | nil => exact .fun_memsxt_case_0
  | cons x xs ih =>
      cases x with
      | MEM t => exact .fun_memsxt_case_1 t xs _ ih
      | FUNC t => exact .fun_memsxt_case_2 t xs _ ih
      | GLOBAL t => exact .fun_memsxt_case_3 t xs _ ih
      | TABLE t => exact .fun_memsxt_case_4 t xs _ ih

/-- The generated `fun_memsxt` relation determines `mems`. -/
theorem mems_unique {xs result} (h : fun_memsxt xs result) : result = mems xs := by
  induction h <;> simp_all [mems]

/-- The limits' minimum and any maximum are ordered and within `bound`. This is the byte-level check
that corresponds to the generated `Limits_ok`. -/
def LimitsValid (lim : wasm_types.Limits) (bound : Nat) : Prop :=
  lim.min.val ≤ bound ∧ ∀ maximum ∈ lim.max, lim.min.val ≤ maximum.val ∧ maximum.val ≤ bound

/-- Valid limits are typed by the generated `Limits_ok`. -/
theorem limits_valid (lim : wasm_types.Limits) (bound : Nat) (h : LimitsValid lim bound) :
    Limits_ok (EnvTranslation.limitsType lim) bound := by
  have hw := EnvTranslation.limitsType_wf lim
  cases lim with
  | mk minimum maximum =>
    cases maximum with
    | none =>
      exact .mk_Limits_ok minimum.val none bound h.1 (by simp [Forall]) hw
    | some maximum =>
      exact .mk_Limits_ok minimum.val (some maximum.val) bound h.1
        (by simpa [Forall] using h.2 maximum (by simp)) hw

/-- Every translated function type is valid. -/
theorem funcType_valid (ft : wasm_types.FuncType) : Functype_ok (EnvTranslation.funcType ft) :=
  .mk_Functype_ok _ _

/-- A table type with valid limits is typed by `Tabletype_ok`. -/
theorem tableType_valid (tt : wasm_types.TableType)
    (h : LimitsValid tt.limits (2 ^ 32 - 1)) :
    Tabletype_ok (EnvTranslation.tableType tt) := by
  apply Tabletype_ok.mk_Tabletype_ok
  · exact limits_valid tt.limits _ h
  · exact EnvTranslation.tableType_wf tt

/-- A memory type with valid limits is typed by `Memtype_ok`. -/
theorem memType_valid (mt : wasm_types.MemType)
    (h : LimitsValid mt.limits (2 ^ 16)) :
    Memtype_ok (EnvTranslation.memType mt) :=
  .mk_Memtype_ok _ (limits_valid mt.limits _ h) (EnvTranslation.memType_wf mt)

end Itasca.ModuleTranslation
