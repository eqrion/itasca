import Itasca.Support.EnvTranslation

open Aeneas Aeneas.Std

namespace Itasca.ModuleTranslation

/-- Canonical projections preserve import order and discard only other kinds. -/
def funcs : List externtype → List functype
  | [] => []
  | .FUNC t :: rest => t :: funcs rest
  | _ :: rest => funcs rest

@[simp] theorem funcs_append (xs ys : List externtype) :
    funcs (xs ++ ys) = funcs xs ++ funcs ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [funcs, ih]

theorem funcs_spec (xs : List externtype) : fun_funcsxt xs (funcs xs) := by
  induction xs with
  | nil => exact .fun_funcsxt_case_0
  | cons x xs ih =>
      cases x with
      | FUNC t => exact .fun_funcsxt_case_1 t xs _ ih
      | GLOBAL t => exact .fun_funcsxt_case_2 t xs _ ih
      | TABLE t => exact .fun_funcsxt_case_3 t xs _ ih
      | MEM t => exact .fun_funcsxt_case_4 t xs _ ih

theorem funcs_unique {xs result} (h : fun_funcsxt xs result) : result = funcs xs := by
  induction h <;> simp_all [funcs]

def globals : List externtype → List globaltype
  | [] => []
  | .GLOBAL t :: rest => t :: globals rest
  | _ :: rest => globals rest

@[simp] theorem globals_append (xs ys : List externtype) :
    globals (xs ++ ys) = globals xs ++ globals ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [globals, ih]

theorem globals_spec (xs : List externtype) : fun_globalsxt xs (globals xs) := by
  induction xs with
  | nil => exact .fun_globalsxt_case_0
  | cons x xs ih =>
      cases x with
      | GLOBAL t => exact .fun_globalsxt_case_1 t xs _ ih
      | FUNC t => exact .fun_globalsxt_case_2 t xs _ ih
      | TABLE t => exact .fun_globalsxt_case_3 t xs _ ih
      | MEM t => exact .fun_globalsxt_case_4 t xs _ ih

theorem globals_unique {xs result} (h : fun_globalsxt xs result) : result = globals xs := by
  induction h <;> simp_all [globals]

def tables : List externtype → List tabletype
  | [] => []
  | .TABLE t :: rest => t :: tables rest
  | _ :: rest => tables rest

@[simp] theorem tables_append (xs ys : List externtype) :
    tables (xs ++ ys) = tables xs ++ tables ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [tables, ih]

theorem tables_spec (xs : List externtype) : fun_tablesxt xs (tables xs) := by
  induction xs with
  | nil => exact .fun_tablesxt_case_0
  | cons x xs ih =>
      cases x with
      | TABLE t => exact .fun_tablesxt_case_1 t xs _ ih
      | FUNC t => exact .fun_tablesxt_case_2 t xs _ ih
      | GLOBAL t => exact .fun_tablesxt_case_3 t xs _ ih
      | MEM t => exact .fun_tablesxt_case_4 t xs _ ih

theorem tables_unique {xs result} (h : fun_tablesxt xs result) : result = tables xs := by
  induction h <;> simp_all [tables]

def mems : List externtype → List memtype
  | [] => []
  | .MEM t :: rest => t :: mems rest
  | _ :: rest => mems rest

@[simp] theorem mems_append (xs ys : List externtype) :
    mems (xs ++ ys) = mems xs ++ mems ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [mems, ih]

theorem mems_spec (xs : List externtype) : fun_memsxt xs (mems xs) := by
  induction xs with
  | nil => exact .fun_memsxt_case_0
  | cons x xs ih =>
      cases x with
      | MEM t => exact .fun_memsxt_case_1 t xs _ ih
      | FUNC t => exact .fun_memsxt_case_2 t xs _ ih
      | GLOBAL t => exact .fun_memsxt_case_3 t xs _ ih
      | TABLE t => exact .fun_memsxt_case_4 t xs _ ih

theorem mems_unique {xs result} (h : fun_memsxt xs result) : result = mems xs := by
  induction h <;> simp_all [mems]

/-- Byte-level limit checks translate to the generated declarative rule. -/
def LimitsValid (lim : types.Limits) (bound : Nat) : Prop :=
  lim.min.val ≤ bound ∧ ∀ maximum ∈ lim.max, lim.min.val ≤ maximum.val ∧ maximum.val ≤ bound

theorem limits_valid (lim : types.Limits) (bound : Nat) (h : LimitsValid lim bound) :
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

theorem funcType_valid (ft : types.FuncType) : Functype_ok (EnvTranslation.funcType ft) :=
  .mk_Functype_ok _ _

theorem tableType_valid (tt : types.TableType)
    (h : LimitsValid tt.limits (2 ^ 32 - 1)) :
    Tabletype_ok (EnvTranslation.tableType tt) := by
  apply Tabletype_ok.mk_Tabletype_ok
  · exact limits_valid tt.limits _ h
  · exact EnvTranslation.tableType_wf tt

theorem memType_valid (mt : types.MemType)
    (h : LimitsValid mt.limits (2 ^ 16)) :
    Memtype_ok (EnvTranslation.memType mt) :=
  .mk_Memtype_ok _ (limits_valid mt.limits _ h) (EnvTranslation.memType_wf mt)

end Itasca.ModuleTranslation
