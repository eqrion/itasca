import Exec.Spec.Context
import Mathlib.Data.List.Forall2
import Mathlib.Tactic
namespace Exec.Spec
open SpecExt

def allocationFunctionIndex : func → Nat
  | .FUNC (.mk_uN index) _ _ => index

def allocationFunction (inst : moduleinst) (source : func) : funcinst :=
  ⟨inst.TYPES[allocationFunctionIndex source]!, inst, funccode_func source⟩

def allocationTable : tabletype → tableinst
  | .mk_tabletype (.mk_limits (.mk_uN minimum) maximum) ty =>
    ⟨.mk_tabletype (.mk_limits (.mk_uN minimum) maximum) ty, List.replicate minimum (.REF_NULL ty)⟩

def allocationMemory : memtype → meminst
  | .PAGE (.mk_limits (.mk_uN minimum) maximum) =>
    ⟨.PAGE (.mk_limits (.mk_uN minimum) maximum), List.replicate (minimum * (64 * Ki)) (.mk_byte 0)⟩

theorem allocation_function_wf (inst : moduleinst) (source : func)
    (instanceWf : wf_moduleinst inst) (sourceWf : wf_func source) : wf_funcinst (allocationFunction inst source) := by
  cases sourceWf with
  | func_case_0 index locals body indexWf bodyWf =>
    exact .funcinst_case_ _ _ _ instanceWf (.funccode_case_0 _ _ _ indexWf bodyWf)

theorem allocate_function (s : store) (inst : moduleinst) (source : func)
    (instanceWf : wf_moduleinst inst) (sourceWf : wf_func source)
    (bound : allocationFunctionIndex source < inst.TYPES.length) :
    fun_allocfunc s inst source ({s with FUNCS := s.FUNCS ++ [allocationFunction inst source]}, s.FUNCS.length) := by
  have allocatedWf := allocation_function_wf inst source instanceWf sourceWf
  cases source with
  | FUNC index locals body =>
    exact .fun_allocfunc_case_0 s inst _ _ index locals body bound rfl rfl allocatedWf allocatedWf sourceWf

theorem allocate_global (s : store) (value : globalinst) (wf : wf_globalinst value) :
    fun_allocglobal s value.TYPE value.VALUE ({s with GLOBALS := s.GLOBALS ++ [value]}, s.GLOBALS.length) := by
  exact .fun_allocglobal_case_0 s value.TYPE value.VALUE value (by cases value; rfl) wf (by simpa using wf)

theorem allocate_table (s : store) (ty : tabletype) (wf : wf_tabletype ty) :
    fun_alloctable s ty ({s with TABLES := s.TABLES ++ [allocationTable ty]}, s.TABLES.length) := by
  cases ty with | mk_tabletype limits refType =>
    cases limits with | mk_limits minimum maximum =>
      cases minimum with | mk_uN minimum =>
        exact .fun_alloctable_case_0 s _ maximum refType _ rfl (.tableinst_case_ _ _ wf) (.tableinst_case_ _ _ wf)

theorem allocate_memory (s : store) (ty : memtype) (wf : wf_memtype ty) :
    fun_allocmem s ty ({s with MEMS := s.MEMS ++ [allocationMemory ty]}, s.MEMS.length) := by
  cases ty with | PAGE limits =>
    cases limits with | mk_limits minimum maximum =>
      cases minimum with | mk_uN minimum =>
        have bytes : Forall wf_byte (List.replicate (minimum * (64 * Ki)) (.mk_byte 0)) := by
          intro value member
          have same : value = .mk_byte 0 := (List.mem_replicate.mp member).2
          rw [same]; constructor; norm_num
        exact .fun_allocmem_case_0 s _ maximum _ rfl (.meminst_case_ _ _ wf bytes) (.meminst_case_ _ _ wf bytes)

theorem allocate_element (s : store) (element : eleminst) :
    fun_allocelem s element.TYPE element.REFS ({s with ELEMS := s.ELEMS ++ [element]}, s.ELEMS.length) := by
  exact .fun_allocelem_case_0 s element.TYPE element.REFS element (by cases element; rfl)

theorem allocate_data (s : store) (data : datainst) (wf : wf_datainst data) :
    fun_allocdata s data.BYTES ({s with DATAS := s.DATAS ++ [data]}, s.DATAS.length) := by
  exact .fun_allocdata_case_0 s data.BYTES data (by cases data; rfl) wf (by simpa using wf)

/-- Allocating a list appends its instances and issues precisely the consecutive
addresses starting at the old vector length. -/
theorem allocate_functions (s : store) (inst : moduleinst) (sources : List func)
    (instanceWf : wf_moduleinst inst) (sourceWf : Forall wf_func sources)
    (bounds : ∀ source ∈ sources, allocationFunctionIndex source < inst.TYPES.length) :
    fun_allocfuncs s inst sources
      ({s with FUNCS := s.FUNCS ++ sources.map (allocationFunction inst)}, List.range' s.FUNCS.length sources.length) := by
  induction sources generalizing s with
  | nil => simpa using fun_allocfuncs.fun_allocfuncs_case_0 s inst
  | cons source sources ih =>
    have one := allocate_function s inst source instanceWf (sourceWf source (by simp)) (bounds source (by simp))
    have rest := ih {s with FUNCS := s.FUNCS ++ [allocationFunction inst source]}
      (fun f hf => sourceWf f (by simp [hf])) (fun f hf => bounds f (by simp [hf]))
    simpa only [List.map_cons, List.length_cons, List.range'_succ, List.length_append,
      List.length_singleton, List.length_nil, Nat.zero_add, List.append_assoc, List.singleton_append] using
      fun_allocfuncs.fun_allocfuncs_case_1 s inst source sources _ _ _ _ _ _ rest one rfl rfl

theorem allocate_globals (s : store) (values : List globalinst)
    (wf : Forall wf_globalinst values) :
    fun_allocglobals s (values.map globalinst.TYPE) (values.map globalinst.VALUE)
      ({s with GLOBALS := s.GLOBALS ++ values}, List.range' s.GLOBALS.length values.length) := by
  induction values generalizing s with
  | nil => simpa using fun_allocglobals.fun_allocglobals_case_0 s
  | cons value values ih =>
    have one := allocate_global s value (wf value (by simp))
    have rest := ih {s with GLOBALS := s.GLOBALS ++ [value]}
      (fun value member => wf value (by simp [member]))
    simpa only [List.map_cons, List.length_cons, List.range'_succ, List.length_append,
      List.length_singleton, List.length_nil, Nat.zero_add, List.append_assoc, List.singleton_append] using
      fun_allocglobals.fun_allocglobals_case_1 s value.TYPE (values.map globalinst.TYPE) value.VALUE (values.map globalinst.VALUE) _ _ _ _ _ _ rest one rfl rfl

theorem allocate_tables (s : store) (values : List tabletype)
    (wf : Forall wf_tabletype values) :
    fun_alloctables s (values)
      ({s with TABLES := s.TABLES ++ values.map allocationTable}, List.range' s.TABLES.length values.length) := by
  induction values generalizing s with
  | nil => simpa using fun_alloctables.fun_alloctables_case_0 s
  | cons value values ih =>
    have one := allocate_table s value (wf value (by simp))
    have rest := ih {s with TABLES := s.TABLES ++ [allocationTable value]}
      (fun value member => wf value (by simp [member]))
    simpa only [List.map_cons, List.length_cons, List.range'_succ, List.length_append,
      List.length_singleton, List.length_nil, Nat.zero_add, List.append_assoc, List.singleton_append] using
      fun_alloctables.fun_alloctables_case_1 s value values _ _ _ _ _ _ rest one rfl rfl

theorem allocate_memories (s : store) (values : List memtype)
    (wf : Forall wf_memtype values) :
    fun_allocmems s (values)
      ({s with MEMS := s.MEMS ++ values.map allocationMemory}, List.range' s.MEMS.length values.length) := by
  induction values generalizing s with
  | nil => simpa using fun_allocmems.fun_allocmems_case_0 s
  | cons value values ih =>
    have one := allocate_memory s value (wf value (by simp))
    have rest := ih {s with MEMS := s.MEMS ++ [allocationMemory value]}
      (fun value member => wf value (by simp [member]))
    simpa only [List.map_cons, List.length_cons, List.range'_succ, List.length_append,
      List.length_singleton, List.length_nil, Nat.zero_add, List.append_assoc, List.singleton_append] using
      fun_allocmems.fun_allocmems_case_1 s value values _ _ _ _ _ _ rest one rfl rfl

theorem allocate_elements (s : store) (values : List eleminst) :
    fun_allocelems s (values.map eleminst.TYPE) (values.map eleminst.REFS)
      ({s with ELEMS := s.ELEMS ++ values}, List.range' s.ELEMS.length values.length) := by
  induction values generalizing s with
  | nil => simpa using fun_allocelems.fun_allocelems_case_0 s
  | cons value values ih =>
    have one := allocate_element s value
    have rest := ih {s with ELEMS := s.ELEMS ++ [value]}
    simpa only [List.map_cons, List.length_cons, List.range'_succ, List.length_append,
      List.length_singleton, List.length_nil, Nat.zero_add, List.append_assoc, List.singleton_append] using
      fun_allocelems.fun_allocelems_case_1 s value.TYPE (values.map eleminst.TYPE) value.REFS (values.map eleminst.REFS) _ _ _ _ _ _ rest one rfl rfl

theorem allocate_datas (s : store) (values : List datainst)
    (wf : Forall wf_datainst values) :
    fun_allocdatas s (values.map datainst.BYTES)
      ({s with DATAS := s.DATAS ++ values}, List.range' s.DATAS.length values.length) := by
  induction values generalizing s with
  | nil => simpa using fun_allocdatas.fun_allocdatas_case_0 s
  | cons value values ih =>
    have one := allocate_data s value (wf value (by simp))
    have rest := ih {s with DATAS := s.DATAS ++ [value]}
      (fun value member => wf value (by simp [member]))
    simpa only [List.map_cons, List.length_cons, List.range'_succ, List.length_append,
      List.length_singleton, List.length_nil, Nat.zero_add, List.append_assoc, List.singleton_append] using
      fun_allocdatas.fun_allocdatas_case_1 s value.BYTES (values.map datainst.BYTES) _ _ _ _ _ _ rest one rfl rfl

end Exec.Spec
