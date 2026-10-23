import Itasca.Module.Const.Inversion

/-!
# Inversion of section typing

Recovers the semantic requirements of each declaration section from the generated typing
judgments. `limits_valid_of_typing`, `global_valid_of_typing`, `export_resolves_of_typing`,
`start_valid_of_typing`, `data_valid_of_typing` and `element_valid_raw_of_typing` turn `Limits_ok`,
`Global_ok`, `Export_ok`, `Start_ok`, `Data_ok` and `Elem_ok` into the validity statements used by
`ModuleEnv.Requirements`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleElaboration

/-- Inversion of `Limits_ok`: the minimum and any maximum are within the bound and ordered. -/
theorem limits_constraints {lim : limits} {bound : Nat} (h : Limits_ok lim bound) :
    match lim with
    | .mk_limits minimum maximum => proj_uN_0 minimum ≤ bound ∧
        ∀ m ∈ maximum, proj_uN_0 minimum ≤ proj_uN_0 m ∧ proj_uN_0 m ≤ bound := by
  cases h with
  | mk_Limits_ok n maximum bound hn hm hw =>
    cases maximum <;> simpa [OMap, Forall, proj_uN_0] using And.intro hn hm

/-- Typed limits are valid in the byte-level sense. -/
theorem limits_valid_of_typing {lim : types.Limits} {bound : Nat}
    (h : Limits_ok (EnvTranslation.limitsType lim) bound) : ModuleTranslation.LimitsValid lim bound := by
  have hc := limits_constraints h
  simpa [EnvTranslation.limitsType, proj_uN_0, ModuleTranslation.LimitsValid] using hc

/-- A typed table type has valid limits for the table size bound. -/
theorem table_valid_of_typing {tt : types.TableType}
    (h : Tabletype_ok (EnvTranslation.tableType tt)) :
    ModuleTranslation.LimitsValid tt.limits (2 ^ 32 - 1) := by
  cases h with
  | mk_Tabletype_ok _ _ h _ => simpa using limits_valid_of_typing h

/-- A typed memory type has valid limits for the memory page bound. -/
theorem memory_valid_of_typing {mt : types.MemType}
    (h : Memtype_ok (EnvTranslation.memType mt)) :
    ModuleTranslation.LimitsValid mt.limits (2 ^ 16) := by
  cases h with
  | mk_Memtype_ok _ h _ => exact limits_valid_of_typing h

/-- A typed global has a typed constant initializer of its value type. -/
theorem global_expr_typed {C : context} {g : module.Global}
    (h : Global_ok C (ModuleConstants.global g) (Translate.globalType g.gtype)) :
    Expr_ok_const C (ModuleConstants.expression g.init) (Translate.valueType g.gtype.valtype) := by
  cases h
  rename_i m t hwC hgt he ht hwg
  have hety : Translate.valueType g.gtype.valtype = t := (globaltype.mk_globaltype.inj he).2
  simpa [hety] using ht

/-- A typed global has a valid initializer in the environment. -/
theorem global_valid_of_typing {env : module.Env} {C : context} {g : module.Global}
    (hg : ModuleConstants.GlobalContext env C)
    (hf : ModuleConstants.FunctionContext env C)
    (h : Global_ok C (ModuleConstants.global g) (Translate.globalType g.gtype)) :
    ModuleConstants.Valid env g.init g.gtype.valtype :=
  ModuleConstants.valid_of_typing hg hf (global_expr_typed h)

/-- Inversion of `Start_ok`: the start function exists and has type `[] -> []`. -/
theorem start_signature {C : context} {s : _root_.start} (h : Start_ok C s) :
    match s with
    | .START idx => proj_uN_0 idx < C.FUNCS.length ∧
        C.FUNCS[proj_uN_0 idx]! = .mk_functype (.mk_list []) (.mk_list []) := by
  cases h
  exact ⟨by assumption, by assumption⟩

/-- A typed start function is a function of the environment with no parameters or results. -/
theorem start_valid_of_typing {env : module.Env} {C : context} {idx : U32}
    (hc : CodeEntry.ModuleContext env C) (h : Start_ok C (start idx)) :
    ∃ hi : idx.val < env.func_types.val.length,
      env.func_types.val[idx.val].params.val = [] ∧ env.func_types.val[idx.val].results.val = [] := by
  obtain ⟨hi, he⟩ := start_signature h
  have hb : idx.val < env.func_types.val.length := by simpa [hc.funcs, proj_uN_0] using hi
  change C.FUNCS[idx.val]! = _ at he
  rw [hc.funcs, getElem!_pos _ _ (by simpa using hb), List.getElem_map] at he
  obtain ⟨hp, hr⟩ := functype.mk_functype.inj he
  exact ⟨hb, List.map_eq_nil_iff.mp (list.mk_list.inj hp), List.map_eq_nil_iff.mp (list.mk_list.inj hr)⟩

/-- Inversion of `Datamode_ok`: an active segment uses memory `0` with a constant `i32` offset. -/
theorem datamode_active_properties {C : context} {mode : datamode} (h : Datamode_ok C mode) :
    match mode with
    | .ACTIVE idx expr => idx = .mk_uN 0 ∧ 0 < C.MEMS.length ∧ Expr_ok_const C expr .I32
    | .PASSIVE => True := by
  cases h
  · exact ⟨rfl, by assumption, by assumption⟩
  · trivial

/-- A typed data segment has a typed mode. -/
theorem data_mode_typed {C : context} {d : _root_.data} (h : Data_ok C d) :
    match d with | .DATA _ mode => Datamode_ok C mode := by cases h; assumption

/-- A typed data segment is valid in the environment. -/
theorem data_valid_of_typing {env : module.Env} {C : context} {entry : module.Data}
    (hg : ModuleConstants.GlobalContext env C)
    (hf : ModuleConstants.FunctionContext env C)
    (hm : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (h : Data_ok C (ModuleData.translate (ModuleData.raw entry))) : ModuleData.Valid env entry := by
  have hmode : Datamode_ok C (ModuleSegments.dataMode entry.mode) := data_mode_typed h
  cases he : entry.mode with
  | Passive => simp [ModuleData.Valid, he]
  | Active idx offset =>
    rw [he] at hmode
    obtain ⟨hi, hn, ht⟩ := datamode_active_properties hmode
    have hidx : idx.val = 0 := uN.mk_uN.inj hi
    simpa only [ModuleData.Valid, he] using
      (And.intro (show idx.val < env.mem_types.val.length by simpa [hm, hidx] using hn)
        (ModuleConstants.valid_of_typing hg hf ht))

/-- Inversion of `Elem_ok`: the initializers are constant expressions of the reference type and
the mode is typed. -/
theorem element_parts {C : context} {e : elem} {rt} (h : Elem_ok C e rt) :
    match e with
    | .ELEM _ exprs mode => Forall (fun expr => Expr_ok_const C expr (valtype_reftype rt)) exprs ∧
        Elemmode_ok C mode rt := by
  cases h
  exact ⟨by assumption, by assumption⟩

/-- A typed raw element segment satisfies the element validity requirement. -/
theorem element_valid_raw_of_typing {env : module.Env} {C : context} {entry : ModuleBinary.Element}
    (hg : ModuleConstants.GlobalContext env C)
    (hf : ModuleConstants.FunctionContext env C)
    (ht : C.TABLES = env.table_types.val.map EnvTranslation.tableType)
    (h : Elem_ok C (element entry) (Translate.referenceType entry.elem)) :
    (match entry.mode with
      | .Active idx offset => ∃ hi : idx.val < env.table_types.val.length,
          env.table_types.val[idx.val].elem = entry.elem ∧ ModuleConstants.Valid env offset .I32
      | .Passive | .Declarative => True) ∧
    ∀ init ∈ entry.init, ModuleConstants.Valid env init (ModuleConstants.referenceValueType entry.elem) := by
  obtain ⟨hexprs, hmode⟩ := element_parts h
  constructor
  · cases hm : entry.mode with
    | Passive => trivial
    | Declarative => trivial
    | Active idx offset =>
      change Elemmode_ok C (ModuleSegments.elementMode entry.mode) (Translate.referenceType entry.elem) at hmode
      rw [hm] at hmode
      cases hmode with
      | active _ _ _ lim hi hlookup hconst _ _ _ =>
        have hb : idx.val < env.table_types.val.length := by simpa [ht, proj_uN_0] using hi
        refine ⟨hb, ?_, ModuleConstants.valid_of_typing hg hf hconst⟩
        change C.TABLES[idx.val]! = _ at hlookup
        rw [ht, getElem!_pos _ _ (by simpa using hb), List.getElem_map] at hlookup
        have href := (tabletype.mk_tabletype.inj hlookup).2
        have hinj : Function.Injective Translate.referenceType := by
          intro a b he
          cases a <;> cases b <;> simp_all [Translate.referenceType]
        exact hinj href
  · intro init hi
    have he := hexprs _ (List.mem_map.mpr ⟨init, hi, rfl⟩)
    have hty : valtype_reftype (Translate.referenceType entry.elem) =
        Translate.valueType (ModuleConstants.referenceValueType entry.elem) := by cases entry.elem <;> rfl
    exact ModuleConstants.valid_of_typing hg hf (hty ▸ he)

end Itasca.ModuleElaboration
