import Itasca.Module.Const.Inversion

open Aeneas Aeneas.Std

namespace Itasca.ModuleElaboration

theorem limits_constraints {lim : limits} {bound : Nat} (h : Limits_ok lim bound) :
    match lim with
    | .mk_limits minimum maximum => proj_uN_0 minimum ≤ bound ∧
        ∀ m ∈ maximum, proj_uN_0 minimum ≤ proj_uN_0 m ∧ proj_uN_0 m ≤ bound := by
  cases h with
  | mk_Limits_ok n maximum bound hn hm hw =>
    cases maximum <;> simpa [OMap, Forall, proj_uN_0] using And.intro hn hm

theorem limits_valid_of_typing {lim : types.Limits} {bound : Nat}
    (h : Limits_ok (EnvTranslation.limitsType lim) bound) : ModuleTranslation.LimitsValid lim bound := by
  have hc := limits_constraints h
  simpa [EnvTranslation.limitsType, proj_uN_0, ModuleTranslation.LimitsValid] using hc

theorem table_valid_of_typing {tt : types.TableType}
    (h : Tabletype_ok (EnvTranslation.tableType tt)) :
    ModuleTranslation.LimitsValid tt.limits (2 ^ 32 - 1) := by
  cases h with
  | mk_Tabletype_ok _ _ h _ => simpa using limits_valid_of_typing h

theorem memory_valid_of_typing {mt : types.MemType}
    (h : Memtype_ok (EnvTranslation.memType mt)) :
    ModuleTranslation.LimitsValid mt.limits (2 ^ 16) := by
  cases h with
  | mk_Memtype_ok _ h _ => exact limits_valid_of_typing h

theorem global_expr_typed {C : context} {g : module.Global}
    (h : Global_ok C (ModuleConstants.global g) (Translate.globalType g.gtype)) :
    Expr_ok_const C (ModuleConstants.expression g.init) (Translate.valueType g.gtype.valtype) := by
  cases h
  rename_i m t hwC hgt he ht hwg
  have hety : Translate.valueType g.gtype.valtype = t := (globaltype.mk_globaltype.inj he).2
  simpa [hety] using ht

theorem global_valid_of_typing {env : module.Env} {C : context} {g : module.Global}
    (hg : ModuleConstants.GlobalContext env C)
    (hf : ModuleConstants.FunctionContext env C)
    (h : Global_ok C (ModuleConstants.global g) (Translate.globalType g.gtype)) :
    ModuleConstants.Valid env g.init g.gtype.valtype :=
  ModuleConstants.valid_of_typing hg hf (global_expr_typed h)

theorem export_resolves_of_typing {env : module.Env} {C : context} {entry : module.Export} {xt}
    (hc : CodeEntry.ModuleContext env C)
    (h : Export_ok C (exportDecl (ModuleEnv.rawExport entry)) xt) :
    ∃ actual, ModuleExternals.ExportResolves env entry actual ∧ ModuleExternals.externalType actual = xt := by
  have hx : Externidx_ok C (exportIndex entry.desc) xt := by cases h; assumption
  cases hd : entry.desc <;> simp only [hd, exportIndex] at hx
  · rename_i idx
    cases hx with
    | func _ ft hi he hw hf ht =>
      have hb : idx.val < env.func_types.val.length := by simpa [hc.funcs, proj_uN_0] using hi
      refine ⟨.Func env.func_types.val[idx.val], ?_, ?_⟩
      · simp only [ModuleExternals.ExportResolves, hd]
        exact ⟨hb, trivial⟩
      · simp only [ModuleExternals.externalType]
        congr 1
        change C.FUNCS[idx.val]! = ft at he
        rw [hc.funcs, getElem!_pos _ _ (by simpa using hb), List.getElem_map] at he
        exact he
  · rename_i idx
    cases hx with
    | table _ tt hi he hw hf ht =>
      have hb : idx.val < env.table_types.val.length := by simpa [hc.tables, proj_uN_0] using hi
      refine ⟨.Table env.table_types.val[idx.val], ?_, ?_⟩
      · simp only [ModuleExternals.ExportResolves, hd]
        exact ⟨hb, trivial⟩
      · simp only [ModuleExternals.externalType]
        congr 1
        change C.TABLES[idx.val]! = tt at he
        rw [hc.tables, getElem!_pos _ _ (by simpa using hb), List.getElem_map] at he
        exact he
  · rename_i idx
    cases hx with
    | mem _ mt hi he hw hf ht =>
      have hb : idx.val < env.mem_types.val.length := by simpa [hc.mems, proj_uN_0] using hi
      refine ⟨.Memory env.mem_types.val[idx.val], ?_, ?_⟩
      · simp only [ModuleExternals.ExportResolves, hd]
        exact ⟨hb, trivial⟩
      · simp only [ModuleExternals.externalType]
        congr 1
        change C.MEMS[idx.val]! = mt at he
        rw [hc.mems, getElem!_pos _ _ (by simpa using hb), List.getElem_map] at he
        exact he
  · rename_i idx
    cases hx with
    | global _ gt hi he hw hf ht =>
      have hb : idx.val < env.global_types.val.length := by simpa [hc.globals, proj_uN_0] using hi
      refine ⟨.Global env.global_types.val[idx.val], ?_, ?_⟩
      · simp only [ModuleExternals.ExportResolves, hd]
        exact ⟨hb, trivial⟩
      · simp only [ModuleExternals.externalType]
        congr 1
        change C.GLOBALS[idx.val]! = gt at he
        rw [hc.globals, getElem!_pos _ _ (by simpa using hb), List.getElem_map] at he
        exact he

theorem start_signature {C : context} {s : _root_.start} (h : Start_ok C s) :
    match s with
    | .START idx => proj_uN_0 idx < C.FUNCS.length ∧
        C.FUNCS[proj_uN_0 idx]! = .mk_functype (.mk_list []) (.mk_list []) := by
  cases h
  exact ⟨by assumption, by assumption⟩

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

theorem datamode_active_properties {C : context} {mode : datamode} (h : Datamode_ok C mode) :
    match mode with
    | .ACTIVE idx expr => idx = .mk_uN 0 ∧ 0 < C.MEMS.length ∧ Expr_ok_const C expr .I32
    | .PASSIVE => True := by
  cases h
  · exact ⟨rfl, by assumption, by assumption⟩
  · trivial

theorem data_mode_typed {C : context} {d : _root_.data} (h : Data_ok C d) :
    match d with | .DATA _ mode => Datamode_ok C mode := by cases h; assumption

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

theorem elemmode_active_properties {C : context} {mode : elemmode} {rt}
    (h : Elemmode_ok C mode rt) :
    match mode with
    | .ACTIVE idx expr => proj_uN_0 idx < C.TABLES.length ∧ Expr_ok_const C expr .I32
    | .PASSIVE | .DECLARE => True := by
  cases h
  · exact ⟨by assumption, by assumption⟩
  · trivial
  · trivial

theorem element_parts {C : context} {e : elem} {rt} (h : Elem_ok C e rt) :
    match e with
    | .ELEM _ exprs mode => Forall (fun expr => Expr_ok_const C expr (valtype_reftype rt)) exprs ∧
        Elemmode_ok C mode rt := by
  cases h
  exact ⟨by assumption, by assumption⟩

theorem ref_func_index {C : context} {idx : U32} {ty}
    (h : Expr_ok_const C [instr.REF_FUNC (.mk_uN idx.val)] ty) : idx.val < C.FUNCS.length := by
  have hs : Instrs_ok C [instr.REF_FUNC (.mk_uN idx.val)] (.mk_functype (.mk_list []) (.mk_list [ty])) := by
    cases h
    rename_i he _ _ _
    cases he
    assumption
  obtain ⟨_, _, _, hp, _, _⟩ := DeclarativeComplete.singleton hs
  cases hp
  assumption

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
