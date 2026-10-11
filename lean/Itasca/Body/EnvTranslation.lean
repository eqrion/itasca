import Itasca.Body.Block

open Aeneas Aeneas.Std

namespace Itasca.EnvTranslation

def funcType (ft : types.FuncType) : functype :=
  .mk_functype (.mk_list (ft.params.val.map Translate.valueType))
    (.mk_list (ft.results.val.map Translate.valueType))

def limitsType (lim : types.Limits) : limits :=
  .mk_limits (.mk_uN lim.min.val) (lim.max.map fun x => .mk_uN x.val)

def tableType (tt : types.TableType) : tabletype :=
  .mk_tabletype (limitsType tt.limits) (Translate.referenceType tt.elem)

def memType (mt : types.MemType) : memtype := .PAGE (limitsType mt.limits)

def elementTypes (env : module.Env) : List elemtype :=
  env.elements.val.map (fun entry => Translate.referenceType entry.elem)

def dataTypes (env : module.Env) : List datatype :=
  List.replicate ((env.data_count.map (fun count => count.val)).getD 0) .OK

/-- The body validator uses the environment's resolved function-type cache. Its
    coherence with the module's type indices is a separate module invariant. -/
def context (env : module.Env) (ctx : code.Context) : _root_.context :=
  { TYPES := env.types.val.map funcType
    FUNCS := env.func_types.val.map funcType
    GLOBALS := env.global_types.val.map Translate.globalType
    TABLES := env.table_types.val.map tableType
    MEMS := env.mem_types.val.map memType
    ELEMS := elementTypes env
    DATAS := dataTypes env
    LOCALS := ctx.locals.val.map Translate.valueType
    LABELS := []
    RETURN := some (.mk_list (ctx.results.val.map Translate.valueType)) }

theorem index_wf (x : U32) : wf_uN 32 (.mk_uN x.val) := by
  apply wf_uN.uN_case_0
  have h := x.hmax
  norm_num at h ⊢
  omega

theorem limitsType_wf (lim : types.Limits) : wf_limits (limitsType lim) := by
  constructor
  · exact index_wf _
  · cases h : lim.max with
    | none => simp [Forall]
    | some x => simpa [Forall] using index_wf x

theorem tableType_wf (tt : types.TableType) : wf_tabletype (tableType tt) :=
  .tabletype_case_0 _ _ (limitsType_wf _)

theorem memType_wf (mt : types.MemType) : wf_memtype (memType mt) :=
  .memtype_case_0 _ (limitsType_wf _)

/-- Syntactic well-formedness needs no module validity assumptions. -/
theorem context_wf (env : module.Env) (ctx : code.Context) :
    wf_context (context env ctx) := by
  constructor
  · simp only [Forall, List.mem_map]
    rintro _ ⟨tt, _, rfl⟩
    exact tableType_wf tt
  · simp only [Forall, List.mem_map]
    rintro _ ⟨mt, _, rfl⟩
    exact memType_wf mt

/-- Static fields stay fixed while structured control adds and removes labels. -/
structure Matches (env : module.Env) (ctx : code.Context) (C : _root_.context) : Prop where
  types : C.TYPES = env.types.val.map funcType
  funcs : C.FUNCS = env.func_types.val.map funcType
  globals : C.GLOBALS = env.global_types.val.map Translate.globalType
  tables : C.TABLES = env.table_types.val.map tableType
  mems : C.MEMS = env.mem_types.val.map memType
  elems : C.ELEMS = elementTypes env
  datas : C.DATAS = dataTypes env
  locals : C.LOCALS = ctx.locals.val.map Translate.valueType
  ret : C.RETURN = some (.mk_list (ctx.results.val.map Translate.valueType))

theorem Matches.root (env : module.Env) (ctx : code.Context) :
    Matches env ctx (context env ctx) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Matches.enter {env ctx C} (h : Matches env ctx C) (ts : List valtype) :
    Matches env ctx (Control.labelContext ts ++ C) := by
  exact ⟨h.types, h.funcs, h.globals, h.tables, h.mems, h.elems, h.datas, h.locals, h.ret⟩

theorem Matches.wf {env ctx C} (h : Matches env ctx C) : wf_context C := by
  cases C
  constructor
  · have ht := h.tables
    dsimp only at ht
    rw [ht]
    simp only [Forall, List.mem_map]
    rintro _ ⟨tt, _, rfl⟩
    exact tableType_wf tt
  · have hm := h.mems
    dsimp only at hm
    rw [hm]
    simp only [Forall, List.mem_map]
    rintro _ ⟨mt, _, rfl⟩
    exact memType_wf mt

theorem Matches.local {env ctx C} (h : Matches env ctx C)
    (idx : U32) (t : types.ValueType) (hi : idx.val < ctx.locals.val.length)
    (ht : ctx.locals.val[idx.val] = t) :
    idx.val < C.LOCALS.length ∧ C.LOCALS[idx.val]! = Translate.valueType t := by
  rw [h.locals]
  constructor
  · simpa using hi
  · rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map, ht]

theorem Matches.global {env ctx C} (h : Matches env ctx C)
    (idx : U32) (gt : types.GlobalType) (hi : idx.val < env.global_types.val.length)
    (ht : env.global_types.val[idx.val] = gt) :
    idx.val < C.GLOBALS.length ∧ C.GLOBALS[idx.val]! = Translate.globalType gt := by
  rw [h.globals]
  constructor
  · simpa using hi
  · rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map, ht]

theorem Matches.local_get {env ctx C} (h : Matches env ctx C)
    (idx : U32) (t : types.ValueType) (hi : idx.val < ctx.locals.val.length)
    (ht : ctx.locals.val[idx.val] = t) :
    Instr_ok C (.LOCAL_GET (.mk_uN idx.val))
      (.mk_functype (.mk_list []) (.mk_list [Translate.valueType t])) := by
  obtain ⟨hb, he⟩ := h.local idx t hi ht
  exact .local_get C _ _ hb he h.wf (.instr_case_43 _ (index_wf idx))

theorem Matches.local_set {env ctx C} (h : Matches env ctx C)
    (idx : U32) (t : types.ValueType) (hi : idx.val < ctx.locals.val.length)
    (ht : ctx.locals.val[idx.val] = t) :
    Instr_ok C (.LOCAL_SET (.mk_uN idx.val))
      (.mk_functype (.mk_list [Translate.valueType t]) (.mk_list [])) := by
  obtain ⟨hb, he⟩ := h.local idx t hi ht
  exact .local_set C _ _ hb he h.wf (.instr_case_44 _ (index_wf idx))

theorem Matches.local_tee {env ctx C} (h : Matches env ctx C)
    (idx : U32) (t : types.ValueType) (hi : idx.val < ctx.locals.val.length)
    (ht : ctx.locals.val[idx.val] = t) :
    Instr_ok C (.LOCAL_TEE (.mk_uN idx.val))
      (.mk_functype (.mk_list [Translate.valueType t]) (.mk_list [Translate.valueType t])) := by
  obtain ⟨hb, he⟩ := h.local idx t hi ht
  exact .local_tee C _ _ hb he h.wf (.instr_case_45 _ (index_wf idx))

theorem Matches.global_get {env ctx C} (h : Matches env ctx C)
    (idx : U32) (gt : types.GlobalType) (hi : idx.val < env.global_types.val.length)
    (ht : env.global_types.val[idx.val] = gt) :
    Instr_ok C (.GLOBAL_GET (.mk_uN idx.val))
      (.mk_functype (.mk_list []) (.mk_list [Translate.valueType gt.valtype])) := by
  obtain ⟨hb, he⟩ := h.global idx gt hi ht
  exact .global_get C _ _ _ hb he h.wf (.instr_case_46 _ (index_wf idx))

theorem Matches.global_set {env ctx C} (h : Matches env ctx C)
    (idx : U32) (gt : types.GlobalType) (hi : idx.val < env.global_types.val.length)
    (ht : env.global_types.val[idx.val] = gt) (hm : gt.mutability = .Var) :
    Instr_ok C (.GLOBAL_SET (.mk_uN idx.val))
      (.mk_functype (.mk_list [Translate.valueType gt.valtype]) (.mk_list [])) := by
  obtain ⟨hb, he⟩ := h.global idx gt hi ht
  apply Instr_ok.global_set C _ _ hb _ h.wf (.instr_case_47 _ (index_wf idx))
  simpa [Translate.globalType, hm, Translate.mutability, proj_uN_0] using he

theorem Matches.call {env ctx C} (h : Matches env ctx C)
    (idx : U32) (ft : types.FuncType) (hi : idx.val < env.func_types.val.length)
    (ht : env.func_types.val[idx.val] = ft) :
    Instr_ok C (.CALL (.mk_uN idx.val)) (funcType ft) := by
  apply Instr_ok.call
  · simpa [h.funcs, proj_uN_0] using hi
  · simp only [h.funcs, proj_uN_0]
    rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map, ht]
    rfl
  · exact h.wf
  · exact .instr_case_10 _ (index_wf idx)

theorem Matches.call_indirect {env ctx C} (h : Matches env ctx C)
    (idx tableIdx : U32) (ft : types.FuncType) (hi : idx.val < env.types.val.length)
    (ht : env.types.val[idx.val] = ft)
    (htable : tableIdx.val < env.table_types.val.length)
    (hfun : env.table_types.val[tableIdx.val].elem = .FuncRef) :
    Instr_ok C (.CALL_INDIRECT (.mk_uN tableIdx.val) (.mk_uN idx.val))
      (.mk_functype (.mk_list (ft.params.val.map Translate.valueType ++ [.I32]))
        (.mk_list (ft.results.val.map Translate.valueType))) := by
  apply Instr_ok.call_indirect _ _ _ _ _ (limitsType (env.table_types.val[tableIdx.val]).limits)
  · simpa [h.tables, proj_uN_0] using htable
  · simp only [h.tables, proj_uN_0]
    rw [getElem!_pos _ _ (by simpa using htable), List.getElem_map]
    simp [tableType, hfun, Translate.referenceType]
  · simpa [h.types, proj_uN_0] using hi
  · simp only [h.types, proj_uN_0]
    rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map, ht]
    rfl
  · exact h.wf
  · exact .instr_case_11 _ _ (index_wf tableIdx) (index_wf idx)
  · exact .tabletype_case_0 _ _ (limitsType_wf _)

theorem Matches.memory_size {env ctx C} (h : Matches env ctx C)
    (hmem : 0 < env.mem_types.val.length) :
    Instr_ok C .MEMORY_SIZE (.mk_functype (.mk_list []) (.mk_list [.I32])) := by
  apply Instr_ok.memory_size _ (memType (env.mem_types.val[0]))
  · simpa [h.mems] using hmem
  · simp only [h.mems]
    rw [getElem!_pos _ _ (by simpa using hmem), List.getElem_map]
  · exact h.wf
  · exact memType_wf _
  · exact .instr_case_62

theorem Matches.memory_grow {env ctx C} (h : Matches env ctx C)
    (hmem : 0 < env.mem_types.val.length) :
    Instr_ok C .MEMORY_GROW (.mk_functype (.mk_list [.I32]) (.mk_list [.I32])) := by
  apply Instr_ok.memory_grow _ (memType (env.mem_types.val[0]))
  · simpa [h.mems] using hmem
  · simp only [h.mems]
    rw [getElem!_pos _ _ (by simpa using hmem), List.getElem_map]
  · exact h.wf
  · exact memType_wf _
  · exact .instr_case_63

end Itasca.EnvTranslation
