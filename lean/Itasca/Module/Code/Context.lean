import Itasca.Module.Code.BodyContext
import Itasca.Binary.Module
import Itasca.Module.Code.BodyContextComplete
import Itasca.Profile.Instructions
import Itasca.Spec.DeclaredReferences

/-!
# Code entry typing contexts

`ModuleContext` and `SegmentContext` describe the module-level typing context a code entry is
checked in. `bodyContext` is the context a function body is typed in, `Typed` is the declarative
certificate for one code entry, and `typed_func_ok` and `Typed.func_ok` turn it into the generated
`Func_ok` in the full module context. `body_context` identifies the extracted frame with
`bodyContext`.
-/

open Aeneas Aeneas.Std

namespace Itasca.CodeEntry

/-- The context `C` has the module's types, functions, globals, tables and memories translated from
`env`, with empty local and label spaces. -/
structure ModuleContext (env : module.Env) (C : context) : Prop where
  types : C.TYPES = env.types.val.map EnvTranslation.funcType
  funcs : C.FUNCS = env.func_types.val.map EnvTranslation.funcType
  globals : C.GLOBALS = env.global_types.val.map Translate.globalType
  tables : C.TABLES = env.table_types.val.map EnvTranslation.tableType
  mems : C.MEMS = env.mem_types.val.map EnvTranslation.memType
  locals : C.LOCALS = []
  labels : C.LABELS = []

/-- The final element and data spaces of `C` extend those available while validating a body. The
data count section supplies the body-visible data space. -/
structure SegmentContext (env : module.Env) (C : context) : Prop where
  elems : (EnvTranslation.elementTypes env).IsPrefix C.ELEMS
  datas : (EnvTranslation.dataTypes env).IsPrefix C.DATAS

/-- The typing context of a function body: the module's index spaces, the parameters followed by
the declared locals, and a single label and the return type both given by the results. -/
def bodyContext (env : module.Env) (params declared results : List types.ValueType) : context :=
  { TYPES := env.types.val.map EnvTranslation.funcType
    FUNCS := env.func_types.val.map EnvTranslation.funcType
    GLOBALS := env.global_types.val.map Translate.globalType
    TABLES := env.table_types.val.map EnvTranslation.tableType
    MEMS := env.mem_types.val.map EnvTranslation.memType
    ELEMS := EnvTranslation.elementTypes env
    DATAS := EnvTranslation.dataTypes env
    LOCALS := (params ++ declared).map Translate.valueType
    LABELS := [.mk_list (results.map Translate.valueType)]
    RETURN := some (.mk_list (results.map Translate.valueType)) }

/-- The type `[] -> results` that a body must have. -/
def instructionType (ft : types.FuncType) : functype :=
  .mk_functype (.mk_list []) (.mk_list (ft.results.val.map Translate.valueType))

/-- The code entry has a function type in the environment's type table. Its body is typed in
`bodyContext` with the parameters followed by the declared locals, is admitted by the profile, uses
allowed local types, and mentions only declared function references. -/
structure Typed (env : module.Env) (typeIdx : U32) (entry : ModuleBinary.Code)
    (validationProfile : ValidationProfile := .Wasm1) : Prop where
  type_lt : typeIdx.val < env.types.val.length
  typed : Instrs_ok (bodyContext env env.types.val[typeIdx.val].params.val
    entry.declared env.types.val[typeIdx.val].results.val) entry.body
    (instructionType env.types.val[typeIdx.val])
  profile : Profile.Instructions validationProfile (bodyContext env env.types.val[typeIdx.val].params.val
    entry.declared env.types.val[typeIdx.val].results.val) entry.body
  locals_allowed : ∀ group ∈ entry.locals, ModuleBinary.ValueTypeAllowed validationProfile group.2
  declared : DeclaredReferences.Instructions
    (env.declared_funcs.val.map (fun idx => uN.mk_uN idx.val)) entry.body

/-- The SpecTec function for a code entry with type index `typeIdx`. -/
def function (typeIdx : U32) (entry : ModuleBinary.Code) : func :=
  .FUNC (.mk_uN typeIdx.val) (entry.declared.map (fun t => .LOCAL (Translate.valueType t))) entry.body

/-- A typed body in an environment without a data count contains no data-index instruction,
regardless of control nesting or stack reachability. -/
theorem Typed.no_data {env typeIdx entry profile} (h : Typed env typeIdx entry profile)
    (hcount : env.data_count = none) : ModuleBinary.instructionsUseData entry.body = false :=
  ModuleBinary.typed_no_data h.typed (by simp [bodyContext, EnvTranslation.dataTypes, hcount])

/-- A module context is well formed. -/
theorem ModuleContext.wf {env C} (h : ModuleContext env C) : wf_context C := by
  have ht := h.tables
  have hm := h.mems
  cases C
  constructor
  · dsimp only at ht
    rw [ht]
    simp only [Forall, List.mem_map]
    rintro _ ⟨tt, _, rfl⟩
    exact EnvTranslation.tableType_wf tt
  · dsimp only at hm
    rw [hm]
    simp only [Forall, List.mem_map]
    rintro _ ⟨mt, _, rfl⟩
    exact EnvTranslation.memType_wf mt

/-- A body typed in `bodyContext` gives the generated function typing `Func_ok` in any full module
context `C` whose segment spaces extend those of the body. -/
theorem typed_func_ok {env : module.Env} {typeIdx : U32} {entry : ModuleBinary.Code}
    (hindex : typeIdx.val < env.types.val.length)
    (htyped : Instrs_ok (bodyContext env env.types.val[typeIdx.val].params.val
      entry.declared env.types.val[typeIdx.val].results.val) entry.body
      (instructionType env.types.val[typeIdx.val])) (C : context) (hc : ModuleContext env C)
    (hsegments : SegmentContext env C) :
    Func_ok C (function typeIdx entry) (EnvTranslation.funcType (env.types.val[typeIdx.val]'hindex)) := by
  let ft := env.types.val[typeIdx.val]'hindex
  let ps := ft.params.val.map Translate.valueType
  let ds := entry.declared.map Translate.valueType
  let rs := ft.results.val.map Translate.valueType
  let localC : context := ⟨[], [], [], [], [], [], [], ps ++ ds, [.mk_list rs], some (.mk_list rs)⟩
  have hlwf : wf_context localC := by constructor <;> simp [Forall]
  have hcore : BodyContext.SameCore
      (bodyContext env ft.params.val entry.declared ft.results.val) (localC ++ C) := by
    constructor
    · exact hc.types.symm
    · exact hc.funcs.symm
    · exact hc.globals.symm
    · exact hc.tables.symm
    · exact hc.mems.symm
    · change (ft.params.val ++ entry.declared).map Translate.valueType = (ps ++ ds) ++ C.LOCALS
      simp [hc.locals, ps, ds]
    · change [.mk_list rs] = [.mk_list rs] ++ C.LABELS
      simp [hc.labels]
    · rfl
  have ht := BodyContext.instrs_transport_extend (D := localC ++ C) htyped
    hsegments.elems hsegments.datas hcore
  have hw := (DeclarativeComplete.wellFormed htyped).2
  have he : Expr_ok (localC ++ C) entry.body (.mk_list rs) :=
    .mk_Expr_ok _ _ _ ht
      ((DeclarativeComplete.wellFormed ht).1) hw
  have hn : Forall (fun t => t ≠ valtype.BOT) ds := by
    simp only [ds, Forall, List.mem_map]
    rintro _ ⟨t, _, rfl⟩
    cases t <;> simp [Translate.valueType]
  have hi : typeIdx.val < C.TYPES.length := by simpa [hc.types] using hindex
  have hlookup : C.TYPES[typeIdx.val]! = EnvTranslation.funcType ft := by
    rw [hc.types, getElem!_pos _ _ (by simpa using hindex), List.getElem_map]
  have hf : wf_func (function typeIdx entry) :=
    .func_case_0 _ _ _ (EnvTranslation.index_wf typeIdx) hw
  simpa only [function, EnvTranslation.funcType, Map, List.map_map,
    Function.comp_def, ds, ps, rs, ft, localC] using
    Func_ok.mk_Func_ok C (.mk_uN typeIdx.val) ds entry.body ps rs hi hlookup hn he hc.wf (by simpa [function, Map, ds, List.map_map, Function.comp_def] using hf) hlwf

/-- A `Typed` certificate in either profile gives `Func_ok` in the full module context. -/
theorem Typed.func_ok {env : module.Env} {typeIdx : U32} {entry : ModuleBinary.Code}
    {profile : ValidationProfile} (h : Typed env typeIdx entry profile) (C : context) (hc : ModuleContext env C)
    (hsegments : SegmentContext env C) :
    Func_ok C (function typeIdx entry) (EnvTranslation.funcType (env.types.val[typeIdx.val]'h.type_lt)) :=
  typed_func_ok h.type_lt h.typed C hc hsegments

/-- The body frame of the extracted context is `bodyContext` when its locals and results are the
vectors that the code-entry validator builds. -/
theorem body_context {env : module.Env} {ctx : code.Context} {bt : code.BlockType}
    {params declared results : List types.ValueType}
    (hl : ctx.locals.val = params ++ declared) (hr : ctx.results.val = results)
    (hbt : results = Control.results bt) :
    Wasm1.Frames.enter (EnvTranslation.context env ctx) .body bt =
      bodyContext env params declared results := by
  cases env
  cases ctx
  simp_all [Wasm1.Frames.enter, Wasm1.Frames.Form.label, Control.labelContext,
    EnvTranslation.context, bodyContext, Control.resultTypes]
  rfl

end Itasca.CodeEntry
