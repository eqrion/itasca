import Itasca.Module.Code.BodyContextComplete
import Itasca.Binary.UnicodeUnique
import Itasca.Spec.Checks
import Itasca.Module.Readers.Copies
import Itasca.Module.Readers.Basic
import Itasca.Binary.Wasm1.EncodingComplete

/-!
Sections, each formerly its own module: Context, Locals, Encoding.
-/

/-! ## Context -/

section

/-!
# Code entry typing contexts

`ModuleContext` and `SegmentContext` describe the module-level typing context a code entry is
checked in. `bodyContext` is the context a function body is typed in, `Typed` is the declarative
certificate for one code entry, and `typed_func_ok` and `Typed.func_ok` turn it into the generated
`Func_ok` in the full module context.
-/

open Aeneas Aeneas.Std

namespace Itasca.CodeEntry

/-- The context `C` has the module's types, functions, globals, tables and memories translated from
`env`, with empty local and label spaces. -/
structure ModuleContext (env : metadata.Env) (C : context) : Prop where
  types : C.TYPES = env.types.val.map EnvTranslation.funcType
  funcs : C.FUNCS = env.func_types.val.map EnvTranslation.funcType
  globals : C.GLOBALS = env.global_types.val.map Translate.globalType
  tables : C.TABLES = env.table_types.val.map EnvTranslation.tableType
  mems : C.MEMS = env.mem_types.val.map EnvTranslation.memType
  locals : C.LOCALS = []
  labels : C.LABELS = []

/-- The final element and data spaces of `C` extend those available while validating a body. The
data count section supplies the body-visible data space. -/
structure SegmentContext (env : metadata.Env) (C : context) : Prop where
  elems : (EnvTranslation.elementTypes env).IsPrefix C.ELEMS
  datas : (EnvTranslation.dataTypes env).IsPrefix C.DATAS

/-- The typing context of a function body: the module's index spaces, the parameters followed by
the declared locals, and a single label and the return type both given by the results. -/
def bodyContext (env : metadata.Env) (params declared results : List wasm_types.ValueType) : context :=
  { TYPES := env.types.val.map EnvTranslation.funcType
    FUNCS := env.func_types.val.map EnvTranslation.funcType
    GLOBALS := env.global_types.val.map Translate.globalType
    TABLES := env.table_types.val.map EnvTranslation.tableType
    MEMS := env.mem_types.val.map EnvTranslation.memType
    ELEMS := EnvTranslation.elementTypes env
    DATAS := EnvTranslation.dataTypes env
    LOCALS := (params ++ declared).map Translate.valueType
    LABELS := [.mk_list (results.map Translate.valueType)]
    RETURN := some (.mk_list (results.map Translate.valueType))}

/-- The type `[] -> results` that a body must have. -/
def instructionType (ft : wasm_types.FuncType) : functype :=
  .mk_functype (.mk_list []) (.mk_list (ft.results.val.map Translate.valueType))

/-- The code entry has a function type in the environment's type table. Its body is typed in
`bodyContext` with the parameters followed by the declared locals and mentions only
declared function references. -/
structure Typed (env : metadata.Env) (typeIdx : U32) (entry : ModuleBinary.Code) : Prop where
  type_lt : typeIdx.val < env.types.val.length
  typed : Instrs_ok (bodyContext env env.types.val[typeIdx.val].params.val
    entry.declared env.types.val[typeIdx.val].results.val) entry.body
    (instructionType env.types.val[typeIdx.val])
  declared : DeclaredReferences.Instructions
    (env.declared_funcs.val.map (fun idx => uN.mk_uN idx.val)) entry.body

/-- The SpecTec function for a code entry with type index `typeIdx`. -/
def function (typeIdx : U32) (entry : ModuleBinary.Code) : func :=
  .FUNC (.mk_uN typeIdx.val) (entry.declared.map (fun t => .LOCAL (Translate.valueType t))) entry.body

/-- A typed body in an environment without a data count contains no data-index instruction,
regardless of control nesting or stack reachability. -/
theorem Typed.no_data {env typeIdx entry} (h : Typed env typeIdx entry)
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
theorem typed_func_ok {env : metadata.Env} {typeIdx : U32} {entry : ModuleBinary.Code}
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

/-- A `Typed` certificate gives `Func_ok` in the full module context. -/
theorem Typed.func_ok {env : metadata.Env} {typeIdx : U32} {entry : ModuleBinary.Code}
     (h : Typed env typeIdx entry) (C : context) (hc : ModuleContext env C)
    (hsegments : SegmentContext env C) :
    Func_ok C (function typeIdx entry) (EnvTranslation.funcType (env.types.val[typeIdx.val]'h.type_lt)) :=
  typed_func_ok h.type_lt h.typed C hc hsegments

end Itasca.CodeEntry

end

/-! ## Locals -/

section

/-!
# Local declarations

Specifications of the extracted local-variable code used by `metadata.validate_code_entry_with`.
`metadata.decode_locals.spec` shows `metadata.decode_locals` decodes grouped local declarations into
`ModuleLocals.declared` within `limits.MAX_LOCALS`, with the independent `LocalEncoding` byte
provenance. `metadata.build_func_locals.spec` shows the function's locals are the parameters
followed by the declared locals, and `metadata.push_locals.spec` is the replication helper.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- `metadata.build_func_locals` returns the parameters followed by the declared locals. The size
bound excludes the allocation overflow possible in a caller-built oversized environment. -/
@[step]
theorem metadata.build_func_locals.spec (params declared : Slice wasm_types.ValueType)
    (hsize : params.val.length + declared.val.length ≤ Usize.max) :
    metadata.build_func_locals params declared ⦃ locals =>
      locals.val = params.val ++ declared.val ⦄ := by
  obtain ⟨out, hout, heq⟩ := WP.spec_imp_exists (metadata.copy_value_types.spec params)
  rw [metadata.build_func_locals, hout]
  simp only [bind_ok]
  simpa [metadata.build_func_locals_loop, metadata.copy_value_types_loop,
    metadata.build_func_locals_loop.body, metadata.copy_value_types_loop.body,
    List.drop_zero, heq] using
    metadata.copy_value_types_loop.spec declared out 0#usize (by simp) (by simpa [heq] using hsize)

/-- The loop of `metadata.push_locals` appends the remaining `count - i` copies of `ty`. -/
@[step]
theorem metadata.push_locals_loop.spec (out : alloc.vec.Vec wasm_types.ValueType)
    (count : U32) (ty : wasm_types.ValueType) (i : U32)
    (hi : i.val ≤ count.val)
    (hsize : out.val.length + (count.val - i.val) ≤ Usize.max) :
    metadata.push_locals_loop out count ty i ⦃ result =>
      result.val = out.val ++ List.replicate (count.val - i.val) ty ⦄ := by
  unfold metadata.push_locals_loop
  apply loop.spec_decr_nat (fun p => count.val - p.2.val)
    (fun p => p.2.val ≤ count.val ∧
      p.1.val ++ List.replicate (count.val - p.2.val) ty =
        out.val ++ List.replicate (count.val - i.val) ty ∧
      p.1.val.length + (count.val - p.2.val) ≤ Usize.max)
  · rintro ⟨v, j⟩ ⟨hj, hv, hb⟩
    dsimp only at hj hv hb
    unfold metadata.push_locals_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : j.val = count.val := by scalar_tac
      simp [heq] at hv
      simp [hv]
    · rename_i hmore
      have hlt : j.val < count.val := by scalar_tac
      have hcapacity : v.val.length < Usize.max := by omega
      step
      step
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals try scalar_tac
      rw [out1_post, i1_post, ← hv]
      have hdiff : count.val - j.val = count.val - (j.val + 1) + 1 := by omega
      rw [hdiff, List.replicate_succ]
      simp [List.append_assoc]
  · exact ⟨hi, rfl, hsize⟩

/-- `metadata.push_locals` appends `count` copies of `ty`. -/
@[step]
theorem metadata.push_locals.spec (out : alloc.vec.Vec wasm_types.ValueType)
    (count : U32) (ty : wasm_types.ValueType)
    (hsize : out.val.length + count.val ≤ Usize.max) :
    metadata.push_locals out count ty ⦃ result =>
      result.val = out.val ++ List.replicate count.val ty ⦄ := by
  simpa [metadata.push_locals] using
    metadata.push_locals_loop.spec out count ty 0#u32 (by simp) (by simpa using hsize)

namespace ModuleLocals

/-- The expansion of grouped local declarations into one type per local. -/
def declared (groups : List (U32 × wasm_types.ValueType)) : List wasm_types.ValueType :=
  groups.flatMap (fun (count, ty) => List.replicate count.val ty)

theorem at_snoc {data start pos next groups group}
    (hp : ModuleBinary.At (ModuleBinary.Rep ModuleBinary.LocalEncoding) data start groups pos)
    (hg : ModuleBinary.At ModuleBinary.LocalEncoding data pos group next) :
    ModuleBinary.At (ModuleBinary.Rep ModuleBinary.LocalEncoding) data start (groups ++ [group]) next := by
  obtain ⟨bs, hb, hs⟩ := hp
  obtain ⟨cs, hc, ht⟩ := hg
  exact ⟨bs ++ cs, hb.snoc hc, hs.append ht⟩

theorem local_at {data start pos next count ty}
    (hc : Leb128.Decoded data start count pos)
    (ht : ModuleBinary.At ModuleBinary.ValueTypeEncoding data pos ty next) :
    ModuleBinary.At ModuleBinary.LocalEncoding data start (count, ty) next := by
  obtain ⟨cs, hs, hl, hb, he⟩ := hc
  obtain ⟨ts, rfl, ht⟩ := ht
  exact ⟨cs ++ [ModuleBinary.valueByte ty], ⟨cs, he, rfl⟩, (⟨hs, hl, hb⟩ : Wasm1.BytesAt data start cs pos).append ht⟩

end ModuleLocals

/-- The loop of `metadata.decode_locals` decodes the remaining `groups - i` local groups, extends the
output by their expansion, and keeps it within `limits.MAX_LOCALS`. -/
@[step]
theorem metadata.decode_locals_loop.spec (data : Slice U8) (groups : U32)
    (out : alloc.vec.Vec wasm_types.ValueType) (q : Usize) (i : U32)
    (hi : i.val ≤ groups.val) (hq : q.val ≤ data.length)
    (hsize : out.val.length ≤ limits.MAX_LOCALS.val) :
    metadata.decode_locals_loop data groups out q i ⦃ r => match r with
      | .Ok (locals, next) => ∃ decoded,
          decoded.length = groups.val - i.val ∧
          ModuleBinary.At (ModuleBinary.Rep ModuleBinary.LocalEncoding) data q decoded next ∧
          locals.val = out.val ++ ModuleLocals.declared decoded ∧
          locals.val.length ≤ limits.MAX_LOCALS.val
      | .Err _ => True ⦄ := by
  unfold metadata.decode_locals_loop
  apply loop.spec_decr_nat (fun s => groups.val - s.2.2.val)
    (fun s => i.val ≤ s.2.2.val ∧ s.2.2.val ≤ groups.val ∧
      ∃ decoded, decoded.length = s.2.2.val - i.val ∧
        ModuleBinary.At (ModuleBinary.Rep ModuleBinary.LocalEncoding) data q decoded s.2.1 ∧
        s.1.val = out.val ++ ModuleLocals.declared decoded ∧
        s.1.val.length ≤ limits.MAX_LOCALS.val)
  · rintro ⟨v, p, j⟩ ⟨hij, hj, decoded, hlen, hbytes, hvals, hcap⟩
    dsimp only at hij hj hlen hbytes hvals hcap
    unfold metadata.decode_locals_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : j.val = groups.val := by scalar_tac
      simp only [WP.spec_ok]
      exact ⟨decoded, by omega, hbytes, hvals, hcap⟩
    · rename_i hmore
      have hlt : j.val < groups.val := by scalar_tac
      obtain ⟨r, hr, hrpost⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data p)
      rw [hr]
      cases r with
      | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from]
      | Ok pair =>
          obtain ⟨count, p1⟩ := pair
          obtain ⟨r, ht, htpost⟩ := WP.spec_imp_exists (metadata.decode_value_type.spec data p1)
          simp [core.result.Result.Insts.CoreOpsTry.branch]
          rw [ht]
          cases r with
          | Err e =>
              simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok pair =>
              obtain ⟨ty, p2⟩ := pair
              have hlocal := ModuleLocals.local_at hrpost htpost
              simp only [bind_ok]
              step
              step
              split
              · simp
              · rename_i hroom
                have hcapacity : v.val.length + count.val ≤ Usize.max := by
                  have : limits.MAX_LOCALS.val < Usize.max := by
                    simp only [limits.MAX_LOCALS]
                    scalar_tac
                  scalar_tac
                step
                step
                refine ⟨?_, ?_, ⟨decoded ++ [(count, ty)], ?_, ?_, ?_, ?_⟩, ?_⟩
                · scalar_tac
                · scalar_tac
                · simp only [List.length_append, List.length_singleton]
                  scalar_tac
                · exact ModuleLocals.at_snoc hbytes hlocal
                · rw [out1_post, hvals]
                  simp [ModuleLocals.declared, List.flatMap_append, List.append_assoc]
                · simp only [out1_post, List.length_append, List.length_replicate]
                  scalar_tac
                · scalar_tac
  · refine ⟨le_refl _, hi, [], by simp, ?_, by simp [ModuleLocals.declared], hsize⟩
    exact ⟨[], .nil, Wasm1.BytesAt.nil data q hq⟩

/-- `metadata.decode_locals` terminates, and on success returns the expansion of independently
encoded local groups within `limits.MAX_LOCALS`. -/
@[step]
theorem metadata.decode_locals.spec (data : Slice U8) (pos : Usize) :
    metadata.decode_locals data pos ⦃ r => match r with
      | .Ok (locals, next) => ∃ groups,
          ModuleBinary.At (ModuleBinary.VecEncoding ModuleBinary.LocalEncoding) data pos groups next ∧
          locals.val = ModuleLocals.declared groups ∧
          locals.val.length ≤ limits.MAX_LOCALS.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e =>
      simp [metadata.decode_locals, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
      obtain ⟨groups, start⟩ := pair
      have hs := hp.span
      rw [metadata.decode_locals, hr]
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      apply WP.spec_mono (metadata.decode_locals_loop.spec data groups (alloc.vec.Vec.new _) start 0#u32
        (by simp) hs.2.2 (by simp))
      rintro r h
      cases r with
      | Err e => trivial
      | Ok pair =>
          obtain ⟨locals, next⟩ := pair
          obtain ⟨decoded, hn, hb, hv, hc⟩ := h
          refine ⟨decoded, ?_, by simpa [alloc.vec.Vec.new] using hv, hc⟩
          obtain ⟨count, hstart, hlength, hbound, he⟩ := hp
          obtain ⟨bytes, he', hs'⟩ := hb
          refine ⟨count ++ bytes, ⟨count, bytes, ?_, he', rfl⟩, ?_⟩
          · simpa using (hn ▸ he)
          · exact (⟨hstart, hlength, hbound⟩ : Wasm1.BytesAt data pos count start).append hs'

end Itasca

end

/-! ## Encoding -/

section

/-!
# Code entry encodings from byte provenance

Conversions between the streaming byte provenance used by the extracted code-entry reader
(`Wasm1.Consumed`, `Wasm1.BytesAt`) and the independent module grammar
(`At`, `Rep`), and `slice_bytes` for the body slice a parser returns.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- The streaming token provenance of a body is an `At (Rep Wasm1.TokenEncoding)` of the module
grammar. -/
theorem consumed_rep {data start tokens next}
    (h : Wasm1.Consumed data start tokens next) :
    At (Rep Wasm1.TokenEncoding) data start tokens next := by
  induction h with
  | nil hb => exact ⟨[], .nil, Wasm1.BytesAt.nil _ _ hb⟩
  | snoc hprev ht ih =>
    obtain ⟨bs, he, hs⟩ := ih
    obtain ⟨cs, hc, hp⟩ := ht
    exact ⟨bs ++ cs, he.snoc hc, hs.append hp⟩

/-- A slice taken from `first` to `last` holds exactly the parent buffer's bytes in that
interval. -/
theorem slice_bytes {data : Slice U8} {first last : Usize} {body : Slice U8}
    (hfirst : first.val ≤ last.val) (hlast : last.val ≤ data.length)
    (hbody : body.val = data.val.slice first.val last.val) :
    Wasm1.BytesAt data first body.val last := by
  refine ⟨?_, ?_, hlast⟩
  · rw [hbody, List.slice]
    have he : first.val + (last.val - first.val) = last.val := by omega
    simpa only [List.drop_drop, he] using
      (List.take_append_drop (last.val - first.val) (data.val.drop first.val)).symm
  · rw [hbody, List.slice_length]
    simp only [Slice.length] at hlast
    omega

/-- A token repetition with matching bytes gives streaming provenance. -/
theorem rep_consumed {data start next tokens bytes}
    (he : Rep Wasm1.TokenEncoding tokens bytes) (hs : Wasm1.BytesAt data start bytes next) :
    Wasm1.Consumed data start tokens next := by
  induction he generalizing start with
  | nil =>
    have hn := hs.empty
    subst next
    exact .nil _ hs.bound
  | cons ht hrest ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hs.split
    exact Wasm1.Consumed.cons_iff.mpr ⟨middle, ⟨_, ht, hfirst⟩, ih hrest⟩

end Itasca.ModuleBinary

end
