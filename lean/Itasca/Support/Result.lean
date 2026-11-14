import Itasca.Generated.FunsValidator
import «wasm2.0»
import Aeneas

/-!
Sections, each formerly its own module: TypeTranslation, EnvTranslation, ControlTranslation, BodyState, Result.
-/

/-! ## TypeTranslation -/

section

/-!
# Type translation

Translates the Rust value, reference, mutability and global types into their SpecTec counterparts
(`Translate.valueType`, `referenceType`, `mutability`, `globalType`), with injectivity and
equality-agreement lemmas.
-/

namespace Itasca.Translate

/-- The SpecTec value type of a Rust value type. -/
def valueType : wasm_types.ValueType → valtype
  | .I32 => .I32
  | .I64 => .I64
  | .F32 => .F32
  | .F64 => .F64
  | .V128 => .V128
  | .FuncRef => .FUNCREF
  | .ExternRef => .EXTERNREF

/-- The SpecTec reference type of a Rust element type. -/
def referenceType : wasm_types.ElemType → reftype
  | .FuncRef => .FUNCREF
  | .ExternRef => .EXTERNREF

/-- The SpecTec mutability of a Rust mutability. -/
def mutability : wasm_types.Mut → «mut»
  | .Const => none
  | .Var => some .MUT

/-- The SpecTec global type of a Rust global type. -/
def globalType (g : wasm_types.GlobalType) : globaltype :=
  .mk_globaltype (mutability g.mutability) (valueType g.valtype)

theorem valueType_injective : Function.Injective valueType := by
  intro a b h
  cases a <;> cases b <;> simp_all [valueType]

theorem mutability_injective : Function.Injective mutability := by
  intro a b h
  cases a <;> cases b <;> simp_all [mutability]

/-- The extracted equality operation agrees with equality in the specification. -/
theorem valueType_eq (a b : wasm_types.ValueType) :
    wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq a b =
      Aeneas.Std.Result.ok (decide (valueType a = valueType b)) := by
  cases a <;> cases b <;> rfl

/-- The translation of every Rust global type, mutable or not, satisfies `Globaltype_ok`. -/
theorem globalType_valid (g : wasm_types.GlobalType) : Globaltype_ok (globalType g) :=
  .mk_Globaltype_ok _ _

end Itasca.Translate

end

/-! ## EnvTranslation -/

section

/-!
# Environment translation

Translates the extracted `metadata.Env` and `code.Context` into a SpecTec `context`
(`EnvTranslation.context`). `Matches` states that a context agrees with this translation in
every field except the labels, and its lemmas turn bounds and lookups in `metadata.Env` into the
premises of the generated `Instr_ok` rules for `local.*`, `global.*`, `call`, `call_indirect` and
`memory.size`/`memory.grow`.
-/

open Aeneas Aeneas.Std

namespace Itasca.EnvTranslation

/-- The SpecTec function type of a Rust function type. -/
def funcType (ft : wasm_types.FuncType) : functype :=
  .mk_functype (.mk_list (ft.params.val.map Translate.valueType))
    (.mk_list (ft.results.val.map Translate.valueType))

/-- The SpecTec limits of Rust limits. -/
def limitsType (lim : wasm_types.Limits) : limits :=
  .mk_limits (.mk_uN lim.min.val) (lim.max.map fun x => .mk_uN x.val)

/-- The SpecTec table type of a Rust table type. -/
def tableType (tt : wasm_types.TableType) : tabletype :=
  .mk_tabletype (limitsType tt.limits) (Translate.referenceType tt.elem)

/-- The SpecTec memory type of a Rust memory type. -/
def memType (mt : wasm_types.MemType) : memtype := .PAGE (limitsType mt.limits)

/-- The element segment types of `env`. -/
def elementTypes (env : metadata.Env) : List elemtype :=
  env.elements.val.map (fun entry => Translate.referenceType entry.elem)

/-- The data segment types of `env`, one `OK` per declared data segment. -/
def dataTypes (env : metadata.Env) : List datatype :=
  List.replicate ((env.data_count.map (fun count => count.val)).getD 0) .OK

/-- The SpecTec context for a function body, with no labels. Function types come from the
environment's resolved function-type cache; its coherence with the module's type indices is a
separate module invariant. -/
def context (env : metadata.Env) (ctx : code.Context) : _root_.context :=
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

/-- Every `u32` index is a well-formed 32-bit `uN`. -/
theorem index_wf (x : U32) : wf_uN 32 (.mk_uN x.val) := by
  apply wf_uN.uN_case_0
  have h := x.hmax
  norm_num at h ⊢
  omega

theorem limitsType_wf (lim : wasm_types.Limits) : wf_limits (limitsType lim) := by
  constructor
  · exact index_wf _
  · cases h : lim.max with
    | none => simp [Forall]
    | some x => simpa [Forall] using index_wf x

theorem tableType_wf (tt : wasm_types.TableType) : wf_tabletype (tableType tt) :=
  .tabletype_case_0 _ _ (limitsType_wf _)

theorem memType_wf (mt : wasm_types.MemType) : wf_memtype (memType mt) :=
  .memtype_case_0 _ (limitsType_wf _)

/-- Syntactic well-formedness needs no module validity assumptions. -/
theorem context_wf (env : metadata.Env) (ctx : code.Context) :
    wf_context (context env ctx) := by
  constructor
  · simp only [Forall, List.mem_map]
    rintro _ ⟨tt, _, rfl⟩
    exact tableType_wf tt
  · simp only [Forall, List.mem_map]
    rintro _ ⟨mt, _, rfl⟩
    exact memType_wf mt

/-- A context `C` agrees with `context env ctx` in every field except the labels, which change as
structured control adds and removes them. -/
structure Matches (env : metadata.Env) (ctx : code.Context) (C : _root_.context) : Prop where
  types : C.TYPES = env.types.val.map funcType
  funcs : C.FUNCS = env.func_types.val.map funcType
  globals : C.GLOBALS = env.global_types.val.map Translate.globalType
  tables : C.TABLES = env.table_types.val.map tableType
  mems : C.MEMS = env.mem_types.val.map memType
  elems : C.ELEMS = elementTypes env
  datas : C.DATAS = dataTypes env
  locals : C.LOCALS = ctx.locals.val.map Translate.valueType
  ret : C.RETURN = some (.mk_list (ctx.results.val.map Translate.valueType))

/-- The root context matches itself. -/
theorem Matches.root (env : metadata.Env) (ctx : code.Context) :
    Matches env ctx (context env ctx) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Contexts that match a translated environment are well-formed. -/
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
    (idx : U32) (t : wasm_types.ValueType) (hi : idx.val < ctx.locals.val.length)
    (ht : ctx.locals.val[idx.val] = t) :
    idx.val < C.LOCALS.length ∧ C.LOCALS[idx.val]! = Translate.valueType t := by
  rw [h.locals]
  constructor
  · simpa using hi
  · rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map, ht]

theorem Matches.global {env ctx C} (h : Matches env ctx C)
    (idx : U32) (gt : wasm_types.GlobalType) (hi : idx.val < env.global_types.val.length)
    (ht : env.global_types.val[idx.val] = gt) :
    idx.val < C.GLOBALS.length ∧ C.GLOBALS[idx.val]! = Translate.globalType gt := by
  rw [h.globals]
  constructor
  · simpa using hi
  · rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map, ht]

theorem Matches.local_get {env ctx C} (h : Matches env ctx C)
    (idx : U32) (t : wasm_types.ValueType) (hi : idx.val < ctx.locals.val.length)
    (ht : ctx.locals.val[idx.val] = t) :
    Instr_ok C (.LOCAL_GET (.mk_uN idx.val))
      (.mk_functype (.mk_list []) (.mk_list [Translate.valueType t])) := by
  obtain ⟨hb, he⟩ := h.local idx t hi ht
  exact .local_get C _ _ hb he h.wf (.instr_case_43 _ (index_wf idx))

theorem Matches.local_set {env ctx C} (h : Matches env ctx C)
    (idx : U32) (t : wasm_types.ValueType) (hi : idx.val < ctx.locals.val.length)
    (ht : ctx.locals.val[idx.val] = t) :
    Instr_ok C (.LOCAL_SET (.mk_uN idx.val))
      (.mk_functype (.mk_list [Translate.valueType t]) (.mk_list [])) := by
  obtain ⟨hb, he⟩ := h.local idx t hi ht
  exact .local_set C _ _ hb he h.wf (.instr_case_44 _ (index_wf idx))

theorem Matches.local_tee {env ctx C} (h : Matches env ctx C)
    (idx : U32) (t : wasm_types.ValueType) (hi : idx.val < ctx.locals.val.length)
    (ht : ctx.locals.val[idx.val] = t) :
    Instr_ok C (.LOCAL_TEE (.mk_uN idx.val))
      (.mk_functype (.mk_list [Translate.valueType t]) (.mk_list [Translate.valueType t])) := by
  obtain ⟨hb, he⟩ := h.local idx t hi ht
  exact .local_tee C _ _ hb he h.wf (.instr_case_45 _ (index_wf idx))

theorem Matches.global_get {env ctx C} (h : Matches env ctx C)
    (idx : U32) (gt : wasm_types.GlobalType) (hi : idx.val < env.global_types.val.length)
    (ht : env.global_types.val[idx.val] = gt) :
    Instr_ok C (.GLOBAL_GET (.mk_uN idx.val))
      (.mk_functype (.mk_list []) (.mk_list [Translate.valueType gt.valtype])) := by
  obtain ⟨hb, he⟩ := h.global idx gt hi ht
  exact .global_get C _ _ _ hb he h.wf (.instr_case_46 _ (index_wf idx))

theorem Matches.global_set {env ctx C} (h : Matches env ctx C)
    (idx : U32) (gt : wasm_types.GlobalType) (hi : idx.val < env.global_types.val.length)
    (ht : env.global_types.val[idx.val] = gt) (hm : gt.mutability = .Var) :
    Instr_ok C (.GLOBAL_SET (.mk_uN idx.val))
      (.mk_functype (.mk_list [Translate.valueType gt.valtype]) (.mk_list [])) := by
  obtain ⟨hb, he⟩ := h.global idx gt hi ht
  apply Instr_ok.global_set C _ _ hb _ h.wf (.instr_case_47 _ (index_wf idx))
  simpa [Translate.globalType, hm, Translate.mutability, proj_uN_0] using he

theorem Matches.call {env ctx C} (h : Matches env ctx C)
    (idx : U32) (ft : wasm_types.FuncType) (hi : idx.val < env.func_types.val.length)
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
    (idx tableIdx : U32) (ft : wasm_types.FuncType) (hi : idx.val < env.types.val.length)
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

open Aeneas Aeneas.Std

namespace Itasca.EnvTranslation

private theorem mapped_lookup {α β : Type} [Inhabited β]
    (xs : List α) (f : α → β) (i : Nat) (t : β)
    (hi : i < (xs.map f).length) (ht : (xs.map f)[i]! = t) :
    ∃ x, ∃ hx : i < xs.length, xs[i] = x ∧ f x = t := by
  have hx : i < xs.length := by simpa using hi
  exact ⟨xs[i], hx, rfl, by simpa [getElem!_pos, hx] using ht⟩

/-- A bounded lookup in the translated context recovers the concrete local. -/
theorem Matches.local_lookup {env ctx C} (h : Matches env ctx C)
    (idx : U32) (t : valtype) (hi : idx.val < C.LOCALS.length) (ht : C.LOCALS[idx.val]! = t) :
    ∃ v, ∃ hv : idx.val < ctx.locals.val.length,
      ctx.locals.val[idx.val] = v ∧ Translate.valueType v = t := by
  exact mapped_lookup _ _ _ _ (by simpa [h.locals] using hi) (by simpa [h.locals] using ht)

theorem Matches.global_lookup {env ctx C} (h : Matches env ctx C)
    (idx : U32) (t : globaltype) (hi : idx.val < C.GLOBALS.length) (ht : C.GLOBALS[idx.val]! = t) :
    ∃ gt, ∃ hv : idx.val < env.global_types.val.length,
      env.global_types.val[idx.val] = gt ∧ Translate.globalType gt = t := by
  exact mapped_lookup _ _ _ _ (by simpa [h.globals] using hi) (by simpa [h.globals] using ht)

theorem Matches.func_lookup {env ctx C} (h : Matches env ctx C)
    (idx : U32) (t : functype) (hi : idx.val < C.FUNCS.length) (ht : C.FUNCS[idx.val]! = t) :
    ∃ ft, ∃ hv : idx.val < env.func_types.val.length,
      env.func_types.val[idx.val] = ft ∧ funcType ft = t := by
  exact mapped_lookup _ _ _ _ (by simpa [h.funcs] using hi) (by simpa [h.funcs] using ht)

theorem Matches.type_lookup {env ctx C} (h : Matches env ctx C)
    (idx : U32) (t : functype) (hi : idx.val < C.TYPES.length) (ht : C.TYPES[idx.val]! = t) :
    ∃ ft, ∃ hv : idx.val < env.types.val.length,
      env.types.val[idx.val] = ft ∧ funcType ft = t := by
  exact mapped_lookup _ _ _ _ (by simpa [h.types] using hi) (by simpa [h.types] using ht)

theorem Matches.table_lookup {env ctx C} (h : Matches env ctx C)
    (idx : U32) (t : tabletype) (hi : idx.val < C.TABLES.length) (ht : C.TABLES[idx.val]! = t) :
    ∃ tt, ∃ hv : idx.val < env.table_types.val.length,
      env.table_types.val[idx.val] = tt ∧ tableType tt = t := by
  exact mapped_lookup _ _ _ _ (by simpa [h.tables] using hi) (by simpa [h.tables] using ht)

/-- A `funcref` table in the context is a `FuncRef` table in the environment. -/
theorem Matches.table_funcref {env ctx C} (h : Matches env ctx C)
    (idx : U32) (lim : limits) (hi : idx.val < C.TABLES.length)
    (ht : C.TABLES[idx.val]! = .mk_tabletype lim .FUNCREF) :
    ∃ hv : idx.val < env.table_types.val.length, env.table_types.val[idx.val].elem = .FuncRef := by
  obtain ⟨tt, hv, htt, htype⟩ := h.table_lookup idx _ hi ht
  refine ⟨hv, ?_⟩
  rw [htt]
  cases he : tt.elem <;> simp_all [tableType, Translate.referenceType]

theorem Matches.memory_exists {env ctx C} (h : Matches env ctx C)
    (hi : 0 < C.MEMS.length) : 0 < env.mem_types.val.length := by simpa [h.mems] using hi

end Itasca.EnvTranslation

end

/-! ## ControlTranslation -/

section

/-!
# Block type translation

Translates `signature.BlockType` into SpecTec `blocktype` with a well-formedness proof.
`labelContext` is the context extension entered by structured control, and `Matches.enter` shows
that it preserves the static fields of `EnvTranslation.Matches`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Control

/-- The context that adds one label with result types `ts`, to be prepended to the outer context. -/
def labelContext (ts : List valtype) : context :=
  ⟨[], [], [], [], [], [], [], [], [.mk_list ts], none⟩

@[simp]
theorem labelContext_labels (C : context) (ts : List valtype) :
    (labelContext ts ++ C).LABELS = .mk_list ts :: C.LABELS := rfl

theorem labelContext_wf (ts : List valtype) : wf_context (labelContext ts) := by
  constructor <;> simp [Forall]

theorem enter_context_wf (C : context) (hC : wf_context C) (ts : List valtype) :
    wf_context (labelContext ts ++ C) := by
  cases hC
  constructor <;> assumption

end Itasca.Control

namespace Itasca.EnvTranslation

theorem Matches.enter {env ctx C} (h : Matches env ctx C) (ts : List valtype) :
    Matches env ctx (Control.labelContext ts ++ C) := by
  exact ⟨h.types, h.funcs, h.globals, h.tables, h.mems, h.elems, h.datas, h.locals, h.ret⟩

end Itasca.EnvTranslation

namespace Itasca.Wasm2

/-- The SpecTec block type of a Wasm 2.0 block type, including type-index blocks. -/
def blockType : signature.BlockType → blocktype
  | .Empty => ._RESULT none
  | .Value t => ._RESULT (some (Translate.valueType t))
  | .TypeIndex i => ._IDX (.mk_uN i.val)

theorem blockType_wf (bt : signature.BlockType) : wf_blocktype (blockType bt) := by
  cases bt with
  | Empty => exact .blocktype_case_0 _
  | Value _ => exact .blocktype_case_0 _
  | TypeIndex i => exact .blocktype_case_1 _ (EnvTranslation.index_wf i)

end Itasca.Wasm2

end

/-! ## BodyState -/

section

/-!
# Block signatures of the body state

`code.BodyState.blocks` projects the signature of every control frame out of the single runtime
control stack `st.core.ctrls`, with simp lemmas for its length, emptiness and indexing.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- The block signatures seen by the body proofs: a projection of the runtime control stack.
Rust stores no separate signature vector. -/
def code.BodyState.blocks (st : code.BodyState) : alloc.vec.Vec signature.BlockType :=
  alloc.vec.Vec.from (st.core.ctrls.val.map code.Ctrl.signature) (by simp)

@[simp] theorem code.BodyState.blocks_val (st : code.BodyState) :
    st.blocks.val = st.core.ctrls.val.map code.Ctrl.signature := by
  simp [code.BodyState.blocks]

@[simp] theorem code.BodyState.blocks_length (st : code.BodyState) :
    st.blocks.val.length = st.core.ctrls.val.length := by simp

@[simp] theorem code.BodyState.blocks_len (st : code.BodyState) :
    alloc.vec.Vec.len st.blocks = alloc.vec.Vec.len st.core.ctrls :=
  UScalar.eq_of_val_eq (by simp)

@[simp] theorem code.BodyState.blocks_is_empty (st : code.BodyState) :
    alloc.vec.Vec.is_empty Global st.blocks = alloc.vec.Vec.is_empty Global st.core.ctrls := by
  simp [alloc.vec.Vec.is_empty]

theorem code.BodyState.blocks_index (st : code.BodyState) (i : Usize) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice signature.BlockType) st.blocks i =
      (do let c ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice code.Ctrl) st.core.ctrls i
          .ok c.signature) := by
  simp only [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize,
    alloc.vec.Vec.getElem?_Nat_eq, code.BodyState.blocks_val, List.getElem?_map]
  cases st.core.ctrls.val[i.val]? <;> simp

theorem code.BodyState.blocks_eq_of_ctrls {st st' : code.BodyState}
    (h : st.core.ctrls = st'.core.ctrls) : st.blocks = st'.blocks := by
  apply alloc.vec.Vec.ext
  simp [h]

@[simp] theorem code.BodyState.blocks_eq_iff (st st' : code.BodyState) :
    st.blocks = st'.blocks ↔
      st.core.ctrls.val.map code.Ctrl.signature = st'.core.ctrls.val.map code.Ctrl.signature := by
  rw [alloc.vec.Vec.eq_iff]
  simp

@[simp] theorem code.BodyState.blocks_pos (st : code.BodyState) (pos : Usize) :
    (code.BodyState.mk { st.core with pos }).blocks = st.blocks := rfl

@[simp] theorem code.BodyState.blocks_vals (st : code.BodyState)
    (vals : alloc.vec.Vec code.StackType) :
    (code.BodyState.mk { st.core with vals }).blocks = st.blocks := rfl

end Itasca

namespace Itasca

/-- Cursor arithmetic just past a body of maximal size does not overflow `Usize`. -/
theorem limits.MAX_FUNCTION_BYTES.room : limits.MAX_FUNCTION_BYTES.val + 2 < Usize.max := by
  simp only [limits.MAX_FUNCTION_BYTES]
  scalar_tac

end Itasca

end

/-! ## Result -/

section

/-!
# Result facts

Inversion of a successful monadic bind in the Aeneas `Result` monad.
-/

open Aeneas Aeneas.Std

namespace Itasca.ResultFacts

/-- A returned result satisfies the postcondition of any specification of the same computation. -/
theorem post_of_ok {α : Type} {m : Result α} {P : α → Prop} {r : α}
    (spec : m ⦃ P ⦄) (called : m = .ok r) : P r := by
  obtain ⟨r', run, post⟩ := WP.spec_imp_exists spec
  rw [called, Result.ok.injEq] at run
  exact run ▸ post

/-- A bind returns `.ok` only if both the producer and the continuation return `.ok`. -/
theorem bind_ok_inv {A B : Type} (read : Result A) (next : A → Result B) (b : B)
    (h : (read >>= next) = .ok b) :
    ∃ a, read = .ok a ∧ next a = .ok b := by
  induction read using Result.cases with
  | ret a => exact ⟨a, rfl, by simpa using h⟩
  | vis e k => simp at h
  | div => simp at h

end Itasca.ResultFacts

end
