import Itasca.Body.References.Readers
import Itasca.Body.LoopDispatch
import Itasca.Binary.Body.Encoding
import Itasca.Body.Scalar.Readers

open WebAssembly

/-!
Proofs for Body / References.

This module collects Reader, Step.
Each section documents its contracts and consumers.
-/

/-! ## Reader -/

section

/-!
# Reader

Reference readers resolve operands against the matching source environment. Their contracts retain the decoded index, operand effects and source instruction meaning.
-/

/-! ## Operands -/

section

/-!
# Operand factorization of reference readers

Each extracted `code.read_ref_null`, `code.read_table_get`, `code.read_table_set`,
`code.read_table_grow`, `code.read_table_size`, `code.read_table_fill` and
`code.read_typed_select` equals `Body.metadataOperands` applied to its metadata decoder, which
is the decoder followed by the fixed pop and push of `Simd.readFixed`.
`code.read_ref_is_null.segment` gives the typing of the polymorphic null test.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body

/-- A checked metadata reader followed by a fixed stack effect. The result keeps the decoded
metadata for the instruction's visitor hook. -/
def metadataOperands {A B : Type}
    (decode : Result (core.result.Result A error.OpError × code.OpIterState))
    (pops : A → List wasm_types.ValueType) (output : A → Option wasm_types.ValueType)
    (metadata : A → B) : Result (core.result.Result B error.OpError × code.OpIterState) := do
  let (r, s) ← decode
  match r with
  | .Err e => .ok (.Err e, s)
  | .Ok a =>
    let (r, out) ← Simd.readFixed s (pops a) (output a)
    match r with
    | .Err e => .ok (.Err e, out)
    | .Ok () => .ok (.Ok (metadata a), out)

/-- The explicit select vector has exactly one literal value-type entry. -/
def selectType (st : code.OpIterState) (data : Slice U8) :
    Result (core.result.Result wasm_types.ValueType error.OpError × code.OpIterState) := do
  let (r, s) ← code.take_index st data
  match r with
  | .Err e => .ok (.Err e, s)
  | .Ok count =>
      if count = 1#u32 then code.take_value_type s data
      else .ok (.Err .TypeMismatch, s)

theorem selectType.spec (st : code.OpIterState) (data : Slice U8) :
    selectType st data ⦃ r => r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      ∀ ty, r.1 = .Ok ty → ∃ count,
        Body.Scalar.BytesAt data st.pos (count ++ [Itasca.Binary.valueByte ty]) r.2.pos ∧ Binary.Leb128.Encoding count 1 ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hd⟩ := WP.spec_imp_exists (code.take_index.spec st data)
  dsimp only at hv hc hd
  cases r with
  | Err e => simp [selectType, hr, hv, hc]
  | Ok count =>
    by_cases he : count = 1#u32
    · subst count
      simp only [selectType, hr, bind_ok]
      apply WP.spec_mono (code.take_value_type.spec s data)
      rintro ⟨res, out⟩ ⟨hvo, hco, htag⟩
      refine ⟨hvo.trans hv, hco.trans hc, ?_⟩
      intro ty hok
      obtain ⟨bytes, hb, hl, hn, he⟩ := hd
      exact ⟨bytes, (show Body.Scalar.BytesAt data st.pos bytes s.pos from ⟨hb, hl, hn⟩).append (htag ty hok), he⟩
    · simp [selectType, hr, he, hv, hc]

theorem metadataOperands.empty {A : Type}
    (decode : Result (core.result.Result A error.OpError × code.OpIterState)) :
    metadataOperands decode (fun _ => []) (fun _ => none) id = decode := by
  calc
    metadataOperands decode (fun _ => []) (fun _ => none) id = decode >>= Result.ok := by
      unfold metadataOperands
      congr 1
      funext pair
      obtain ⟨res, s⟩ := pair
      cases res <;> simp [Simd.readFixed]
    _ = decode := Std.bind_pure decode

end Itasca.Body

namespace Itasca

/-- The extracted handler has exactly its metadata-dependent fixed operand effect. -/
theorem code.read_ref_null.fixed (st : code.OpIterState) (data : Slice U8) :
    code.read_ref_null st data = Body.metadataOperands (code.take_reference_type st data)
      (fun _ => []) (fun rt => some (Module.Constants.referenceValueType rt)) id := by
  simp only [code.read_ref_null, Body.metadataOperands]
  congr 1
  funext pair
  obtain ⟨r, state⟩ := pair
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok a =>
    try (cases (show U32 × wasm_types.ValueType from a))
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      wasm_types.ElemType.value_type.eq, Body.Simd.readFixed, Std.bind_assoc, Std.uncurry]
    try dsimp only
    repeat' rfl

/-- The extracted handler has exactly its metadata-dependent fixed operand effect. -/
theorem code.read_table_get.fixed (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) :
    code.read_table_get st data env = Body.metadataOperands (code.take_table st data env)
      (fun _ => [.I32]) (fun a => some a.2) Prod.fst := by
  simp only [code.read_table_get, Body.metadataOperands]
  congr 1
  funext pair
  obtain ⟨r, state⟩ := pair
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok a =>
    try (cases (show U32 × wasm_types.ValueType from a))
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      Body.Simd.readFixed, Std.bind_assoc, Std.uncurry]
    try dsimp only
    repeat' first
      | rfl
      | (congr 1
         funext pair
         obtain ⟨res, state⟩ := pair
         cases res <;> simp [
           core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
           Std.bind_assoc])

/-- The extracted handler has exactly its metadata-dependent fixed operand effect. -/
theorem code.read_table_set.fixed (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) :
    code.read_table_set st data env = Body.metadataOperands (code.take_table st data env)
      (fun a => [a.2, .I32]) (fun _ => none) Prod.fst := by
  simp only [code.read_table_set, Body.metadataOperands]
  congr 1
  funext pair
  obtain ⟨r, state⟩ := pair
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok a =>
    try (cases (show U32 × wasm_types.ValueType from a))
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      Body.Simd.readFixed, Std.bind_assoc, Std.uncurry]
    try dsimp only
    repeat' first
      | rfl
      | (congr 1
         funext pair
         obtain ⟨res, state⟩ := pair
         cases res <;> simp [
           core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
           Std.bind_assoc])

/-- The extracted handler has exactly its metadata-dependent fixed operand effect. -/
theorem code.read_table_grow.fixed (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) :
    code.read_table_grow st data env = Body.metadataOperands (code.take_table st data env)
      (fun a => [.I32, a.2]) (fun _ => some .I32) Prod.fst := by
  simp only [code.read_table_grow, Body.metadataOperands]
  congr 1
  funext pair
  obtain ⟨r, state⟩ := pair
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok a =>
    try (cases (show U32 × wasm_types.ValueType from a))
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      Body.Simd.readFixed, Std.bind_assoc, Std.uncurry]
    try dsimp only
    repeat' first
      | rfl
      | (congr 1
         funext pair
         obtain ⟨res, state⟩ := pair
         cases res <;> simp [
           core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
           Std.bind_assoc])

/-- The extracted handler has exactly its metadata-dependent fixed operand effect. -/
theorem code.read_table_size.fixed (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) :
    code.read_table_size st data env = Body.metadataOperands (code.take_table st data env)
      (fun _ => []) (fun _ => some .I32) Prod.fst := by
  simp only [code.read_table_size, Body.metadataOperands]
  congr 1
  funext pair
  obtain ⟨r, state⟩ := pair
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok a =>
    try (cases (show U32 × wasm_types.ValueType from a))
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      Body.Simd.readFixed, Std.bind_assoc, Std.uncurry]
    try dsimp only

/-- The extracted handler has exactly its metadata-dependent fixed operand effect. -/
theorem code.read_table_fill.fixed (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) :
    code.read_table_fill st data env = Body.metadataOperands (code.take_table st data env)
      (fun a => [.I32, a.2, .I32]) (fun _ => none) Prod.fst := by
  simp only [code.read_table_fill, Body.metadataOperands]
  congr 1
  funext pair
  obtain ⟨r, state⟩ := pair
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok a =>
    try (cases (show U32 × wasm_types.ValueType from a))
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      Body.Simd.readFixed, Std.bind_assoc, Std.uncurry]
    try dsimp only
    repeat' first
      | rfl
      | (congr 1
         funext pair
         obtain ⟨res, state⟩ := pair
         cases res <;> simp [
           core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
           Std.bind_assoc])

theorem code.read_typed_select.fixed (st : code.OpIterState) (data : Slice U8) :
    code.read_typed_select st data = Body.metadataOperands (Body.selectType st data)
      (fun ty => [.I32, ty, ty]) some id := by
  obtain ⟨⟨r, state⟩, hr, _⟩ := WP.spec_imp_exists (code.take_index.spec st data)
  cases r with
  | Err e => simp [code.read_typed_select, Body.metadataOperands, Body.selectType, hr,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok count =>
    by_cases hc : count = 1#u32
    · subst count
      simp [code.read_typed_select, Body.metadataOperands, Body.selectType, hr,
        core.result.Result.Insts.CoreOpsTry.branch]
      congr 1
      funext pair
      obtain ⟨r, state⟩ := pair
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok ty =>
        simp only [bind_ok, Body.Simd.readFixed, Std.bind_assoc, Std.uncurry]
        repeat' first
          | rfl
          | (congr 1
             funext pair
             obtain ⟨res, state⟩ := pair
             cases res <;> simp [
               core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
               Std.bind_assoc])
    · have hcv : count.val ≠ 1 := fun he => hc (UScalar.eq_of_val_eq he)
      simp [code.read_typed_select, Body.metadataOperands, Body.selectType, hr, hc, hcv,
        core.result.Result.Insts.CoreOpsTry.branch]

/-- A successful null test consumes a reference (or the polymorphic bottom)
and produces i32. The chosen reference type remains explicit in the typing. -/
theorem code.read_ref_is_null.segment (st : code.OpIterState)
    (outer segment : List code.StackType)
    (hv : st.vals.val = outer ++ segment) (hb : (Body.Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max) :
    code.read_ref_is_null st ⦃ r => r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ after, r.2.vals.val = outer ++ after ∧
        (r.1 = .Ok () → ∃ rt, Body.Simd.FixedEffect (Body.Control.polymorphic st) segment
          [Module.Constants.referenceValueType rt] (some .I32) after) ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hc, hp, popped, hpv, hpop⟩ := WP.spec_imp_exists
    (code.pop_stack_type.segment st outer segment hv hb)
  dsimp only at hc hp hpv hpop
  have hlen := hpop.length
  cases r with
  | Err e =>
    simpa [code.read_ref_is_null, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using
      (show s.ctrls = st.ctrls ∧ s.pos = st.pos ∧ ∃ after, s.vals.val = outer ++ after from
        ⟨hc, hp, popped, hpv⟩)
  | Ok t =>
    change Body.Stack.Semantics.Popped (Body.Control.polymorphic st) segment t popped at hpop
    have hcap : s.vals.val.length < Usize.max := by
      simp only [hv, hpv, List.length_append] at *
      omega
    have finish (rt : wasm_types.ElemType)
        (ht : Body.Stack.Accepts t (valtype_reftype (Translation.referenceType rt)))
        (hrun : code.read_ref_is_null st = do
          let out ← code.push_val s (.Val .I32)
          .ok (.Ok (), out)) :
        code.read_ref_is_null st ⦃ r => r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
          ∃ after, r.2.vals.val = outer ++ after ∧
            (r.1 = .Ok () → ∃ rt, Body.Simd.FixedEffect (Body.Control.polymorphic st) segment
              [Module.Constants.referenceValueType rt] (some .I32) after) ⦄ := by
      obtain ⟨out, ho, hov, hoc, hop⟩ := WP.spec_imp_exists (code.push_val.spec s (.Val .I32) hcap)
      rw [hrun, ho, bind_ok, WP.spec_ok]
      refine ⟨hoc.trans hc, hop.trans hp, popped ++ [.Val .I32],
        by simpa [hpv, List.append_assoc] using hov, ?_⟩
      intro _
      refine ⟨rt, ?_⟩
      intro ts hts
      obtain ⟨front, hfront, rfl⟩ := (Body.Stack.realizes_append_concrete _ _ [.I32] ts).mp hts
      refine ⟨front, rfl, ?_⟩
      have hh := hpop.realizes front (valtype_reftype (Translation.referenceType rt)) ht hfront
      cases rt <;> simpa [Body.Simd.inputTypes, Module.Constants.referenceValueType, Translation.referenceType,
        Translation.valueType, valtype_reftype] using hh
    cases t with
    | Bot =>
      apply finish .FuncRef trivial
      simp [code.read_ref_is_null, hr, core.result.Result.Insts.CoreOpsTry.branch]
    | Val ty =>
      cases ty
      all_goals first
        | (apply finish .FuncRef rfl; simp [code.read_ref_is_null, hr, core.result.Result.Insts.CoreOpsTry.branch])
        | (apply finish .ExternRef rfl; simp [code.read_ref_is_null, hr, core.result.Result.Insts.CoreOpsTry.branch])
        | (simpa [code.read_ref_is_null, hr, core.result.Result.Insts.CoreOpsTry.branch] using
          (show s.ctrls = st.ctrls ∧ s.pos = st.pos ∧ ∃ after, s.vals.val = outer ++ after from
            ⟨hc, hp, popped, hpv⟩))

end Itasca

end

/-! ## EnvMatches -/

section

/-!
# Environment matching for reference and bulk instructions

Lemmas about `Translation.Environment.Matches`, the agreement between a runtime `metadata.CodeMetadata` and a
SpecTec context. Each `Matches.table_get`, `Matches.table_copy`, `Matches.memory_init`, ... turns
bounds on the runtime environment into the corresponding `Instr_ok` judgment for the reference,
table and bulk-memory instructions.
-/

open Aeneas Aeneas.Std

namespace Itasca.Translation.Environment

/-- A runtime table entry supplies the corresponding generated lookup. -/
theorem Matches.table_entry {env ctx C} (h : Matches env ctx C)
    (idx : U32) (tt : wasm_types.TableType) (hi : idx.val < env.tables.val.length)
    (ht : env.tables.val[idx.val].ty = tt) :
    idx.val < C.TABLES.length ∧ C.TABLES[idx.val]! = tableType tt := by
  rw [h.tables]
  constructor
  · simpa using hi
  · rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map, ht]

theorem Matches.element_entry {env ctx C} (h : Matches env ctx C)
    (idx : U32) (elem : wasm_types.ElemType) (hi : idx.val < env.elem_segment_types.val.length)
    (ht : env.elem_segment_types.val[idx.val] = elem) :
    idx.val < C.ELEMS.length ∧ C.ELEMS[idx.val]! = Translation.referenceType elem := by
  rw [h.elems]
  simp only [elementTypes]
  constructor
  · simpa using hi
  · rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map, ht]

theorem Matches.data_entry {env ctx C} (h : Matches env ctx C)
    (idx count : U32) (hc : env.data_count = some count) (hi : idx.val < count.val) :
    idx.val < C.DATAS.length ∧ C.DATAS[idx.val]! = .OK := by
  rw [h.datas]
  simp only [dataTypes, hc, Option.map_some, Option.getD_some, List.length_replicate]
  exact ⟨hi, trivial⟩

theorem Matches.ref_func {env ctx C} (h : Matches env ctx C)
    (idx : U32) (hi : idx.val < env.funcs.val.length) :
    Instr_ok C (.REF_FUNC (.mk_uN idx.val)) (.mk_functype (.mk_list []) (.mk_list [.FUNCREF])) := by
  apply Instr_ok.ref_func _ _ (descriptorType env.types.val env.funcs.val[idx.val])
  · simpa [h.funcs, proj_uN_0] using hi
  · simp only [h.funcs, proj_uN_0]
    rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map]
  · exact h.wf
  · exact .instr_case_41 _ (index_wf idx)

theorem Matches.table_get {env ctx C} (h : Matches env ctx C)
    (idx : U32) (tt : wasm_types.TableType) (hi : idx.val < env.tables.val.length)
    (ht : env.tables.val[idx.val].ty = tt) :
    Instr_ok C (.TABLE_GET (.mk_uN idx.val))
      (.mk_functype (.mk_list [.I32]) (.mk_list [valtype_reftype (Translation.referenceType tt.elem)])) := by
  obtain ⟨hb, he⟩ := h.table_entry idx tt hi ht
  exact .table_get _ _ _ _ hb he h.wf (.instr_case_48 _ (index_wf idx)) (table_type_wf tt)

theorem Matches.table_set {env ctx C} (h : Matches env ctx C)
    (idx : U32) (tt : wasm_types.TableType) (hi : idx.val < env.tables.val.length)
    (ht : env.tables.val[idx.val].ty = tt) :
    Instr_ok C (.TABLE_SET (.mk_uN idx.val))
      (.mk_functype (.mk_list [.I32, valtype_reftype (Translation.referenceType tt.elem)]) (.mk_list [])) := by
  obtain ⟨hb, he⟩ := h.table_entry idx tt hi ht
  exact .table_set _ _ _ _ hb he h.wf (.instr_case_49 _ (index_wf idx)) (table_type_wf tt)

theorem Matches.table_size {env ctx C} (h : Matches env ctx C)
    (idx : U32) (tt : wasm_types.TableType) (hi : idx.val < env.tables.val.length)
    (ht : env.tables.val[idx.val].ty = tt) :
    Instr_ok C (.TABLE_SIZE (.mk_uN idx.val))
      (.mk_functype (.mk_list []) (.mk_list [.I32])) := by
  obtain ⟨hb, he⟩ := h.table_entry idx tt hi ht
  exact .table_size _ _ _ _ hb he h.wf (.instr_case_50 _ (index_wf idx)) (table_type_wf tt)

theorem Matches.table_grow {env ctx C} (h : Matches env ctx C)
    (idx : U32) (tt : wasm_types.TableType) (hi : idx.val < env.tables.val.length)
    (ht : env.tables.val[idx.val].ty = tt) :
    Instr_ok C (.TABLE_GROW (.mk_uN idx.val))
      (.mk_functype (.mk_list [valtype_reftype (Translation.referenceType tt.elem), .I32]) (.mk_list [.I32])) := by
  obtain ⟨hb, he⟩ := h.table_entry idx tt hi ht
  exact .table_grow _ _ _ _ hb he h.wf (.instr_case_51 _ (index_wf idx)) (table_type_wf tt)

theorem Matches.table_fill {env ctx C} (h : Matches env ctx C)
    (idx : U32) (tt : wasm_types.TableType) (hi : idx.val < env.tables.val.length)
    (ht : env.tables.val[idx.val].ty = tt) :
    Instr_ok C (.TABLE_FILL (.mk_uN idx.val))
      (.mk_functype (.mk_list [.I32, valtype_reftype (Translation.referenceType tt.elem), .I32]) (.mk_list [])) := by
  obtain ⟨hb, he⟩ := h.table_entry idx tt hi ht
  exact .table_fill _ _ _ _ hb he h.wf (.instr_case_52 _ (index_wf idx)) (table_type_wf tt)

theorem Matches.table_copy {env ctx C} (h : Matches env ctx C)
    (destination source : U32) (dst src : wasm_types.TableType)
    (hd : destination.val < env.tables.val.length) (hs : source.val < env.tables.val.length)
    (htd : env.tables.val[destination.val].ty = dst) (hts : env.tables.val[source.val].ty = src)
    (htype : src.elem = dst.elem) :
    Instr_ok C (.TABLE_COPY (.mk_uN destination.val) (.mk_uN source.val))
      (.mk_functype (.mk_list [.I32, .I32, .I32]) (.mk_list [])) := by
  obtain ⟨hdb, hde⟩ := h.table_entry destination dst hd htd
  obtain ⟨hsb, hse⟩ := h.table_entry source src hs hts
  exact .table_copy C _ _ (limitsType dst.limits) (Translation.referenceType dst.elem)
    (limitsType src.limits) hdb hde hsb (by simpa [tableType, htype, proj_uN_0] using hse) h.wf
    (.instr_case_53 _ _ (index_wf destination) (index_wf source)) (table_type_wf dst)
    (by simpa [tableType, htype] using table_type_wf src)

theorem Matches.table_init {env ctx C} (h : Matches env ctx C)
    (table element : U32) (tt : wasm_types.TableType) (elem : wasm_types.ElemType)
    (ht : table.val < env.tables.val.length) (he : element.val < env.elem_segment_types.val.length)
    (htt : env.tables.val[table.val].ty = tt) (hee : env.elem_segment_types.val[element.val] = elem)
    (htype : elem = tt.elem) :
    Instr_ok C (.TABLE_INIT (.mk_uN table.val) (.mk_uN element.val))
      (.mk_functype (.mk_list [.I32, .I32, .I32]) (.mk_list [])) := by
  obtain ⟨htb, hte⟩ := h.table_entry table tt ht htt
  obtain ⟨heb, hee⟩ := h.element_entry element elem he hee
  exact .table_init _ _ _ _ _ htb hte heb (by simpa [htype, proj_uN_0] using hee) h.wf
    (.instr_case_54 _ _ (index_wf table) (index_wf element)) (table_type_wf tt)

theorem Matches.elem_drop {env ctx C} (h : Matches env ctx C)
    (idx : U32) (elem : wasm_types.ElemType) (hi : idx.val < env.elem_segment_types.val.length)
    (ht : env.elem_segment_types.val[idx.val] = elem) :
    Instr_ok C (.ELEM_DROP (.mk_uN idx.val)) (.mk_functype (.mk_list []) (.mk_list [])) := by
  obtain ⟨hb, he⟩ := h.element_entry idx elem hi ht
  exact .elem_drop _ _ _ hb he h.wf (.instr_case_55 _ (index_wf idx))

theorem Matches.memory_copy {env ctx C} (h : Matches env ctx C)
    (hmem : 0 < env.memories.val.length) :
    Instr_ok C .MEMORY_COPY (.mk_functype (.mk_list [.I32, .I32, .I32]) (.mk_list [])) := by
  apply Instr_ok.memory_copy _ (memType env.memories.val[0].ty)
  · simpa [h.mems] using hmem
  · simp only [h.mems]
    rw [getElem!_pos _ _ (by simpa using hmem), List.getElem_map]
  · exact h.wf
  · exact mem_type_wf _
  · exact .instr_case_65

theorem Matches.memory_fill {env ctx C} (h : Matches env ctx C)
    (hmem : 0 < env.memories.val.length) :
    Instr_ok C .MEMORY_FILL (.mk_functype (.mk_list [.I32, .I32, .I32]) (.mk_list [])) := by
  apply Instr_ok.memory_fill _ (memType env.memories.val[0].ty)
  · simpa [h.mems] using hmem
  · simp only [h.mems]
    rw [getElem!_pos _ _ (by simpa using hmem), List.getElem_map]
  · exact h.wf
  · exact mem_type_wf _
  · exact .instr_case_64

theorem Matches.memory_init {env ctx C} (h : Matches env ctx C)
    (idx count : U32) (hc : env.data_count = some count) (hi : idx.val < count.val)
    (hmem : 0 < env.memories.val.length) :
    Instr_ok C (.MEMORY_INIT (.mk_uN idx.val))
      (.mk_functype (.mk_list [.I32, .I32, .I32]) (.mk_list [])) := by
  obtain ⟨hb, he⟩ := h.data_entry idx count hc hi
  apply Instr_ok.memory_init _ _ (memType env.memories.val[0].ty)
  · simpa [h.mems] using hmem
  · simp only [h.mems]
    rw [getElem!_pos _ _ (by simpa using hmem), List.getElem_map]
  · exact hb
  · exact he
  · exact h.wf
  · exact mem_type_wf _
  · exact .instr_case_66 _ (index_wf idx)

theorem Matches.data_drop {env ctx C} (h : Matches env ctx C)
    (idx count : U32) (hc : env.data_count = some count) (hi : idx.val < count.val) :
    Instr_ok C (.DATA_DROP (.mk_uN idx.val)) (.mk_functype (.mk_list []) (.mk_list [])) := by
  obtain ⟨hb, he⟩ := h.data_entry idx count hc hi
  exact .data_drop _ _ hb he h.wf (.instr_case_67 _ (index_wf idx))

end Itasca.Translation.Environment

end

/-! ## Reader -/

section

/-!
The reader specification for references, tables, and bulk memory records decoded
metadata, fixed stack effects, and exact source-prefix advancement. It includes
declared-reference evidence.
-/
namespace Itasca.Body
open Aeneas Aeneas.Std Itasca

/-- Exact successful decoder and fixed-stack effect, with the original source zipper. -/
abbrev MetadataReaderPost {data env locals index st}
    (p : Pending data env locals index st) {A B : Type}
    (decode : Result (core.result.Result A error.OpError × code.OpIterState))
    (pops : A → List wasm_types.ValueType) (output : A → Option wasm_types.ValueType)
    (metadata : A → B) (operation : A → instr) (value : B) (out : code.OpIterState) : Prop :=
    ∃ a middle values, decode = .ok (.Ok a,middle) ∧ middle.vals = st.core.vals ∧
      middle.ctrls = st.core.ctrls ∧ metadata a = value ∧
      Simd.readFixed middle (pops a) (output a) = .ok (.Ok (),out) ∧
      out.ctrls = st.core.ctrls ∧ out.pos = middle.pos ∧
      Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals (pops a) (output a) values ∧
      Body.ReaderPost p out (operation a) p.current.ctrl.polymorphic_base values ∧
      (∀ C, Translation.Environment.Matches env ⟨locals,p.ft.results⟩ C →
        Instr_ok C (operation a) (.mk_functype (.mk_list (Simd.inputTypes (pops a)))
          (.mk_list (Simd.outputTypes (output a)))))

theorem Pending.metadata_reader {data env locals index st}
    (p : Pending data env locals index st) {A B : Type}
    (decode : Result (core.result.Result A error.OpError × code.OpIterState))
    (pops : A → List wasm_types.ValueType) (output : A → Option wasm_types.ValueType)
    (metadata : A → B) (operation : A → instr)
    (decoded : decode ⦃ r => r.2.vals = st.core.vals ∧ r.2.ctrls = st.core.ctrls ∧
      ∀ a, r.1 = .Ok a → At data p.start (.plain (operation a)) r.2.pos ⦄)
    (wellFormed : ∀ a, wf_instr (operation a))
    (typing : ∀ a, (∃ state, decode = .ok (.Ok a,state)) → ∀ C,
      Translation.Environment.Matches env ⟨locals,p.ft.results⟩ C →
      Instr_ok C (operation a) (.mk_functype (.mk_list (Simd.inputTypes (pops a)))
        (.mk_list (Simd.outputTypes (output a)))))
    (declared : ∀ a, (∃ state, decode = .ok (.Ok a,state)) → Spec.DeclaredReferences.Instruction
      (Translation.Environment.declaredReferences env) (operation a))
    (size : st.core.vals.val.length < Usize.max) :
    metadataOperands decode pops output metadata ⦃ r => ∀ value, r.1 = .Ok value →
      MetadataReaderPost p decode pops output metadata operation value r.2 ⦄ := by
  obtain ⟨C,outer,spine,header,base,typed,ctrls,blocks,stack⟩ := p.opened
  have context := (spine.matches (Translation.Environment.Matches.root env ⟨locals,p.ft.results⟩)).enter
    (p.current.form.label p.current.ins p.current.outs)
  obtain ⟨⟨result,middle⟩,read,valuesEq,controlsEq,encoding⟩ := WP.spec_imp_exists decoded
  dsimp only at valuesEq controlsEq encoding
  cases result with
  | Err error => simp [metadataOperands,read]
  | Ok a =>
    have middleBase : (Body.Control.base middle).val = outer.length := by
      simp [Body.Control.base,controlsEq,ctrls,base]
    have poly : Body.Control.polymorphic middle = p.current.ctrl.polymorphic_base := by
      simp [Body.Control.polymorphic,controlsEq,ctrls]
    obtain ⟨⟨result,final⟩,readFixed,controls,position,values,afterValues,length,effect⟩ := WP.spec_imp_exists
      (Simd.readFixed.segment middle (pops a) (output a) outer p.current.vals
        (by simpa [valuesEq] using stack) middleBase (by simpa [valuesEq] using size))
    dsimp only at controls position afterValues length effect
    cases result with
    | Err error => simp [metadataOperands,read,readFixed]
    | Ok unitValue =>
      cases unitValue
      rw [WP.spec_equiv_exists]
      refine ⟨(.Ok (metadata a),final), by simp [metadataOperands,read,readFixed], ?_⟩
      intro value accepted
      have same : metadata a = value := by simpa using accepted
      subst value
      have newTyped := (effect rfl).prefix _ context.wf _ p.current.ops (operation a)
        (by simpa [poly,Frames.enter] using typed) (wellFormed a) (typing a ⟨middle,read⟩ _ context)
      have finalTyped := newTyped
      rw [poly] at finalTyped
      have sourceEncoding : At data p.start (.plain (operation a)) final.pos := by
        simpa only [position] using encoding a rfl
      have controlEq : final.ctrls.val = p.parents.map Frames.Saved.ctrl ++
          [{p.current.ctrl with polymorphic_base := p.current.ctrl.polymorphic_base}] := by
        simpa [controls,controlsEq] using ctrls
      have newBlocks : ({st with core := final} : code.BodyState).blocks.val =
          p.parents.map Frames.Saved.bt ++ [p.current.bt] := by
        simpa [controls,controlsEq,ctrls] using blocks
      refine ⟨a,middle,values,read,valuesEq,controlsEq,rfl,readFixed,controls.trans controlsEq,position,?_,?_,typing a ⟨middle,read⟩⟩
      · simpa only [poly] using effect rfl
      · exact p.append_reader_context C outer spine header base final (operation a)
          p.current.ctrl.polymorphic_base values (wellFormed a) sourceEncoding finalTyped
          controlEq newBlocks afterValues (declared a ⟨middle,read⟩)

end Itasca.Body

end

end

/-! ## Step -/

section

/-!
# Preservation for reference and table instructions

`Pending.table_get`, `Pending.table_set`, `Pending.ref_null`, `Pending.ref_func`,
`Pending.typed_select`, `Pending.table_grow`, `Pending.table_size`, `Pending.table_fill`,
`Pending.data_drop`, `Pending.elem_drop` and `Pending.ref_is_null` show that the corresponding
extracted readers preserve the body invariant `Pending` (Wasm 2.0). `Pending.metadata_read` is the
shared argument for readers that decode metadata and then apply a fixed stack effect.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body

/-- A successful metadata decoder supplies byte provenance and a principal
effect; the shared fixed checker transports both through the typed zipper. -/
theorem Pending.metadata_read {data env locals index st} (p : Pending data env locals index st)
    {A B : Type}
    (decode : Result (core.result.Result A error.OpError × code.OpIterState))
    (pops : A → List wasm_types.ValueType) (output : A → Option wasm_types.ValueType)
    (metadata : A → B) (operation : A → instr)
    (hd : decode ⦃ r => r.2.vals = st.core.vals ∧ r.2.ctrls = st.core.ctrls ∧
      ∀ a, r.1 = .Ok a → At data p.start (.plain (operation a)) r.2.pos ⦄)
    (hw : ∀ a, wf_instr (operation a))
    (ht : ∀ a, (∃ s, decode = .ok (.Ok a, s)) → ∀ C,
      Translation.Environment.Matches env ⟨locals, p.ft.results⟩ C →
      Instr_ok C (operation a) (.mk_functype (.mk_list (Simd.inputTypes (pops a)))
        (.mk_list (Simd.outputTypes (output a)))))
    (hsize : st.core.vals.val.length < Usize.max)
    (hdecl : ∀ a, Spec.DeclaredReferences.Instruction
      (Translation.Environment.declaredReferences env) (operation a) := by
        intro a
        simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]) :
    metadataOperands decode pops output metadata ⦃ r =>
      (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  apply WP.spec_mono (p.metadata_reader decode pops output metadata operation hd hw ht
    (fun a _ => hdecl a) hsize)
  intro r effect accepted
  obtain ⟨value, accepted⟩ := accepted
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, post, _⟩ := effect value accepted
  exact post.after

theorem reference_value_translation (rt : wasm_types.ElemType) :
    Translation.valueType (Module.Constants.referenceValueType rt) = valtype_reftype (Translation.referenceType rt) := by
  cases rt <;> rfl

theorem Pending.table_get {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 37#u8)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_table_get st.core data env ⦃ r => (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  rw [code.read_table_get.fixed]
  apply p.metadata_read
    (code.take_table st.core data env) (fun _ => [.I32]) (fun a => some a.2) Prod.fst
    (fun a => .TABLE_GET (.mk_uN a.1.val)) ?_ ?_ ?_ hsize
  · apply WP.spec_mono (code.take_table.spec st.core data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    dsimp only at hv hc hd ⊢
    refine ⟨hv, hc, ?_⟩
    rintro ⟨idx, ty⟩ hok
    obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx ty hok).1
    exact At.of_immediate p.inbounds hbyte p.pos (.reference (.tableGet idx hencoding))
      ⟨hbytes, hlen, hbound⟩
  · exact fun a => .instr_case_48 _ (Translation.Environment.index_wf a.1)
  · rintro ⟨idx, ty⟩ ⟨decoded, hrun⟩ C hC
    have hspec := code.take_table.spec st.core data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, hi, hty⟩ := hspec.2.2 idx ty rfl
    have htyped := hC.table_get idx env.tables.val[idx.val].ty hi rfl
    simpa [Simd.inputTypes, Simd.outputTypes, hty, reference_value_translation, show Translation.valueType .I32 = valtype.I32 from rfl]
      using htyped

theorem Pending.table_set {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 38#u8)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_table_set st.core data env ⦃ r => (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  rw [code.read_table_set.fixed]
  apply p.metadata_read
    (code.take_table st.core data env) (fun a => [a.2, .I32]) (fun _ => none) Prod.fst
    (fun a => .TABLE_SET (.mk_uN a.1.val)) ?_ ?_ ?_ hsize
  · apply WP.spec_mono (code.take_table.spec st.core data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    dsimp only at hv hc hd ⊢
    refine ⟨hv, hc, ?_⟩
    rintro ⟨idx, ty⟩ hok
    obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx ty hok).1
    exact At.of_immediate p.inbounds hbyte p.pos (.reference (.tableSet idx hencoding))
      ⟨hbytes, hlen, hbound⟩
  · exact fun a => .instr_case_49 _ (Translation.Environment.index_wf a.1)
  · rintro ⟨idx, ty⟩ ⟨decoded, hrun⟩ C hC
    have hspec := code.take_table.spec st.core data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, hi, hty⟩ := hspec.2.2 idx ty rfl
    have htyped := hC.table_set idx env.tables.val[idx.val].ty hi rfl
    simpa [Simd.inputTypes, Simd.outputTypes, hty, reference_value_translation, show Translation.valueType .I32 = valtype.I32 from rfl]
      using htyped

theorem Pending.ref_null {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 208#u8)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_ref_null st.core data ⦃ r => (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  rw [code.read_ref_null.fixed]
  apply p.metadata_read
    (code.take_reference_type st.core data) (fun _ => [])
    (fun rt => some (Module.Constants.referenceValueType rt)) id
    (fun rt => .REF_NULL (Translation.referenceType rt)) ?_ ?_ ?_ hsize
  · apply WP.spec_mono (code.take_reference_type.spec st.core data)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    exact ⟨hv, hc, fun rt hok => At.of_immediate p.inbounds hbyte p.pos
      (.reference (.refNull rt)) (hd rt hok)⟩
  · exact fun _ => .instr_case_40 _
  · intro rt _ C hC
    simpa [Simd.inputTypes, Simd.outputTypes, reference_value_translation] using
      Instr_ok.ref_null C (Translation.referenceType rt) hC.wf (.instr_case_40 _)

/-- The `ref.func` leaf uses the runtime declaration check independently of
its ordinary generated instruction typing. -/
theorem Pending.ref_func_reader {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 210#u8)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_ref_func st.core data env ⦃ r =>
      ∀ idx, r.1 = .Ok idx → idx.val < env.funcs.val.length ∧ r.2.ctrls = st.core.ctrls ∧
        r.2.vals.val = st.core.vals.val ++ [.Val .FuncRef] ∧
        ReaderPost p r.2 (.REF_FUNC (.mk_uN idx.val)) p.current.ctrl.polymorphic_base
          (p.current.vals ++ [.Val .FuncRef]) ∧
        Spec.DeclaredReferences.Instruction (Translation.Environment.declaredReferences env)
          (.REF_FUNC (.mk_uN idx.val)) ⦄ := by
  apply WP.spec_mono (code.read_ref_func.spec st.core data env hsize)
  rintro ⟨res, out⟩ ⟨hc, hout⟩ idx hok
  dsimp only at hc hout
  obtain ⟨hd, hi, hdecl, hv⟩ := hout idx hok
  refine ⟨hi, hc, hv, ?_, hdecl⟩
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, stack⟩ := id p.opened
  have hC := (spine.matches (Translation.Environment.Matches.root env ⟨locals, p.ft.results⟩)).enter
    (p.current.form.label p.current.ins p.current.outs)
  obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := hd
  refine p.append_reader_context C outer spine header base out
    (.REF_FUNC (.mk_uN idx.val)) p.current.ctrl.polymorphic_base
    (p.current.vals ++ [.Val .FuncRef]) (.instr_case_41 _ (Translation.Environment.index_wf idx))
    (At.of_immediate p.inbounds hbyte p.pos (.reference (.refFunc idx hencoding))
      ⟨hbytes, hlen, hbound⟩) ?_ ?_ ?_ ?_ hdecl
  · apply typed.append hC.wf _ (.instr_case_41 _ (Translation.Environment.index_wf idx))
    intro ts ht
    obtain ⟨front, hfront, rfl⟩ := (Body.Stack.realizes_append_concrete _ _ [.FuncRef] ts).mp ht
    exact ⟨front, hfront, by simpa [Frames.enter, Translation.valueType] using (Instrs_ok.frame _ _ front [] [.FUNCREF]
      (.instr _ _ [] [.FUNCREF] (hC.ref_func idx hi) hC.wf
        (.instr_case_41 _ (Translation.Environment.index_wf idx))) hC.wf
        (by simpa [Forall] using wf_instr.instr_case_41 _ (Translation.Environment.index_wf idx)))⟩
  · simpa [hc] using ctrls
  · simpa [code.BodyState.blocks_eq_of_ctrls hc] using blocks
  · simpa [stack, List.append_assoc] using hv

theorem Pending.ref_func {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 210#u8)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_ref_func st.core data env ⦃ r =>
      ∀ idx, r.1 = .Ok idx → p.After {st with core := r.2} ∧
        Spec.DeclaredReferences.Instruction (Translation.Environment.declaredReferences env)
          (.REF_FUNC (.mk_uN idx.val)) ⦄ := by
  apply WP.spec_mono (p.ref_func_reader hbyte hsize)
  intro r effect idx accepted
  obtain ⟨_, _, _, post, declared⟩ := effect idx accepted
  exact ⟨post.after, declared⟩

theorem Pending.typed_select {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 28#u8)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_typed_select st.core data ⦃ r => (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  rw [code.read_typed_select.fixed]
  apply p.metadata_read
    (selectType st.core data) (fun ty => [.I32, ty, ty]) some id
    (fun ty => .SELECT (some [Translation.valueType ty])) ?_ ?_ ?_ hsize
  · apply WP.spec_mono (selectType.spec st.core data)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    refine ⟨hv, hc, ?_⟩
    intro ty hok
    obtain ⟨count, hb, he⟩ := hd ty hok
    exact At.of_immediate p.inbounds hbyte p.pos (.reference (.selectTyped ty he)) hb
  · exact fun _ => .instr_case_3 _
  · intro ty _ C hC
    simpa [Simd.inputTypes, Simd.outputTypes, show Translation.valueType .I32 = valtype.I32 from rfl] using
      Instr_ok.select_expl C (Translation.valueType ty) hC.wf (.instr_case_3 _)

theorem Pending.table_grow {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 15#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_table_grow {st.core with pos := next} data env ⦃ r =>
      (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  rw [code.read_table_grow.fixed]
  apply p.metadata_read
    (code.take_table {st.core with pos := next} data env) (fun a => [.I32, a.2]) (fun _ => some .I32) Prod.fst
    (fun a => .TABLE_GROW (.mk_uN a.1.val)) ?_ ?_ ?_ hsize
  · apply WP.spec_mono (code.take_table.spec {st.core with pos := next} data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    dsimp only at hv hc hd ⊢
    refine ⟨hv, hc, ?_⟩
    rintro ⟨idx, ty⟩ hok
    obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx ty hok).1
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 15#u32 hpe (.tableGrow idx hencoding))
      ((Body.Scalar.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)
  · exact fun a => .instr_case_51 _ (Translation.Environment.index_wf a.1)
  · rintro ⟨idx, ty⟩ ⟨decoded, hrun⟩ C hC
    have hspec := code.take_table.spec {st.core with pos := next} data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, hi, hty⟩ := hspec.2.2 idx ty rfl
    have htyped := hC.table_grow idx env.tables.val[idx.val].ty hi rfl
    simpa [Simd.inputTypes, Simd.outputTypes, hty, reference_value_translation,
      show Translation.valueType .I32 = valtype.I32 from rfl] using htyped

theorem Pending.table_size {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 16#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_table_size {st.core with pos := next} data env ⦃ r =>
      (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  rw [code.read_table_size.fixed]
  apply p.metadata_read
    (code.take_table {st.core with pos := next} data env) (fun _ => []) (fun _ => some .I32) Prod.fst
    (fun a => .TABLE_SIZE (.mk_uN a.1.val)) ?_ ?_ ?_ hsize
  · apply WP.spec_mono (code.take_table.spec {st.core with pos := next} data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    dsimp only at hv hc hd ⊢
    refine ⟨hv, hc, ?_⟩
    rintro ⟨idx, ty⟩ hok
    obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx ty hok).1
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 16#u32 hpe (.tableSize idx hencoding))
      ((Body.Scalar.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)
  · exact fun a => .instr_case_50 _ (Translation.Environment.index_wf a.1)
  · rintro ⟨idx, ty⟩ ⟨decoded, hrun⟩ C hC
    have hspec := code.take_table.spec {st.core with pos := next} data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, hi, hty⟩ := hspec.2.2 idx ty rfl
    have htyped := hC.table_size idx env.tables.val[idx.val].ty hi rfl
    simpa [Simd.inputTypes, Simd.outputTypes, hty, reference_value_translation,
      show Translation.valueType .I32 = valtype.I32 from rfl] using htyped

theorem Pending.table_fill {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 17#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_table_fill {st.core with pos := next} data env ⦃ r =>
      (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  rw [code.read_table_fill.fixed]
  apply p.metadata_read
    (code.take_table {st.core with pos := next} data env) (fun a => [.I32, a.2, .I32]) (fun _ => none) Prod.fst
    (fun a => .TABLE_FILL (.mk_uN a.1.val)) ?_ ?_ ?_ hsize
  · apply WP.spec_mono (code.take_table.spec {st.core with pos := next} data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    dsimp only at hv hc hd ⊢
    refine ⟨hv, hc, ?_⟩
    rintro ⟨idx, ty⟩ hok
    obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx ty hok).1
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 17#u32 hpe (.tableFill idx hencoding))
      ((Body.Scalar.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)
  · exact fun a => .instr_case_52 _ (Translation.Environment.index_wf a.1)
  · rintro ⟨idx, ty⟩ ⟨decoded, hrun⟩ C hC
    have hspec := code.take_table.spec {st.core with pos := next} data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, hi, hty⟩ := hspec.2.2 idx ty rfl
    have htyped := hC.table_fill idx env.tables.val[idx.val].ty hi rfl
    simpa [Simd.inputTypes, Simd.outputTypes, hty, reference_value_translation,
      show Translation.valueType .I32 = valtype.I32 from rfl] using htyped

theorem Pending.data_drop {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 9#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.take_data_index {st.core with pos := next} data env ⦃ r =>
      (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  rw [← metadataOperands.empty (code.take_data_index {st.core with pos := next} data env)]
  apply p.metadata_read
    _ (fun _ => []) (fun _ => none) id
    (fun idx => .DATA_DROP (.mk_uN idx.val)) ?_ ?_ ?_ hsize
  · apply WP.spec_mono (code.take_data_index.spec {st.core with pos := next} data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    refine ⟨hv, hc, ?_⟩
    intro idx hok
    obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx hok).1
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 9#u32 hpe (.dataDrop idx hencoding))
      ((Body.Scalar.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)
  · exact fun a => .instr_case_67 _ (Translation.Environment.index_wf a)
  · rintro idx ⟨decoded, hrun⟩ C hC
    have hspec := code.take_data_index.spec {st.core with pos := next} data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, count, hc, hi⟩ := hspec.2.2 idx rfl
    exact hC.data_drop idx count hc hi

theorem Pending.elem_drop {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 13#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.take_element {st.core with pos := next} data env ⦃ r =>
      (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  rw [← metadataOperands.empty (code.take_element {st.core with pos := next} data env)]
  apply p.metadata_read
    _ (fun _ => []) (fun _ => none) id
    (fun a => .ELEM_DROP (.mk_uN a.1.val)) ?_ ?_ ?_ hsize
  · apply WP.spec_mono (code.take_element.spec {st.core with pos := next} data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    refine ⟨hv, hc, ?_⟩
    rintro ⟨idx, ty⟩ hok
    obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx ty hok).1
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 13#u32 hpe (.elemDrop idx hencoding))
      ((Body.Scalar.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)
  · exact fun a => .instr_case_55 _ (Translation.Environment.index_wf a.1)
  · rintro ⟨idx, ty⟩ ⟨decoded, hrun⟩ C hC
    have hspec := code.take_element.spec {st.core with pos := next} data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, hi, hty⟩ := hspec.2.2 idx ty rfl
    exact hC.elem_drop idx env.elem_segment_types.val[idx.val] hi rfl

theorem Pending.ref_is_null_reader {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 209#u8)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_ref_is_null st.core ⦃ r => r.2.ctrls = st.core.ctrls ∧ r.2.pos = st.core.pos ∧
      (r.1 = .Ok () → ∃ rt after,
        Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals
          [Module.Constants.referenceValueType rt] (some .I32) after ∧
        ReaderPost p r.2 .REF_IS_NULL p.current.ctrl.polymorphic_base after) ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, stack⟩ := id p.opened
  have hC := (spine.matches (Translation.Environment.Matches.root env ⟨locals, p.ft.results⟩)).enter
    (p.current.form.label p.current.ins p.current.outs)
  have hbase : (Body.Control.base st.core).val = outer.length := by simp [Body.Control.base, ctrls, base]
  have hpoly : Body.Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Body.Control.polymorphic, ctrls]
  apply WP.spec_mono (code.read_ref_is_null.segment st.core outer p.current.vals stack hbase hsize)
  rintro ⟨res, out⟩ ⟨hc, hp, after, hv, heffect⟩
  dsimp only at hc hp hv heffect
  refine ⟨hc, hp, ?_⟩
  intro hok
  obtain ⟨rt, he⟩ := heffect hok
  have htyped := he.prefix _ hC.wf _ p.current.ops .REF_IS_NULL
    (by simpa [hpoly, Frames.enter] using typed) .instr_case_42
    (by simpa [Simd.inputTypes, Simd.outputTypes, reference_value_translation,
      show Translation.valueType .I32 = valtype.I32 from rfl] using
      Instr_ok.ref_is_null _ (Translation.referenceType rt) hC.wf .instr_case_42)
  refine ⟨rt, after, (by simpa [hpoly] using he), ?_⟩
  refine p.append_reader_context C outer spine header base out .REF_IS_NULL
    p.current.ctrl.polymorphic_base after .instr_case_42 ?_
    (by simpa [hpoly, Frames.enter] using htyped) ?_ ?_ hv (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices])

  · apply At.of_immediate p.inbounds hbyte p.pos (.reference .refIsNull)
    exact ⟨by simp [hp], by simp [hp], by have := p.pos; have := p.inbounds; simp only [hp]; omega⟩
  · simpa [hc] using ctrls
  · simpa [code.BodyState.blocks_eq_of_ctrls hc] using blocks

theorem Pending.ref_is_null {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 209#u8)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_ref_is_null st.core ⦃ r => (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  apply WP.spec_mono (p.ref_is_null_reader hbyte hsize)
  intro r effect accepted
  obtain ⟨unitValue, accepted⟩ := accepted
  cases unitValue
  obtain ⟨_, _, _, post⟩ := effect.2.2 accepted
  exact post.after

end Itasca.Body

end
