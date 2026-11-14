import Itasca.Wasm2.References.Readers
import Itasca.Wasm2.SuffixTyping
import Itasca.Binary.Wasm2.DeclaredReferences
import Itasca.Wasm2.Scalar.IndexReader

/-!
Sections, each formerly its own module: Operands, EnvMatches, Reader.
-/

/-! ## Operands -/

section

/-!
# Operand factorization of reference readers

Each extracted `code.read_ref_null`, `code.read_table_get`, `code.read_table_set`,
`code.read_table_grow`, `code.read_table_size`, `code.read_table_fill` and
`code.read_typed_select` equals `Wasm2.metadataOperands` applied to its metadata decoder, which
is the decoder followed by the fixed pop and push of `Simd.readFixed`.
`code.read_ref_is_null.segment` gives the typing of the polymorphic null test.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

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
        Wasm1.BytesAt data st.pos (count ++ [valueByte ty]) r.2.pos ∧ Leb128.Encoding count 1 ⦄ := by
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
      exact ⟨bytes, (show Wasm1.BytesAt data st.pos bytes s.pos from ⟨hb, hl, hn⟩).append (htag ty hok), he⟩
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

end Itasca.Wasm2

namespace Itasca

/-- The extracted handler has exactly its metadata-dependent fixed operand effect. -/
theorem code.read_ref_null.fixed (st : code.OpIterState) (data : Slice U8) :
    code.read_ref_null st data = Wasm2.metadataOperands (code.take_reference_type st data)
      (fun _ => []) (fun rt => some (ModuleConstants.referenceValueType rt)) id := by
  simp only [code.read_ref_null, Wasm2.metadataOperands]
  congr 1
  funext pair
  obtain ⟨r, state⟩ := pair
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok a =>
    try (cases (show U32 × wasm_types.ValueType from a))
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      wasm_types.ElemType.value_type.eq, Wasm2.Simd.readFixed, Std.bind_assoc, Std.uncurry]
    try dsimp only
    repeat' rfl

/-- The extracted handler has exactly its metadata-dependent fixed operand effect. -/
theorem code.read_table_get.fixed (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) :
    code.read_table_get st data env = Wasm2.metadataOperands (code.take_table st data env)
      (fun _ => [.I32]) (fun a => some a.2) Prod.fst := by
  simp only [code.read_table_get, Wasm2.metadataOperands]
  congr 1
  funext pair
  obtain ⟨r, state⟩ := pair
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok a =>
    try (cases (show U32 × wasm_types.ValueType from a))
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      Wasm2.Simd.readFixed, Std.bind_assoc, Std.uncurry]
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
theorem code.read_table_set.fixed (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) :
    code.read_table_set st data env = Wasm2.metadataOperands (code.take_table st data env)
      (fun a => [a.2, .I32]) (fun _ => none) Prod.fst := by
  simp only [code.read_table_set, Wasm2.metadataOperands]
  congr 1
  funext pair
  obtain ⟨r, state⟩ := pair
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok a =>
    try (cases (show U32 × wasm_types.ValueType from a))
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      Wasm2.Simd.readFixed, Std.bind_assoc, Std.uncurry]
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
theorem code.read_table_grow.fixed (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) :
    code.read_table_grow st data env = Wasm2.metadataOperands (code.take_table st data env)
      (fun a => [.I32, a.2]) (fun _ => some .I32) Prod.fst := by
  simp only [code.read_table_grow, Wasm2.metadataOperands]
  congr 1
  funext pair
  obtain ⟨r, state⟩ := pair
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok a =>
    try (cases (show U32 × wasm_types.ValueType from a))
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      Wasm2.Simd.readFixed, Std.bind_assoc, Std.uncurry]
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
theorem code.read_table_size.fixed (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) :
    code.read_table_size st data env = Wasm2.metadataOperands (code.take_table st data env)
      (fun _ => []) (fun _ => some .I32) Prod.fst := by
  simp only [code.read_table_size, Wasm2.metadataOperands]
  congr 1
  funext pair
  obtain ⟨r, state⟩ := pair
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok a =>
    try (cases (show U32 × wasm_types.ValueType from a))
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      Wasm2.Simd.readFixed, Std.bind_assoc, Std.uncurry]
    try dsimp only

/-- The extracted handler has exactly its metadata-dependent fixed operand effect. -/
theorem code.read_table_fill.fixed (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) :
    code.read_table_fill st data env = Wasm2.metadataOperands (code.take_table st data env)
      (fun a => [.I32, a.2, .I32]) (fun _ => none) Prod.fst := by
  simp only [code.read_table_fill, Wasm2.metadataOperands]
  congr 1
  funext pair
  obtain ⟨r, state⟩ := pair
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok a =>
    try (cases (show U32 × wasm_types.ValueType from a))
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      Wasm2.Simd.readFixed, Std.bind_assoc, Std.uncurry]
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
    code.read_typed_select st data = Wasm2.metadataOperands (Wasm2.selectType st data)
      (fun ty => [.I32, ty, ty]) some id := by
  obtain ⟨⟨r, state⟩, hr, _⟩ := WP.spec_imp_exists (code.take_index.spec st data)
  cases r with
  | Err e => simp [code.read_typed_select, Wasm2.metadataOperands, Wasm2.selectType, hr,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok count =>
    by_cases hc : count = 1#u32
    · subst count
      simp [code.read_typed_select, Wasm2.metadataOperands, Wasm2.selectType, hr,
        core.result.Result.Insts.CoreOpsTry.branch]
      congr 1
      funext pair
      obtain ⟨r, state⟩ := pair
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok ty =>
        simp only [bind_ok, Wasm2.Simd.readFixed, Std.bind_assoc, Std.uncurry]
        repeat' first
          | rfl
          | (congr 1
             funext pair
             obtain ⟨res, state⟩ := pair
             cases res <;> simp [
               core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
               Std.bind_assoc])
    · have hcv : count.val ≠ 1 := fun he => hc (UScalar.eq_of_val_eq he)
      simp [code.read_typed_select, Wasm2.metadataOperands, Wasm2.selectType, hr, hc, hcv,
        core.result.Result.Insts.CoreOpsTry.branch]

/-- A successful null test consumes a reference (or the polymorphic bottom)
and produces i32. The chosen reference type remains explicit in the typing. -/
theorem code.read_ref_is_null.segment (st : code.OpIterState)
    (outer segment : List code.StackType)
    (hv : st.vals.val = outer ++ segment) (hb : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max) :
    code.read_ref_is_null st ⦃ r => r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ after, r.2.vals.val = outer ++ after ∧
        (r.1 = .Ok () → ∃ rt, Wasm2.Simd.FixedEffect (Control.polymorphic st) segment
          [ModuleConstants.referenceValueType rt] (some .I32) after) ⦄ := by
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
    change StackSemantics.Popped (Control.polymorphic st) segment t popped at hpop
    have hcap : s.vals.val.length < Usize.max := by
      simp only [hv, hpv, List.length_append] at *
      omega
    have finish (rt : wasm_types.ElemType)
        (ht : Sequence.Accepts t (valtype_reftype (Translate.referenceType rt)))
        (hrun : code.read_ref_is_null st = do
          let out ← code.push_val s (.Val .I32)
          .ok (.Ok (), out)) :
        code.read_ref_is_null st ⦃ r => r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
          ∃ after, r.2.vals.val = outer ++ after ∧
            (r.1 = .Ok () → ∃ rt, Wasm2.Simd.FixedEffect (Control.polymorphic st) segment
              [ModuleConstants.referenceValueType rt] (some .I32) after) ⦄ := by
      obtain ⟨out, ho, hov, hoc, hop⟩ := WP.spec_imp_exists (code.push_val.spec s (.Val .I32) hcap)
      rw [hrun, ho, bind_ok, WP.spec_ok]
      refine ⟨hoc.trans hc, hop.trans hp, popped ++ [.Val .I32],
        by simpa [hpv, List.append_assoc] using hov, ?_⟩
      intro _
      refine ⟨rt, ?_⟩
      intro ts hts
      obtain ⟨front, hfront, rfl⟩ := (Sequence.realizes_append_concrete _ _ [.I32] ts).mp hts
      refine ⟨front, rfl, ?_⟩
      have hh := hpop.realizes front (valtype_reftype (Translate.referenceType rt)) ht hfront
      cases rt <;> simpa [Wasm2.Simd.inputTypes, ModuleConstants.referenceValueType, Translate.referenceType,
        Translate.valueType, valtype_reftype] using hh
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

Lemmas about `EnvTranslation.Matches`, the agreement between a runtime `metadata.Env` and a
SpecTec context. Each `Matches.table_get`, `Matches.table_copy`, `Matches.memory_init`, ... turns
bounds on the runtime environment into the corresponding `Instr_ok` judgment for the reference,
table and bulk-memory instructions.
-/

open Aeneas Aeneas.Std

namespace Itasca.EnvTranslation

/-- A runtime table entry supplies the corresponding generated lookup. -/
theorem Matches.table_entry {env ctx C} (h : Matches env ctx C)
    (idx : U32) (tt : wasm_types.TableType) (hi : idx.val < env.table_types.val.length)
    (ht : env.table_types.val[idx.val] = tt) :
    idx.val < C.TABLES.length ∧ C.TABLES[idx.val]! = tableType tt := by
  rw [h.tables]
  constructor
  · simpa using hi
  · rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map, ht]

theorem Matches.element_entry {env ctx C} (h : Matches env ctx C)
    (idx : U32) (elem : metadata.Element) (hi : idx.val < env.elements.val.length)
    (ht : env.elements.val[idx.val] = elem) :
    idx.val < C.ELEMS.length ∧ C.ELEMS[idx.val]! = Translate.referenceType elem.elem := by
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
    (idx : U32) (hi : idx.val < env.func_types.val.length) :
    Instr_ok C (.REF_FUNC (.mk_uN idx.val)) (.mk_functype (.mk_list []) (.mk_list [.FUNCREF])) := by
  apply Instr_ok.ref_func _ _ (funcType env.func_types.val[idx.val])
  · simpa [h.funcs, proj_uN_0] using hi
  · simp only [h.funcs, proj_uN_0]
    rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map]
  · exact h.wf
  · exact .instr_case_41 _ (index_wf idx)

theorem Matches.table_get {env ctx C} (h : Matches env ctx C)
    (idx : U32) (tt : wasm_types.TableType) (hi : idx.val < env.table_types.val.length)
    (ht : env.table_types.val[idx.val] = tt) :
    Instr_ok C (.TABLE_GET (.mk_uN idx.val))
      (.mk_functype (.mk_list [.I32]) (.mk_list [valtype_reftype (Translate.referenceType tt.elem)])) := by
  obtain ⟨hb, he⟩ := h.table_entry idx tt hi ht
  exact .table_get _ _ _ _ hb he h.wf (.instr_case_48 _ (index_wf idx)) (tableType_wf tt)

theorem Matches.table_set {env ctx C} (h : Matches env ctx C)
    (idx : U32) (tt : wasm_types.TableType) (hi : idx.val < env.table_types.val.length)
    (ht : env.table_types.val[idx.val] = tt) :
    Instr_ok C (.TABLE_SET (.mk_uN idx.val))
      (.mk_functype (.mk_list [.I32, valtype_reftype (Translate.referenceType tt.elem)]) (.mk_list [])) := by
  obtain ⟨hb, he⟩ := h.table_entry idx tt hi ht
  exact .table_set _ _ _ _ hb he h.wf (.instr_case_49 _ (index_wf idx)) (tableType_wf tt)

theorem Matches.table_size {env ctx C} (h : Matches env ctx C)
    (idx : U32) (tt : wasm_types.TableType) (hi : idx.val < env.table_types.val.length)
    (ht : env.table_types.val[idx.val] = tt) :
    Instr_ok C (.TABLE_SIZE (.mk_uN idx.val))
      (.mk_functype (.mk_list []) (.mk_list [.I32])) := by
  obtain ⟨hb, he⟩ := h.table_entry idx tt hi ht
  exact .table_size _ _ _ _ hb he h.wf (.instr_case_50 _ (index_wf idx)) (tableType_wf tt)

theorem Matches.table_grow {env ctx C} (h : Matches env ctx C)
    (idx : U32) (tt : wasm_types.TableType) (hi : idx.val < env.table_types.val.length)
    (ht : env.table_types.val[idx.val] = tt) :
    Instr_ok C (.TABLE_GROW (.mk_uN idx.val))
      (.mk_functype (.mk_list [valtype_reftype (Translate.referenceType tt.elem), .I32]) (.mk_list [.I32])) := by
  obtain ⟨hb, he⟩ := h.table_entry idx tt hi ht
  exact .table_grow _ _ _ _ hb he h.wf (.instr_case_51 _ (index_wf idx)) (tableType_wf tt)

theorem Matches.table_fill {env ctx C} (h : Matches env ctx C)
    (idx : U32) (tt : wasm_types.TableType) (hi : idx.val < env.table_types.val.length)
    (ht : env.table_types.val[idx.val] = tt) :
    Instr_ok C (.TABLE_FILL (.mk_uN idx.val))
      (.mk_functype (.mk_list [.I32, valtype_reftype (Translate.referenceType tt.elem), .I32]) (.mk_list [])) := by
  obtain ⟨hb, he⟩ := h.table_entry idx tt hi ht
  exact .table_fill _ _ _ _ hb he h.wf (.instr_case_52 _ (index_wf idx)) (tableType_wf tt)

theorem Matches.table_copy {env ctx C} (h : Matches env ctx C)
    (destination source : U32) (dst src : wasm_types.TableType)
    (hd : destination.val < env.table_types.val.length) (hs : source.val < env.table_types.val.length)
    (htd : env.table_types.val[destination.val] = dst) (hts : env.table_types.val[source.val] = src)
    (htype : src.elem = dst.elem) :
    Instr_ok C (.TABLE_COPY (.mk_uN destination.val) (.mk_uN source.val))
      (.mk_functype (.mk_list [.I32, .I32, .I32]) (.mk_list [])) := by
  obtain ⟨hdb, hde⟩ := h.table_entry destination dst hd htd
  obtain ⟨hsb, hse⟩ := h.table_entry source src hs hts
  exact .table_copy C _ _ (limitsType dst.limits) (Translate.referenceType dst.elem)
    (limitsType src.limits) hdb hde hsb (by simpa [tableType, htype, proj_uN_0] using hse) h.wf
    (.instr_case_53 _ _ (index_wf destination) (index_wf source)) (tableType_wf dst)
    (by simpa [tableType, htype] using tableType_wf src)

theorem Matches.table_init {env ctx C} (h : Matches env ctx C)
    (table element : U32) (tt : wasm_types.TableType) (elem : metadata.Element)
    (ht : table.val < env.table_types.val.length) (he : element.val < env.elements.val.length)
    (htt : env.table_types.val[table.val] = tt) (hee : env.elements.val[element.val] = elem)
    (htype : elem.elem = tt.elem) :
    Instr_ok C (.TABLE_INIT (.mk_uN table.val) (.mk_uN element.val))
      (.mk_functype (.mk_list [.I32, .I32, .I32]) (.mk_list [])) := by
  obtain ⟨htb, hte⟩ := h.table_entry table tt ht htt
  obtain ⟨heb, hee⟩ := h.element_entry element elem he hee
  exact .table_init _ _ _ _ _ htb hte heb (by simpa [htype, proj_uN_0] using hee) h.wf
    (.instr_case_54 _ _ (index_wf table) (index_wf element)) (tableType_wf tt)

theorem Matches.elem_drop {env ctx C} (h : Matches env ctx C)
    (idx : U32) (elem : metadata.Element) (hi : idx.val < env.elements.val.length)
    (ht : env.elements.val[idx.val] = elem) :
    Instr_ok C (.ELEM_DROP (.mk_uN idx.val)) (.mk_functype (.mk_list []) (.mk_list [])) := by
  obtain ⟨hb, he⟩ := h.element_entry idx elem hi ht
  exact .elem_drop _ _ _ hb he h.wf (.instr_case_55 _ (index_wf idx))

theorem Matches.memory_copy {env ctx C} (h : Matches env ctx C)
    (hmem : 0 < env.mem_types.val.length) :
    Instr_ok C .MEMORY_COPY (.mk_functype (.mk_list [.I32, .I32, .I32]) (.mk_list [])) := by
  apply Instr_ok.memory_copy _ (memType env.mem_types.val[0])
  · simpa [h.mems] using hmem
  · simp only [h.mems]
    rw [getElem!_pos _ _ (by simpa using hmem), List.getElem_map]
  · exact h.wf
  · exact memType_wf _
  · exact .instr_case_65

theorem Matches.memory_fill {env ctx C} (h : Matches env ctx C)
    (hmem : 0 < env.mem_types.val.length) :
    Instr_ok C .MEMORY_FILL (.mk_functype (.mk_list [.I32, .I32, .I32]) (.mk_list [])) := by
  apply Instr_ok.memory_fill _ (memType env.mem_types.val[0])
  · simpa [h.mems] using hmem
  · simp only [h.mems]
    rw [getElem!_pos _ _ (by simpa using hmem), List.getElem_map]
  · exact h.wf
  · exact memType_wf _
  · exact .instr_case_64

theorem Matches.memory_init {env ctx C} (h : Matches env ctx C)
    (idx count : U32) (hc : env.data_count = some count) (hi : idx.val < count.val)
    (hmem : 0 < env.mem_types.val.length) :
    Instr_ok C (.MEMORY_INIT (.mk_uN idx.val))
      (.mk_functype (.mk_list [.I32, .I32, .I32]) (.mk_list [])) := by
  obtain ⟨hb, he⟩ := h.data_entry idx count hc hi
  apply Instr_ok.memory_init _ _ (memType env.mem_types.val[0])
  · simpa [h.mems] using hmem
  · simp only [h.mems]
    rw [getElem!_pos _ _ (by simpa using hmem), List.getElem_map]
  · exact hb
  · exact he
  · exact h.wf
  · exact memType_wf _
  · exact .instr_case_66 _ (index_wf idx)

theorem Matches.data_drop {env ctx C} (h : Matches env ctx C)
    (idx count : U32) (hc : env.data_count = some count) (hi : idx.val < count.val) :
    Instr_ok C (.DATA_DROP (.mk_uN idx.val)) (.mk_functype (.mk_list []) (.mk_list [])) := by
  obtain ⟨hb, he⟩ := h.data_entry idx count hc hi
  exact .data_drop _ _ hb he h.wf (.instr_case_67 _ (index_wf idx))

end Itasca.EnvTranslation

end

/-! ## Reader -/

section

/-!
Shared metadata decoding, fixed-stack effects, and exact source-prefix advancement.
Reference, table, and bulk-memory preservation and compiler inversion use the same
reader specification, with explicit declared-reference evidence.
-/
namespace Itasca.Wasm2
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
      Wasm2.ReaderPost p out (operation a) p.current.ctrl.polymorphic_base values ∧
      (∀ C, EnvTranslation.Matches env ⟨locals,p.ft.results⟩ C →
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
      EnvTranslation.Matches env ⟨locals,p.ft.results⟩ C →
      Instr_ok C (operation a) (.mk_functype (.mk_list (Simd.inputTypes (pops a)))
        (.mk_list (Simd.outputTypes (output a)))))
    (declared : ∀ a, (∃ state, decode = .ok (.Ok a,state)) → DeclaredReferences.Instruction
      (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) (operation a))
    (size : st.core.vals.val.length < Usize.max) :
    metadataOperands decode pops output metadata ⦃ r => ∀ value, r.1 = .Ok value →
      MetadataReaderPost p decode pops output metadata operation value r.2 ⦄ := by
  obtain ⟨C,outer,spine,header,base,typed,ctrls,blocks,stack⟩ := p.opened
  have context := (spine.matches (EnvTranslation.Matches.root env ⟨locals,p.ft.results⟩)).enter
    (p.current.form.label p.current.ins p.current.outs)
  obtain ⟨⟨result,middle⟩,read,valuesEq,controlsEq,encoding⟩ := WP.spec_imp_exists decoded
  dsimp only at valuesEq controlsEq encoding
  cases result with
  | Err error => simp [metadataOperands,read]
  | Ok a =>
    have middleBase : (Control.base middle).val = outer.length := by
      simp [Control.base,controlsEq,ctrls,base]
    have poly : Control.polymorphic middle = p.current.ctrl.polymorphic_base := by
      simp [Control.polymorphic,controlsEq,ctrls]
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
      have newTyped := (effect rfl).wasm2_prefix _ context.wf _ p.current.ops (operation a)
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

theorem Pending.metadata_reader_accepted {data env locals index st}
    (p : Pending data env locals index st) {A B : Type}
    (decode : Result (core.result.Result A error.OpError × code.OpIterState))
    (pops : A → List wasm_types.ValueType) (output : A → Option wasm_types.ValueType)
    (metadata : A → B) (operation : A → instr)
    (decoded : decode ⦃ r => r.2.vals = st.core.vals ∧ r.2.ctrls = st.core.ctrls ∧
      ∀ a, r.1 = .Ok a → At data p.start (.plain (operation a)) r.2.pos ⦄)
    (wellFormed : ∀ a, wf_instr (operation a))
    (typing : ∀ a, (∃ state, decode = .ok (.Ok a,state)) → ∀ C,
      EnvTranslation.Matches env ⟨locals,p.ft.results⟩ C →
      Instr_ok C (operation a) (.mk_functype (.mk_list (Simd.inputTypes (pops a)))
        (.mk_list (Simd.outputTypes (output a)))))
    (declared : ∀ a, (∃ state, decode = .ok (.Ok a,state)) → DeclaredReferences.Instruction
      (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) (operation a))
    (size : st.core.vals.val.length < Usize.max) (value : B) (out : code.OpIterState)
    (accepted : metadataOperands decode pops output metadata = .ok (.Ok value,out)) :
    MetadataReaderPost p decode pops output metadata operation value out := by
  have effect := p.metadata_reader decode pops output metadata operation decoded wellFormed typing declared size
  rw [accepted, WP.spec_ok] at effect
  exact effect value rfl

end Itasca.Wasm2

end
