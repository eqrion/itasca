import Itasca.Wasm2.Bulk.Complete
import Itasca.Wasm2.Simd.Complete
import Itasca.Wasm2.Complete.Leaf
import Itasca.Wasm2.Control.Return
import Itasca.Wasm2.Control.BranchStep
import Itasca.Support.EnvTranslation
import Itasca.Wasm2.References.Complete

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

theorem EnvironmentWithinLimits.resolve_bound {env} (h : EnvironmentWithinLimits env)
    (view : signature.ResultType) (ts : List types.ValueType) (ht : resolve env view = some ts) :
    ts.length ≤ 1000 := by
  cases view with
  | Empty => simp [resolve] at ht; subst ts; simp
  | One t => simp [resolve] at ht; subst ts; simp
  | «Type» idx part =>
    cases hi : env.types.val[idx.val]? with
    | none => simp [resolve, hi] at ht
    | some ft =>
      have hm : ft ∈ env.types.val := List.mem_of_getElem? hi
      cases part <;> simp [resolve, hi] at ht <;> subst ts
      · exact (h.types ft hm).1
      · exact (h.types ft hm).2

theorem Labels.lookup {env st C} (hl : Labels env st C) (depth : U32)
    (hi : depth.val < C.LABELS.length) :
    ∃ view ts, labelAt st depth.val = some view ∧ resolve env view = some ts ∧
      C.LABELS[depth.val]! = .mk_list (ts.map Translate.valueType) := by
  have he := hl depth.val
  rw [List.getElem?_eq_getElem hi] at he
  unfold labelTypes at he
  cases hv : labelAt st depth.val with
  | none => simp [hv] at he
  | some view =>
    cases ht : resolve env view with
    | none => simp [hv, ht] at he
    | some ts =>
      refine ⟨view, ts, rfl, ht, ?_⟩
      rw [getElem!_pos C.LABELS depth.val hi]
      simpa [hv, ht] using he

namespace Completeness

def LeafResult {st} (f : Frame st) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (opcode : U8) (bytes : List U8) (next : Usize) (out : List valtype) : Prop :=
  ∃ s, step st data env ctx index opcode = .ok (.Ok (), s) ∧ s.core.pos = next ∧
    f.Output out s ∧ s.core.vals.val.length ≤ st.core.vals.val.length + 500 * (bytes.length + 1)

private theorem encoding_nonempty {bytes n} (h : Leb128.Encoding bytes n) : 1 ≤ bytes.length := by
  obtain ⟨bs, hb, _, _⟩ := h
  cases bs <;> simp_all

theorem Frame.call {st} (f : Frame st) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (C : context) (hmatch : EnvTranslation.Matches env ctx C)
    (henv : EnvironmentWithinLimits env) (idx : U32) (bytes : List U8) (next : Usize)
    (he : Leb128.Encoding bytes idx.val) (hb : Wasm1.BytesAt data st.core.pos bytes next)
    (front input output : List valtype)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input))
    (ht : Instr_ok C (.CALL (.mk_uN idx.val)) (.mk_functype (.mk_list input) (.mk_list output)))
    (hcap : st.core.vals.val.length + 1000 < Usize.max) :
    LeafResult f data env ctx index 0x10#u8 bytes next (front ++ output) := by
  cases ht with
  | call _ _ params results hi ht _ _ =>
    obtain ⟨ft, hi, ht, hv⟩ := hmatch.func_lookup idx _ hi ht
    have hparams : ft.params.val.map Translate.valueType = input :=
      list.mk_list.inj (functype.mk_functype.inj hv).1
    have hresults : ft.results.val.map Translate.valueType = output :=
      list.mk_list.inj (functype.mk_functype.inj hv).2
    have hlimits := henv.funcs ft (ht ▸ List.getElem_mem hi)
    obtain ⟨⟨_, s⟩, hrun, rfl, hc, hblocks, hp, rest, hvals, hlen, hreal⟩ := WP.spec_imp_exists
      (code.call.direct_complete st data env idx next ft ⟨bytes, hb.suffix, hb.length, hb.bound, he⟩
        hi ht hlimits.1 hlimits.2 f.core.outer f.core.operands front f.core.vals f.core.base_eq
        (by omega) (by simpa [f.core.poly_eq, hparams] using hr))
    dsimp only at hc hblocks hp hvals hlen hreal
    refine ⟨s, by simpa [step] using hrun, hp,
      ⟨f.core.output_of_same_ctrls hc hvals (by simpa [hresults] using hreal), hblocks⟩, ?_⟩
    have hbytes := encoding_nonempty he
    simp only [hvals, f.core.vals, List.length_append]
    omega

theorem Frame.call_indirect_indexed {st} (f : Frame st) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (C : context) (hmatch : EnvTranslation.Matches env ctx C)
    (henv : EnvironmentWithinLimits env) (idx table : U32) (bytes tableBytes : List U8) (next : Usize)
    (he : Leb128.Encoding bytes idx.val) (hte : Leb128.Encoding tableBytes table.val)
    (hb : Wasm1.BytesAt data st.core.pos (bytes ++ tableBytes) next)
    (front input output : List valtype)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input))
    (ht : Instr_ok C (.CALL_INDIRECT (.mk_uN table.val) (.mk_uN idx.val))
      (.mk_functype (.mk_list input) (.mk_list output)))
    (hcap : st.core.vals.val.length + 1000 < Usize.max) :
    LeafResult f data env ctx index 0x11#u8 (bytes ++ tableBytes) next (front ++ output) := by
  cases ht with
  | call_indirect _ _ _ params results lim htable htabletype hi ht _ _ _ =>
    obtain ⟨ft, hi, ht, hv⟩ := hmatch.type_lookup idx _ hi ht
    have hparams : ft.params.val.map Translate.valueType = params :=
      list.mk_list.inj (functype.mk_functype.inj hv).1
    have hresults : ft.results.val.map Translate.valueType = output :=
      list.mk_list.inj (functype.mk_functype.inj hv).2
    have hlimits := henv.types ft (ht ▸ List.getElem_mem hi)
    obtain ⟨middle, hindex, hzero⟩ := hb.split
    obtain ⟨htableenv, hfun⟩ := hmatch.table_funcref table lim htable htabletype
    obtain ⟨⟨_, s⟩, hrun, rfl, hc, hblocks, hp, rest, hvals, hlen, hreal⟩ := WP.spec_imp_exists
      (code.call.indirect_complete st data env idx table middle next ft
        ⟨bytes, hindex.suffix, hindex.length, hindex.bound, he⟩
        ⟨tableBytes, hzero.suffix, hzero.length, hzero.bound, hte⟩ htableenv hfun hi ht hlimits.1 hlimits.2 f.core.outer f.core.operands front
        f.core.vals f.core.base_eq (by omega) (by simpa [f.core.poly_eq, hparams] using hr))
    dsimp only at hc hblocks hp hvals hlen hreal
    refine ⟨s, by simpa [step] using hrun, hp,
      ⟨f.core.output_of_same_ctrls hc hvals (by simpa [hresults] using hreal), hblocks⟩, ?_⟩
    have hbytes := encoding_nonempty he
    have htables := encoding_nonempty hte
    simp only [hvals, f.core.vals, List.length_append]
    omega

theorem Frame.call_indirect {st} (f : Frame st) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (C : context) (hmatch : EnvTranslation.Matches env ctx C)
    (henv : EnvironmentWithinLimits env) (idx : U32) (bytes : List U8) (next : Usize)
    (he : Leb128.Encoding bytes idx.val) (hb : Wasm1.BytesAt data st.core.pos (bytes ++ [0#u8]) next)
    (front input output : List valtype)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input))
    (ht : Instr_ok C (.CALL_INDIRECT (.mk_uN 0) (.mk_uN idx.val))
      (.mk_functype (.mk_list input) (.mk_list output)))
    (hcap : st.core.vals.val.length + 1000 < Usize.max) :
    LeafResult f data env ctx index 0x11#u8 (bytes ++ [0#u8]) next (front ++ output) := by
  apply f.call_indirect_indexed data env ctx index C hmatch henv idx 0#u32 bytes [0#u8]
    next he _ hb front input output hr ht hcap
  exact ⟨[], 0#u8, rfl, by simp, by simp, by decide, by simp, by simp [Leb128.payload]⟩

theorem Frame.branch {st} (f : Frame st) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (C : context) (hlabels : Labels env st C)
    (depth : U32) (bytes : List U8) (next : Usize)
    (he : Leb128.Encoding bytes depth.val) (hb : Wasm1.BytesAt data st.core.pos bytes next)
    (front input output : List valtype)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input))
    (ht : Instr_ok C (.BR (.mk_uN depth.val)) (.mk_functype (.mk_list input) (.mk_list output))) :
    LeafResult f data env ctx index 0x0C#u8 bytes next (front ++ output) := by
  cases ht with
  | br _ _ before args after hi ht _ _ =>
    obtain ⟨view, ts, hl, hts, hlookup⟩ := hlabels.lookup depth hi
    have hargs : ts.map Translate.valueType = args := by
      simpa [proj_uN_0, proj_list_0, hlookup] using ht
    obtain ⟨s, hrun, hc, hblocks, hp, hv⟩ := code.branch.complete st data env depth next view ts
      f.core.parents f.core.current f.core.outer f.core.operands (front ++ before)
      f.core.ctrls f.core.vals f.core.base
      (by simp [f.blocks, f.core.ctrls, f.aligned])
      ⟨bytes, hb.suffix, hb.length, hb.bound, he⟩ hl hts
      (by simpa [f.core.poly_eq, hargs, List.append_assoc] using hr)
    refine ⟨s, by simpa [step] using hrun, hp,
      ⟨⟨true, [], hc, by simpa using hv, Sequence.realizes_polymorphic_empty _⟩, hblocks⟩, ?_⟩
    simp only [hv, f.core.vals, List.length_append]
    omega

theorem Frame.branch_if {st} (f : Frame st) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (C : context) (hlabels : Labels env st C) (henv : EnvironmentWithinLimits env)
    (depth : U32) (bytes : List U8) (next : Usize)
    (he : Leb128.Encoding bytes depth.val) (hb : Wasm1.BytesAt data st.core.pos bytes next)
    (front input output : List valtype)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input))
    (ht : Instr_ok C (.BR_IF (.mk_uN depth.val)) (.mk_functype (.mk_list input) (.mk_list output)))
    (hcap : st.core.vals.val.length + 1000 < Usize.max) :
    LeafResult f data env ctx index 0x0D#u8 bytes next (front ++ output) := by
  cases ht with
  | br_if _ _ args hi ht _ _ =>
    obtain ⟨view, ts, hl, hts, hlookup⟩ := hlabels.lookup depth hi
    have hargs : ts.map Translate.valueType = output := by simpa [proj_uN_0, proj_list_0, hlookup] using ht
    have hsize := henv.resolve_bound view ts hts
    obtain ⟨⟨_, s⟩, hrun, rfl, hc, hblocks, hp, rest, hv, hlen, hreal⟩ := WP.spec_imp_exists
      (code.branch.conditional_complete st data env depth next view ts
        f.core.outer f.core.operands front f.core.vals f.core.base_eq
        (by simp [f.blocks, f.core.ctrls, f.aligned])
        ⟨bytes, hb.suffix, hb.length, hb.bound, he⟩ hl hts (by omega)
        (by simpa [f.core.poly_eq, hargs] using hr))
    dsimp only at hc hblocks hp hv hlen hreal
    refine ⟨s, by simpa [step] using hrun, hp,
      ⟨f.core.output_of_same_ctrls hc hv (by simpa [hargs] using hreal), hblocks⟩, ?_⟩
    have hbytes := encoding_nonempty he
    simp only [hv, f.core.vals, List.length_append]
    omega

theorem Frame.return_ {st} (f : Frame st) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (C : context) (hmatch : EnvTranslation.Matches env ctx C)
    (hroot : resolve env (.Type index .Results) = some ctx.results.val)
    (next : Usize) (hb : Wasm1.BytesAt data st.core.pos [] next)
    (front input output : List valtype)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input))
    (ht : Instr_ok C .RETURN (.mk_functype (.mk_list input) (.mk_list output))) :
    LeafResult f data env ctx index 0x0F#u8 [] next (front ++ output) := by
  cases ht with
  | «return» _ before args after hreturn _ _ =>
    have hargs : ctx.results.val.map Translate.valueType = args := by
      simpa [hmatch.ret] using hreturn
    obtain ⟨s, hrun, hc, hblocks, hp, hv⟩ := returnStep.complete st env index ctx.results.val
      f.core.parents f.core.current f.core.outer f.core.operands (front ++ before)
      f.core.ctrls f.core.vals f.core.base hroot
      (by simpa [f.core.poly_eq, hargs, List.append_assoc] using hr)
    refine ⟨s, by simpa [step] using hrun, hp.trans hb.empty.symm,
      ⟨⟨true, [], hc, by simpa using hv, Sequence.realizes_polymorphic_empty _⟩, hblocks⟩, ?_⟩
    simp only [hv, f.core.vals, List.length_append]
    omega

theorem Frame.branch_table {st} (f : Frame st) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (C : context) (hlabels : Labels env st C)
    (depths : List U32) (default : U32) (count entries final : List U8) (next : Usize)
    (hcount : Leb128.Encoding count depths.length) (hentries : Wasm1.IndicesEncoding depths entries)
    (hdefault : Leb128.Encoding final default.val)
    (hb : Wasm1.BytesAt data st.core.pos (count ++ entries ++ final) next)
    (front input output : List valtype)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input))
    (ht : Instr_ok C (BrTable.instruction depths default) (.mk_functype (.mk_list input) (.mk_list output))) :
    LeafResult f data env ctx index 0x0E#u8 (count ++ entries ++ final) next (front ++ output) := by
  cases ht with
  | br_table _ _ _ before common after hbound hsub hdefaultbound hdefaultsub _ _ =>
    have htargets : ∀ d ∈ depths ++ [default], ∃ view ts,
        labelAt st d.val = some view ∧ resolve env view = some ts ∧
        Resulttype_sub (.mk_list common) (.mk_list (ts.map Translate.valueType)) := by
      intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · have hm : uN.mk_uN d.val ∈ depths.map (fun d => uN.mk_uN d.val) := List.mem_map.mpr ⟨d, hd, rfl⟩
        obtain ⟨view, ts, hl, hts, hlookup⟩ := hlabels.lookup d (hbound _ hm)
        exact ⟨view, ts, hl, hts, by simpa [proj_uN_0, hlookup] using hsub _ hm⟩
      · have he : d = default := by simpa using hd
        subst d
        obtain ⟨view, ts, hl, hts, hlookup⟩ := hlabels.lookup default hdefaultbound
        exact ⟨view, ts, hl, hts, by simpa [proj_uN_0, hlookup] using hdefaultsub⟩
    obtain ⟨s, hrun, hc, hblocks, hp, hv⟩ := code.branch_table.complete st data env
      f.core.parents f.core.current f.core.outer f.core.operands (front ++ before) common depths default next
      f.core.ctrls f.core.vals f.core.base
      (hb.br_table_decoded depths default hcount hentries hdefault) htargets
      (by simpa [f.core.poly_eq, List.append_assoc] using hr)
    refine ⟨s, by simpa [step] using hrun, hp,
      ⟨⟨true, [], hc, by simpa using hv, Sequence.realizes_polymorphic_empty _⟩, hblocks⟩, ?_⟩
    simp only [hv, f.core.vals, List.length_append]
    omega

/-- All multi-value control leaves satisfy the shared byte-weighted execution
contract directly from independent encodings and generated primitive rules. -/
theorem control_leaf (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (henv : EnvironmentWithinLimits env)
    (hroot : resolve env (.Type index .Results) = some ctx.results.val)
    (C : context) (st : code.BodyState) (f : Frame st) (opcode : U8)
    (op : instr) (bytes : List U8) (next : Usize) (front input output : List valtype)
    (hmatch : EnvTranslation.Matches env ctx C) (hlabels : Labels env st C)
    (hcap : st.core.vals.val.length + 1000 < Usize.max)
    (hi : ControlImmediate opcode op bytes) (hb : Wasm1.BytesAt data st.core.pos bytes next)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input))
    (ht : Instr_ok C op (.mk_functype (.mk_list input) (.mk_list output))) :
    LeafResult f data env ctx index opcode bytes next (front ++ output) := by
  cases hi with
  | br depth he => exact f.branch data env ctx index C hlabels depth _ next he hb front input output hr ht
  | brIf depth he => exact f.branch_if data env ctx index C hlabels henv depth _ next he hb front input output hr ht hcap
  | brTable depths default hc he hd =>
    exact f.branch_table data env ctx index C hlabels
      depths default _ _ _ next hc he hd hb front input output hr ht
  | return_ => exact f.return_ data env ctx index C hmatch hroot next hb front input output hr ht
  | call idx he => exact f.call data env ctx index C hmatch henv idx _ next he hb front input output hr ht hcap
  | callIndirect idx he => exact f.call_indirect data env ctx index C hmatch henv idx _ next he hb front input output hr ht hcap

/-- Reference immediates use ordinary generated typing together with the
independent declaration condition for ref.func. -/
theorem reference_leaf (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (henv : EnvironmentWithinLimits env)
    (C : context) (st : code.BodyState) (f : Frame st) (opcode : U8)
    (op : instr) (bytes : List U8) (next : Usize) (front input output : List valtype)
    (hmatch : EnvTranslation.Matches env ctx C)
    (hcap : st.core.vals.val.length + 1000 < Usize.max)
    (hi : ReferencesBinary.Immediate opcode op bytes) (hb : Wasm1.BytesAt data st.core.pos bytes next)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input))
    (ht : Instr_ok C op (.mk_functype (.mk_list input) (.mk_list output)))
    (hdecl : DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) op) :
    LeafResult f data env ctx index opcode bytes next (front ++ output) := by
  cases hi with
  | refNull rt =>
    cases ht with
    | ref_null =>
      obtain ⟨s, hs, hp, ho, hl⟩ := f.ref_null data env ctx index rt next front hb (by omega) (by simpa using hr)
      exact ⟨s, hs, hp, ho, by simp; omega⟩
  | refIsNull =>
    cases ht with
    | ref_is_null _ rt _ _ =>
      obtain ⟨s, hs, hp, ho, hl⟩ := f.ref_is_null data env ctx index rt next front hb (by omega) hr
      exact ⟨s, hs, hp, ho, by simp; omega⟩
  | refFunc idx he =>
    cases ht with
    | ref_func _ _ ft hbound hlookup _ _ =>
      have hidx : idx.val < env.func_types.val.length := by simpa [hmatch.funcs, proj_uN_0] using hbound
      obtain ⟨s, hs, hp, ho, hl⟩ := f.ref_func data env ctx index idx next front
        (hb.u32_decoded idx he) hidx hdecl (by omega) (by simpa using hr)
      exact ⟨s, hs, hp, ho, by omega⟩
  | selectTyped ty he =>
    cases ht with
    | select_expl =>
      obtain ⟨s, hs, hp, ho, hl⟩ := f.typed_select data env ctx index ty _ next front he hb (by omega) hr
      exact ⟨s, hs, hp, ho, by simp; omega⟩
  | tableGet idx he =>
    cases ht with
    | table_get _ _ rt lim hbound hlookup _ _ _ =>
      obtain ⟨hidx, hty⟩ := hmatch.table_reference idx lim rt hbound hlookup
      obtain ⟨s, hs, hp, ho, hl⟩ := f.table_get data env ctx index idx next front
        (hb.u32_decoded idx he) hidx (by omega)
        (by simpa [Simd.inputTypes, Translate.valueType] using hr)
      exact ⟨s, hs, hp, by simpa [Simd.outputTypes, hty] using ho, by omega⟩
  | tableSet idx he =>
    cases ht with
    | table_set _ _ rt lim hbound hlookup _ _ _ =>
      obtain ⟨hidx, hty⟩ := hmatch.table_reference idx lim rt hbound hlookup
      obtain ⟨s, hs, hp, ho, hl⟩ := f.table_set data env ctx index idx next front
        (hb.u32_decoded idx he) hidx (by omega)
        (by simpa [Simd.inputTypes, hty, show Translate.valueType .I32 = valtype.I32 from rfl] using hr)
      exact ⟨s, hs, hp, by simpa [Simd.outputTypes] using ho, by omega⟩
  | callIndirect idx table he hte =>
    exact f.call_indirect_indexed data env ctx index C hmatch henv idx table _ _ next he hte hb
      front input output hr ht hcap

private theorem reference_type_injective {a b : types.ElemType}
    (h : Translate.valueType (ModuleConstants.referenceValueType a) =
      Translate.valueType (ModuleConstants.referenceValueType b)) : a = b := by
  cases a <;> cases b <;> simp_all [ModuleConstants.referenceValueType, Translate.valueType]

/-- Bulk memory and table instructions are complete for the Core 2.0
reserved-byte grammar and the actual segment and table contexts. -/
theorem bulk_leaf (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (C : context) (st : code.BodyState) (f : Frame st) (subopcode : U32)
    (op : instr) (prefixBytes bytes : List U8) (next : Usize) (front input output : List valtype)
    (hmatch : EnvTranslation.Matches env ctx C)
    (hcap : st.core.vals.val.length + 1000 < Usize.max)
    (he : Leb128.Encoding prefixBytes subopcode.val)
    (hi : BulkBinary.Immediate subopcode op bytes)
    (hb : Wasm1.BytesAt data st.core.pos (prefixBytes ++ bytes) next)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input))
    (ht : Instr_ok C op (.mk_functype (.mk_list input) (.mk_list output))) :
    LeafResult f data env ctx index 252#u8 (prefixBytes ++ bytes) next (front ++ output) := by
  obtain ⟨middle, hprefixSpan, hpayload⟩ := hb.split
  have hprefix := hprefixSpan.u32_decoded subopcode he
  cases hi with
  | memoryInit idx hindex =>
    cases ht with
    | memory_init _ _ mt hmem hlookup hdata hdataLookup _ _ _ =>
      obtain ⟨count, hcount, hidx⟩ := hmatch.data_bound idx hdata
      obtain ⟨s, hs, hp, ho, hl⟩ := f.memory_init data env ctx index middle next front idx count _
        hindex hcount hidx hprefix hpayload (hmatch.memory_exists hmem) (by omega) hr
      exact ⟨s, hs, hp, by simpa using ho, by omega⟩
  | dataDrop idx hindex =>
    cases ht with
    | data_drop _ _ hdata hlookup _ _ =>
      obtain ⟨count, hcount, hidx⟩ := hmatch.data_bound idx hdata
      obtain ⟨s, hs, hp, ho, hl⟩ := f.data_drop data env ctx index idx middle next front count
        hcount hidx hprefix (hpayload.u32_decoded idx hindex) (by omega) (by simpa using hr)
      exact ⟨s, hs, hp, by simpa using ho, by omega⟩
  | memoryCopy =>
    cases ht with
    | memory_copy _ mt hmem hlookup _ _ _ =>
      obtain ⟨s, hs, hp, ho, hl⟩ := f.memory_copy data env ctx index middle next front hprefix
        hpayload (hmatch.memory_exists hmem) (by omega) hr
      exact ⟨s, hs, hp, by simpa using ho, by omega⟩
  | memoryFill =>
    cases ht with
    | memory_fill _ mt hmem hlookup _ _ _ =>
      obtain ⟨s, hs, hp, ho, hl⟩ := f.memory_fill data env ctx index middle next front hprefix
        hpayload (hmatch.memory_exists hmem) (by omega) hr
      exact ⟨s, hs, hp, by simpa using ho, by omega⟩
  | tableInit element table helement htable =>
    cases ht with
    | table_init _ _ _ lim rt htableBound htableLookup helementBound helementLookup _ _ _ =>
      obtain ⟨htb, htt⟩ := hmatch.table_reference table lim rt htableBound htableLookup
      obtain ⟨heb, het⟩ := hmatch.element_reference element rt helementBound helementLookup
      obtain ⟨s, hs, hp, ho, hl⟩ := f.table_init data env ctx index element table middle next front _ _
        helement htable hprefix hpayload heb htb (reference_type_injective (het.trans htt.symm)) (by omega) hr
      exact ⟨s, hs, hp, by simpa using ho, by omega⟩
  | elemDrop idx hindex =>
    cases ht with
    | elem_drop _ _ rt hbound hlookup _ _ =>
      obtain ⟨hidx, hty⟩ := hmatch.element_reference idx rt hbound hlookup
      obtain ⟨s, hs, hp, ho, hl⟩ := f.elem_drop data env ctx index idx middle next front hidx
        hprefix (hpayload.u32_decoded idx hindex) (by omega) (by simpa using hr)
      exact ⟨s, hs, hp, by simpa using ho, by omega⟩
  | tableCopy destination source hdestination hsource =>
    cases ht with
    | table_copy _ _ _ limD rt limS hd hdl hs hsl _ _ _ _ =>
      obtain ⟨hdb, hdt⟩ := hmatch.table_reference destination limD rt hd hdl
      obtain ⟨hsb, hst⟩ := hmatch.table_reference source limS rt hs hsl
      obtain ⟨s, hs, hp, ho, hl⟩ := f.table_copy data env ctx index destination source middle next front _ _
        hdestination hsource hprefix hpayload hdb hsb (reference_type_injective (hdt.trans hst.symm)) (by omega) hr
      exact ⟨s, hs, hp, by simpa using ho, by omega⟩
  | tableGrow idx hindex =>
    cases ht with
    | table_grow _ _ rt lim hbound hlookup _ _ _ =>
      obtain ⟨hidx, hty⟩ := hmatch.table_reference idx lim rt hbound hlookup
      obtain ⟨s, hs, hp, ho, hl⟩ := f.table_grow data env ctx index idx middle hprefix next front
        (hpayload.u32_decoded idx hindex) hidx (by omega)
        (by simpa [Simd.inputTypes, hty, show Translate.valueType .I32 = valtype.I32 from rfl] using hr)
      exact ⟨s, hs, hp, by simpa [Simd.outputTypes, Translate.valueType] using ho, by omega⟩
  | tableSize idx hindex =>
    cases ht with
    | table_size _ _ lim rt hbound hlookup _ _ _ =>
      obtain ⟨hidx, hty⟩ := hmatch.table_reference idx lim rt hbound hlookup
      obtain ⟨s, hs, hp, ho, hl⟩ := f.table_size data env ctx index idx middle hprefix next front
        (hpayload.u32_decoded idx hindex) hidx (by omega) (by simpa [Simd.inputTypes] using hr)
      exact ⟨s, hs, hp, by simpa [Simd.outputTypes, Translate.valueType] using ho, by omega⟩
  | tableFill idx hindex =>
    cases ht with
    | table_fill _ _ rt lim hbound hlookup _ _ _ =>
      obtain ⟨hidx, hty⟩ := hmatch.table_reference idx lim rt hbound hlookup
      obtain ⟨s, hs, hp, ho, hl⟩ := f.table_fill data env ctx index idx middle hprefix next front
        (hpayload.u32_decoded idx hindex) hidx (by omega)
        (by simpa [Simd.inputTypes, hty, show Translate.valueType .I32 = valtype.I32 from rfl] using hr)
      exact ⟨s, hs, hp, by simpa [Simd.outputTypes] using ho, by omega⟩

/-- Every plain instruction of the independent multi-value grammar has a
complete actual dispatch contract, including all shared scalar instructions. -/
theorem leaf_contract (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (henv : EnvironmentWithinLimits env)
    (hroot : resolve env (.Type index .Results) = some ctx.results.val) :
    LeafContract data env ctx index := by
  intro C st f opcode op bytes next front input output hmatch hlabels hcap hi hb hr ht hdecl
  cases hi with
  | plain hi =>
    rcases classify_plain hi with hscalar | hcontrol
    · exact scalar_leaf data env ctx index C st f opcode op bytes next front input output
        hmatch hcap hscalar hi hb hr ht
    · exact control_leaf data env ctx index henv hroot C st f opcode op bytes next front input output
        hmatch hlabels hcap hcontrol hb hr ht
  | reference hi =>
    exact reference_leaf data env ctx index henv C st f opcode op bytes next front input output
      hmatch hcap hi hb hr ht hdecl
  | signExtension opcode operation hmap =>
    obtain ⟨s, hs, hp, ho, hl⟩ := f.sign_extension data env ctx index opcode operation next C
      front input output hmap hb (by omega) ht hr
    exact ⟨s, hs, hp, ho, by simp; omega⟩
  | saturating subopcode operation hmap he =>
    obtain ⟨s, hs, hp, ho, hl⟩ := f.saturating data env ctx index subopcode operation _ next C
      front input output hmap he hb (by omega) ht hr
    exact ⟨s, hs, hp, ho, by omega⟩
  | bulk subopcode he hi =>
    exact bulk_leaf data env ctx index C st f subopcode op _ _ next front input output
      hmatch hcap he hi hb hr ht
  | simd subopcode he hi =>
    obtain ⟨s, hs, hp, ho, hl⟩ := f.simd data env ctx ctx index subopcode op _ _ next C
      front input output he hi hb hmatch (by omega) ht hr
    exact ⟨s, hs, hp, ho, by omega⟩

end Completeness
end Itasca.Wasm2
