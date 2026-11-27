import Itasca.Binary.ReadBody
import Itasca.Binary.ModuleSource

namespace Itasca.Binary.Source
open Aeneas.Std WebAssembly

private theorem vec {R : α → List U8 → Prop} {S : β → List UInt8 → Prop} (f : α → β)
    (step : ∀ {y bs}, S y bs → ∃ x, f x = y ∧ R x (readerBytes bs))
    {ys bs} (h : WebAssembly.Binary.VecEncoding S ys bs) :
    ∃ xs, xs.map f = ys ∧ VecEncoding R xs (readerBytes bs) := by
  obtain ⟨cnt, entries, hc, he, rfl⟩ := h
  obtain ⟨xs, rfl, hx⟩ := readRep f @step he
  exact ⟨xs, rfl, _, _, by simpa using readerLeb hc, hx, List.map_append⟩

private theorem nameEncoding {nm bs} (h : WebAssembly.Binary.NameEncoding nm bs) :
    NameEncoding (readerBytes nm) (readerBytes bs) :=
  WebAssembly.Binary.NameEncodingWith.map readerByte (fun h => readerLeb h) h

private theorem value {t bs} (h : WebAssembly.Binary.ValueTypeEncoding t bs) :
    ∃ ty, Translation.valueType ty = t ∧ ValueTypeEncoding ty (readerBytes bs) := by
  obtain ⟨t, rfl, rfl⟩ := h
  exact ⟨readerType t, by simpa only [valueType_readerType] using (valueType_toSpec (readerType t)).symm,
    ValueTypeEncoding.reader_bytes.mpr (congrArg ([·]) (readerValueByte t))⟩

private theorem values {ts bs} (h : WebAssembly.Binary.VecEncoding WebAssembly.Binary.ValueTypeEncoding ts bs) :
    ∃ v : alloc.vec.Vec wasm_types.ValueType, v.val.map Translation.valueType = ts ∧
      VecEncoding ValueTypeEncoding v.val (readerBytes bs) := by
  obtain ⟨xs, rfl, hx⟩ := vec Translation.valueType @value h
  obtain ⟨_, _, hc, _⟩ := h
  have bound := (readerLeb hc).value_lt
  simp only [List.length_map] at bound
  have small : xs.length ≤ Usize.max := by scalar_tac
  exact ⟨alloc.vec.Vec.from xs small, by simp, by simpa using hx⟩

private theorem funcType {ty bs} (h : WebAssembly.Binary.FuncTypeEncoding ty bs) :
    ∃ t, Translation.Environment.funcType t = ty ∧ FuncTypeEncoding t (readerBytes bs) := by
  suffices ∃ t, Translation.Environment.funcType t = ty by
    obtain ⟨t, rfl⟩ := this
    exact ⟨t, rfl, by simpa only [FuncTypeEncoding, bytes_readerBytes] using h⟩
  obtain ⟨⟨ps⟩, ⟨rs⟩⟩ := ty
  obtain ⟨p, r, hp, hr, rfl⟩ := h
  obtain ⟨ps, rfl, ep⟩ := values hp
  obtain ⟨rs, rfl, er⟩ := values hr
  exact ⟨⟨ps, rs⟩, rfl⟩

private theorem limits {ty bs} (h : WebAssembly.Binary.LimitsEncoding ty bs) :
    ∃ t, Translation.Environment.limitsType t = ty := by
  cases h with
  | noMax _ hn =>
    obtain ⟨n, rfl, _⟩ := readerIndex hn
    exact ⟨⟨n, none⟩, rfl⟩
  | max _ _ hn hm =>
    obtain ⟨n, rfl, _⟩ := readerIndex hn
    obtain ⟨m, rfl, _⟩ := readerIndex hm
    exact ⟨⟨n, some m⟩, rfl⟩

private theorem tableType {ty bs} (h : WebAssembly.Binary.TableTypeEncoding ty bs) :
    ∃ t, Translation.Environment.tableType t = ty ∧ TableTypeEncoding t (readerBytes bs) := by
  obtain ⟨lim, rt⟩ := ty
  have h' := h
  obtain ⟨ls, hl, _⟩ := h'
  obtain ⟨l, rfl⟩ := limits hl
  cases rt <;> first
    | exact ⟨⟨l, .FuncRef⟩, rfl, by simpa only [TableTypeEncoding, Translation.Environment.tableType, Translation.referenceType, bytes_readerBytes] using h⟩
    | exact ⟨⟨l, .ExternRef⟩, rfl, by simpa only [TableTypeEncoding, Translation.Environment.tableType, Translation.referenceType, bytes_readerBytes] using h⟩

private theorem memType {ty bs} (h : WebAssembly.Binary.MemTypeEncoding ty bs) :
    ∃ t, Translation.Environment.memType t = ty ∧ MemTypeEncoding t (readerBytes bs) := by
  obtain ⟨lim⟩ := ty
  obtain ⟨l, rfl⟩ := limits h
  exact ⟨⟨l⟩, rfl, by simpa only [MemTypeEncoding, Translation.Environment.memType, bytes_readerBytes] using h⟩

private theorem globalType {ty bs} (h : WebAssembly.Binary.GlobalTypeEncoding ty bs) :
    ∃ t, Translation.globalType t = ty ∧ GlobalTypeEncoding t (readerBytes bs) := by
  suffices ∃ t, Translation.globalType t = ty by
    obtain ⟨t, rfl⟩ := this
    exact ⟨t, rfl, by simpa only [GlobalTypeEncoding, bytes_readerBytes] using h⟩
  obtain ⟨mutability, ty⟩ := ty
  obtain ⟨t, rfl, rfl⟩ := h
  cases mutability with
  | none => exact ⟨⟨.Const, readerType t⟩, by cases t <;> rfl⟩
  | some m => cases m; exact ⟨⟨.Var, readerType t⟩, by cases t <;> rfl⟩

private theorem localEncoding {e bs} (h : WebAssembly.Binary.LocalEncoding e bs) :
    ∃ x, localDecl x = e ∧ LocalEncoding x (readerBytes bs) := by
  obtain ⟨n, t⟩ := e
  obtain ⟨i, eq, _⟩ := readerIndex h.choose_spec.1
  have same : localDecl (i, readerType t) = (n, t) := by simp [localDecl, eq]
  exact ⟨_, same, by simpa only [LocalEncoding, same, bytes_readerBytes] using h⟩

theorem readCode {e bs} (h : WebAssembly.Binary.CodeEncoding e bs) :
    ∃ x, code x = e ∧ CodeEntry.CodeEncoding x (readerBytes bs) := by
  obtain ⟨ls, ops⟩ := e
  obtain ⟨sz, lsBytes, body, hs, hl, hb, rfl⟩ := h
  obtain ⟨locals, eq, he⟩ := vec localDecl @localEncoding hl
  exact ⟨⟨locals, ops⟩, by simp [code, eq], readerBytes sz, _, _, by simpa using readerLeb hs,
    he, readBody hb, by simp [readerBytes]⟩


private theorem importEncoding {e bs} (h : WebAssembly.Binary.ImportEncoding e bs) :
    ∃ x, importEntry x = e ∧ ImportEncoding x (readerBytes bs) := by
  suffices ∃ x, importEntry x = e by
    obtain ⟨x, rfl⟩ := this
    exact ⟨x, rfl, by simpa only [ImportEncoding, bytes_readerBytes] using h⟩
  obtain ⟨nm, field, d⟩ := e
  obtain ⟨mn, fnm, ds, hm, hf, hd, rfl⟩ := h
  have desc : ∃ x, importDesc x = d ∧ ImportDescEncoding x (readerBytes ds) := by
    suffices ∃ x, importDesc x = d by
      obtain ⟨x, rfl⟩ := this
      exact ⟨x, rfl, by simpa only [ImportDescEncoding, bytes_readerBytes] using hd⟩
    cases hd with
    | func _ h =>
      obtain ⟨x, rfl, _⟩ := readerIndex h
      exact ⟨.Func x, rfl⟩
    | table _ h =>
      obtain ⟨x, rfl, _⟩ := tableType h
      exact ⟨.Table x, rfl⟩
    | memory _ h =>
      obtain ⟨x, rfl, _⟩ := memType h
      exact ⟨.Memory x, rfl⟩
    | global _ h =>
      obtain ⟨x, rfl, _⟩ := globalType h
      exact ⟨.Global x, rfl⟩

  obtain ⟨x, rfl, hx⟩ := desc
  exact ⟨⟨readerBytes nm, readerBytes field, x⟩, by simp only [importEntry, bytes_readerBytes]⟩

private theorem exportEncoding {e bs} (h : WebAssembly.Binary.ExportEncoding e bs) :
    ∃ x, exportEntry x = e ∧ ExportEncoding x (readerBytes bs) := by
  suffices ∃ x, exportEntry x = e by
    obtain ⟨x, rfl⟩ := this
    exact ⟨x, rfl, by simpa only [ExportEncoding, bytes_readerBytes] using h⟩
  obtain ⟨nm, d⟩ := e
  obtain ⟨en, ds, hn, hd, rfl⟩ := h
  have desc : ∃ x, exportDesc x = d ∧ ExportDescEncoding x (readerBytes ds) := by
    suffices ∃ x, exportDesc x = d by
      obtain ⟨x, rfl⟩ := this
      exact ⟨x, rfl, by simpa only [ExportDescEncoding, bytes_readerBytes] using hd⟩
    cases hd with
    | func _ h =>
      obtain ⟨x, rfl, _⟩ := readerIndex h
      exact ⟨.Func x, rfl⟩
    | table _ h =>
      obtain ⟨x, rfl, _⟩ := readerIndex h
      exact ⟨.Table x, rfl⟩
    | memory _ h =>
      obtain ⟨x, rfl, _⟩ := readerIndex h
      exact ⟨.Memory x, rfl⟩
    | global _ h =>
      obtain ⟨x, rfl, _⟩ := readerIndex h
      exact ⟨.Global x, rfl⟩

  obtain ⟨x, rfl, hx⟩ := desc
  exact ⟨⟨readerBytes nm, x⟩, by simp only [exportEntry, bytes_readerBytes]⟩

private theorem globalEncoding {e bs} (h : WebAssembly.Binary.GlobalEncoding e bs) :
    ∃ x, globalEntry x = e ∧ GlobalEncoding x (readerBytes bs) := by
  suffices ∃ x, globalEntry x = e by
    obtain ⟨x, rfl⟩ := this
    exact ⟨x, rfl, by simpa only [GlobalEncoding, bytes_readerBytes] using h⟩
  obtain ⟨t, c⟩ := e
  obtain ⟨ts, cs, ht, hc, rfl⟩ := h
  obtain ⟨t, rfl, et⟩ := globalType ht
  obtain ⟨c, rfl, ec⟩ := readConstant hc
  exact ⟨⟨t, c⟩, rfl⟩

private theorem elementEncoding {e bs} (h : WebAssembly.Binary.ElementEncoding e bs) :
    ∃ x, element x = e ∧ ElementEncoding x (readerBytes bs) := by
  suffices ∃ x, element x = e by
    obtain ⟨x, rfl⟩ := this
    exact ⟨x, rfl, by simpa only [ElementEncoding, bytes_readerBytes] using h⟩
  obtain ⟨t, m, xs⟩ := e
  obtain ⟨ex, header, init, hh, hi, _⟩ := h
  have initValue {v raw} (hv : WebAssembly.Binary.InitializerEncoding ex v raw) :
      ∃ c, constant c = v ∧ True := by
    cases ex with
    | true => obtain ⟨c, rfl, _⟩ := readConstant hv; exact ⟨c, rfl, trivial⟩
    | false =>
      obtain ⟨n, rfl, hn⟩ := hv
      obtain ⟨i, rfl, _⟩ := readerIndex hn
      exact ⟨.RefFunc i, rfl, trivial⟩
  obtain ⟨_, _, _, hr, _⟩ := hi
  obtain ⟨values, eq, _⟩ := readRep (R := fun _ _ => True) constant @initValue hr
  have modeValue : ∃ mode, elementMode mode = m := by
    cases hh with
    | activeIndices _ ho | activeExpressions _ ho =>
      obtain ⟨c, rfl, _⟩ := readConstant ho
      exact ⟨.Active 0#u32 c, rfl⟩
    | explicitIndices _ hn ho | explicitExpressions _ hn ho =>
      obtain ⟨i, rfl, _⟩ := readerIndex hn
      obtain ⟨c, rfl, _⟩ := readConstant ho
      exact ⟨.Active i c, rfl⟩
    | passiveIndices _ | passiveExpressions _ => exact ⟨.Passive, rfl⟩
    | declarativeIndices _ | declarativeExpressions _ => exact ⟨.Declarative, rfl⟩
  obtain ⟨mode, rfl⟩ := modeValue
  exact ⟨⟨readerRef t, mode, values⟩, by simp [element, eq]⟩

private theorem activeIndex {n ex bs} (h : WebAssembly.Binary.ActiveIndexEncoding n ex bs) :
    ∃ i : U32, i.val = n := by
  cases h with
  | implicit => exact ⟨0#u32, rfl⟩
  | explicit _ hi => obtain ⟨i, rfl, _⟩ := readerIndex hi; exact ⟨i, rfl⟩

private theorem dataEncoding {e bs} (h : WebAssembly.Binary.DataEncoding e bs) :
    ∃ x, dataEntry x = e ∧ DataEncoding x (readerBytes bs) := by
  suffices ∃ x, dataEntry x = e by
    obtain ⟨x, rfl⟩ := this
    exact ⟨x, rfl, by simpa only [DataEncoding, bytes_readerBytes] using h⟩
  cases h with
  | @active _ _ init _ _ _ _ hf ho _ =>
    obtain ⟨i, rfl⟩ := activeIndex hf
    obtain ⟨o, rfl, _⟩ := readConstant ho
    exact ⟨⟨.Active i o, readerBytes init⟩, by simp only [dataEntry, dataMode, bytes_readerBytes]⟩
  | @passive init _ _ _ _ =>
    exact ⟨⟨.Passive, readerBytes init⟩, by simp only [dataEntry, dataMode, bytes_readerBytes]⟩

private theorem startEncoding {v bs} (h : WebAssembly.Binary.StartEncoding v bs) :
    ∃ x, x.map UScalar.val = v ∧ StartEncoding x (readerBytes bs) := by
  obtain ⟨v, rfl, hi⟩ := h
  obtain ⟨i, rfl, ei⟩ := readerIndex hi
  exact ⟨some i, rfl, _, rfl, ei⟩

private theorem customs {bs} (h : WebAssembly.Binary.CustomsEncoding bs) :
    CustomsEncoding (readerBytes bs) := by
  induction h with
  | nil => exact .nil
  | cons hc _ ih =>
    simp only [readerBytes, List.map_append]
    apply WebAssembly.Binary.CustomsEncodingWith.cons _ ih
    obtain ⟨nm, payload, en, hn, sz, _, hs, rfl, rfl⟩ := hc
    refine ⟨_, readerBytes payload, _, nameEncoding hn, readerBytes sz, _, ?_, rfl, ?_⟩
    · simpa using readerLeb hs
    · simp [readerBytes, readerByte] <;> rfl

private theorem padded {R : α → List U8 → Prop} {S : β → List UInt8 → Prop} (f : α → β)
    (step : ∀ {y bs}, S y bs → ∃ x, f x = y ∧ R x (readerBytes bs))
    {tag : UInt8} {absent y bs} (h : WebAssembly.Binary.PaddedEncoding tag S (f absent) y bs) :
    ∃ x, f x = y ∧ PaddedEncoding (readerByte tag) R absent x (readerBytes bs) := by
  obtain ⟨cs, sec, hcs, he, rfl⟩ := h
  cases he with
  | absent => exact ⟨absent, rfl, _, _, customs hcs, .absent, List.map_append⟩
  | present h =>
    obtain ⟨sz, payload, hs, hp, rfl⟩ := h
    obtain ⟨x, rfl, hx⟩ := step hp
    refine ⟨x, rfl, _, _, customs hcs, .present ⟨readerBytes sz, _, ?_, hx, ?_⟩, List.map_append⟩
    · simpa using readerLeb hs
    · simp only [readerBytes, List.map_cons, List.map_append]

private theorem paddedVec {tag : UInt8} (f : α → β) {R : α → List U8 → Prop} {S : β → List UInt8 → Prop}
    (step : ∀ {y bs}, S y bs → ∃ x, f x = y ∧ R x (readerBytes bs)) {ys bs}
    (h : WebAssembly.Binary.PaddedEncoding tag (WebAssembly.Binary.VecEncoding S) [] ys bs) :
    ∃ xs, xs.map f = ys ∧ PaddedEncoding (readerByte tag) (VecEncoding R) [] xs (readerBytes bs) :=
  padded (absent := []) (List.map f) (fun h => vec f @step h) h

theorem readModuleWith {R : Itasca.Binary.Code → List U8 → Prop}
    {S : WebAssembly.Binary.Code → List UInt8 → Prop}
    (entry : ∀ {e bs}, S e bs → ∃ x, code x = e ∧ R x (readerBytes bs))
    {m bs} (h : WebAssembly.Binary.ModuleEncodingWith S m bs) :
    ∃ x, rawModule x = m ∧ ModuleEncodingWith R x (readerBytes bs) := by
  obtain ⟨ts, is, fs, tabs, ms, gs, es, st, els, dc, cs, ds⟩ := m
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ht, hi, hf, htab, hm, hg, he, hst, hel,
    hdc, hc, hd, hcustom, rfl, hv⟩ := h
  obtain ⟨ts, eqts, ets⟩ := paddedVec Translation.Environment.funcType @funcType ht
  obtain ⟨is, eqis, eis⟩ := paddedVec importEntry @importEncoding hi
  obtain ⟨fs, eqfs, efs⟩ := paddedVec UScalar.val (R := IndexEncoding) (S := WebAssembly.Binary.IndexEncoding) (fun h => readerIndex h) hf
  obtain ⟨tabs, eqtabs, etabs⟩ := paddedVec Translation.Environment.tableType @tableType htab
  obtain ⟨ms, eqms, ems⟩ := paddedVec Translation.Environment.memType @memType hm
  obtain ⟨gs, eqgs, egs⟩ := paddedVec globalEntry @globalEncoding hg
  obtain ⟨es, eqes, ees⟩ := paddedVec exportEntry @exportEncoding he
  obtain ⟨st, eqst, est⟩ := padded (absent := none) (Option.map UScalar.val) @startEncoding hst
  obtain ⟨els, eqels, eels⟩ := paddedVec element @elementEncoding hel
  obtain ⟨dc, eqdc, edc⟩ := padded (absent := none) (Option.map UScalar.val) @startEncoding hdc
  obtain ⟨cs, eqcs, ecs⟩ := paddedVec code @entry hc
  obtain ⟨ds, eqds, eds⟩ := paddedVec dataEntry @dataEncoding hd

  let raw : Itasca.Binary.Module := ⟨ts, is, fs, tabs, ms, gs, es, st, els, dc, cs, ds⟩
  dsimp only at eqts eqis eqfs eqtabs eqms eqgs eqes eqst eqels eqdc eqcs eqds
  subst_vars
  refine ⟨raw, rfl, _, _, _, _, _, _, _, _, _, _, _, _, _, ets, eis, efs, etabs, ems,
    egs, ees, est, eels, edc, ecs, eds, customs hcustom, ?_, ?_⟩
  · simp only [readerBytes, List.map_append]
    rfl
  · cases dc with
    | none => simpa [WebAssembly.Binary.DataCountValid, WebAssembly.Binary.DataCountValidWith, DataCountValid, raw, code] using hv
    | some n => simpa [WebAssembly.Binary.DataCountValid, WebAssembly.Binary.DataCountValidWith, DataCountValid, raw] using hv

theorem readModule {m bs} (h : WebAssembly.Binary.ModuleEncoding m bs) :
    ∃ x, rawModule x = m ∧ ModuleEncodingWith CodeEntry.CodeEncoding x (readerBytes bs) :=
  readModuleWith @readCode h

theorem readCodeWithinLimits {e bs} (h : CodeWithinLimits e bs) :
    ∃ x, code x = e ∧ CodeEntry.CodeEncodingWithinLimits x (readerBytes bs) := by
  obtain ⟨ls, ops⟩ := e
  obtain ⟨hcap, sz, lsBytes, body, hs, hl, ⟨hb, cap⟩, rfl⟩ := h
  obtain ⟨locals, eq, he⟩ := vec localDecl @localEncoding hl
  let x : Itasca.Binary.Code := ⟨locals, ops⟩
  have source : code x = ⟨ls, ops⟩ := by simp [x, code, eq]
  exact ⟨x, source, by rwa [← declared_length, source], readerBytes sz, _, _,
    by simpa using readerLeb hs, he, ⟨readBody hb, by simpa using cap⟩, by simp [readerBytes]⟩


/-- Transfer a section span for an already known value, including custom sections
and an omitted field's default value. -/
private theorem knownPadded {R : α → List U8 → Prop} {S : β → List UInt8 → Prop}
    (f : α → β) {absent x} (empty : f x = f absent → x = absent)
    (step : ∀ {bs}, S (f x) bs → R x (readerBytes bs)) {tag bs}
    (h : WebAssembly.Binary.PaddedEncoding tag S (f absent) (f x) bs) :
    PaddedEncoding (readerByte tag) R absent x (readerBytes bs) := by
  obtain ⟨cs, sec, hc, hs, rfl⟩ := h
  refine ⟨_, _, customs hc, ?_, List.map_append⟩
  generalize eq : f x = value at hs
  cases hs with
  | absent => obtain rfl := empty eq; exact .absent
  | present hp =>
    obtain ⟨sz, payload, hn, hv, rfl⟩ := hp
    exact .present ⟨readerBytes sz, readerBytes payload, by simpa using readerLeb hn,
      step (eq.symm ▸ hv), by simp only [readerBytes, List.map_cons, List.map_append]⟩

private theorem knownVec {R : α → List U8 → Prop} {S : β → List UInt8 → Prop}
    (f : α → β) (step : ∀ {x bs}, S (f x) bs → R x (readerBytes bs)) {xs tag bs}
    (h : WebAssembly.Binary.PaddedEncoding tag (WebAssembly.Binary.VecEncoding S) [] (xs.map f) bs) :
    PaddedEncoding (readerByte tag) (VecEncoding R) [] xs (readerBytes bs) :=
  knownPadded (List.map f) (by simp) (fun h =>
    WebAssembly.Binary.VecEncodingWith.unmapValues f readerByte @readerLeb @step h) h

private theorem knownStart {x : Option U32} {tag bs}
    (h : WebAssembly.Binary.PaddedEncoding tag WebAssembly.Binary.StartEncoding none (x.map UScalar.val) bs) :
    PaddedEncoding (readerByte tag) StartEncoding none x (readerBytes bs) := by
  apply knownPadded (Option.map UScalar.val) (by cases x <;> simp) _ h
  rintro bs ⟨i, hi, he⟩
  cases x with
  | none => cases hi
  | some x => obtain rfl := Option.some.inj hi; exact ⟨x, rfl, readerLeb he⟩

/-- Recover the exact section and bounded body spans of a module whose extracted
values are already known. Local groups and the bound use the same body witness. -/
theorem limitedReaderSpans {m bs} (h : WebAssembly.Binary.ModuleEncodingWith CodeWithinLimits
    (rawModule m) bs) : ModuleEncodingWith CodeEntry.CodeEncodingWithinLimits m (readerBytes bs) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ht, hi, hf, htab, hm, hg, he, hst, hel,
    hdc, hc, hd, hcustom, rfl, hv⟩ := h
  refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, _,
    knownVec Translation.Environment.funcType ?_ ht, knownVec importEntry ?_ hi,
    knownVec UScalar.val (fun h => readerLeb h) hf, knownVec Translation.Environment.tableType ?_ htab,
    knownVec Translation.Environment.memType ?_ hm, knownVec globalEntry ?_ hg, knownVec exportEntry ?_ he,
    knownStart hst, knownVec element ?_ hel, knownStart hdc, knownVec code ?_ hc, knownVec dataEntry ?_ hd,
    customs hcustom, by simp only [readerBytes, List.map_append]; rfl, dataCountValid.mp hv⟩
  all_goals intro x bs hx
  all_goals first
    | simpa only [FuncTypeEncoding, ImportEncoding, TableTypeEncoding, MemTypeEncoding, GlobalEncoding,
        ExportEncoding, ElementEncoding, DataEncoding, bytes_readerBytes] using hx
    | skip
  obtain ⟨hcap, sz, ls, body, hs, hl, ⟨hb, cap⟩, rfl⟩ := hx
  exact ⟨by rwa [← declared_length], readerBytes sz, readerBytes ls, readerBytes body,
    by simpa using readerLeb hs,
    WebAssembly.Binary.VecEncodingWith.unmapValues localDecl readerByte @readerLeb
      (fun h => by simpa only [LocalEncoding, bytes_readerBytes] using h) hl,
    ⟨readBody hb, by simpa using cap⟩, by simp [readerBytes]⟩

end Itasca.Binary.Source
