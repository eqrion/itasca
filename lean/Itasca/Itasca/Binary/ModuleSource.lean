import WebAssembly.Binary.Map
import Itasca.Binary.InstructionSource
import Itasca.Results.Definitions.Validation

namespace Itasca.Binary.Source
open Aeneas.Std WebAssembly

private theorem vec {R : α → List U8 → Prop} {S : β → List UInt8 → Prop} {f : α → β}
    (step : ∀ {x bs}, R x bs → S (f x) (bytes bs)) {xs bs} (h : VecEncoding R xs bs) :
    WebAssembly.Binary.VecEncoding S (xs.map f) (bytes bs) :=
  WebAssembly.Binary.VecEncodingWith.map f sourceByte (fun h => (Leb128.encoding_iff _ _).mp h) @step h

private theorem nameEncoding {nm bs} (h : NameEncoding nm bs) :
    WebAssembly.Binary.NameEncoding (bytes nm) (bytes bs) := WebAssembly.Binary.NameEncodingWith.map sourceByte (fun h => (Leb128.encoding_iff _ _).mp h) h

private theorem index {i bs} (h : IndexEncoding i bs) :
    WebAssembly.Binary.IndexEncoding i.val (bytes bs) := (Leb128.encoding_iff _ _).mp h

theorem codeEncoding {e bs} (h : CodeEntry.CodeEncoding e bs) :
    WebAssembly.Binary.CodeEncoding (code e) (bytes bs) := by
  obtain ⟨sz, ls, body, hs, hl, ⟨ts, ht, hb⟩, rfl⟩ := h
  refine ⟨bytes sz, bytes ls, bytes body, ?_, vec (f := localDecl) (fun h => h) hl, ⟨_, WebAssembly.Binary.Rep.map token sourceByte @tokenEncoding ht,
    bodyTokens hb⟩, by simp [bytes]⟩
  simpa using (Leb128.encoding_iff _ _).mp hs

private theorem startEncoding {i bs} (h : StartEncoding i bs) :
    WebAssembly.Binary.StartEncoding (i.map UScalar.val) (bytes bs) := by
  obtain ⟨v, rfl, h⟩ := h
  exact ⟨_, rfl, index h⟩

private theorem sectionEncoding {R : α → List U8 → Prop} {S : β → List UInt8 → Prop} {f : α → β}
    (step : ∀ {x bs}, R x bs → S (f x) (bytes bs)) {id x bs} (h : SectionEncoding id R x bs) :
    WebAssembly.Binary.SectionEncoding (sourceByte id) S (f x) (bytes bs) := by
  obtain ⟨sz, payload, hs, hp, rfl⟩ := h
  exact ⟨bytes sz, _, by simpa using (Leb128.encoding_iff _ _).mp hs, step hp, by simp [bytes]⟩

private theorem customs {bs} (h : CustomsEncoding bs) : WebAssembly.Binary.CustomsEncoding (bytes bs) := by
  induction h with
  | nil => exact .nil
  | cons hc _ ih =>
    simp only [bytes, List.map_append]
    apply WebAssembly.Binary.CustomsEncodingWith.cons _ ih
    obtain ⟨nm, payload, en, hn, hs⟩ := hc
    refine ⟨bytes nm, bytes payload, bytes en, nameEncoding hn, ?_⟩
    obtain ⟨sz, _, hsz, rfl, rfl⟩ := hs
    exact ⟨bytes sz, _, by simpa using (Leb128.encoding_iff _ _).mp hsz, rfl, by simp [bytes, sourceByte, readerByte] <;> rfl⟩

private theorem padded {R : α → List U8 → Prop} {S : β → List UInt8 → Prop} {f : α → β}
    (step : ∀ {x bs}, R x bs → S (f x) (bytes bs)) {id absent x bs}
    (h : PaddedEncoding id R absent x bs) :
    WebAssembly.Binary.PaddedEncoding (sourceByte id) S (f absent) (f x) (bytes bs) := by
  obtain ⟨cs, sec, hc, hs, rfl⟩ := h
  refine ⟨_, bytes sec, customs hc, ?_, List.map_append⟩
  cases hs with
  | absent => exact .absent
  | present h => exact .present (sectionEncoding (f := f) @step h)

private theorem paddedVec (f : α → β) {R : α → List U8 → Prop} {S : β → List UInt8 → Prop}
    (step : ∀ {x bs}, R x bs → S (f x) (bytes bs)) {id xs bs}
    (h : PaddedEncoding id (VecEncoding R) [] xs bs) :
    WebAssembly.Binary.PaddedEncoding (sourceByte id) (WebAssembly.Binary.VecEncoding S) []
      (xs.map f) (bytes bs) :=
  padded (absent := []) (f := List.map f) (fun h => vec (f := f) @step h) h

theorem dataCountValid {m : Itasca.Binary.Module} :
    WebAssembly.Binary.DataCountValid (rawModule m) ↔ DataCountValid m := by
  cases h : m.dataCount <;>
    simp [WebAssembly.Binary.DataCountValid, DataCountValid, WebAssembly.Binary.DataCountValidWith,
      rawModule, code, h]

theorem moduleEncodingWith {R : Itasca.Binary.Code → List U8 → Prop}
    {S : WebAssembly.Binary.Code → List UInt8 → Prop}
    (entry : ∀ {e bs}, R e bs → S (code e) (bytes bs)) {m bs} (h : ModuleEncodingWith R m bs) :
    WebAssembly.Binary.ModuleEncodingWith S (rawModule m) (bytes bs) := by
  obtain ⟨ts, is, fs, tabs, ms, gs, es, st, els, dc, cs, ds, custom,
    ht, hi, hf, htab, hm, hg, he, hst, hel, hdc, hc, hd, hcustom, rfl, hv⟩ := h
  refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, _,
    paddedVec Translation.Environment.funcType (fun h => h) ht,
    paddedVec importEntry (fun h => h) hi, paddedVec UScalar.val @index hf, paddedVec Translation.Environment.tableType (fun h => h) htab,
    paddedVec Translation.Environment.memType (fun h => h) hm, paddedVec globalEntry (fun h => h) hg, paddedVec exportEntry (fun h => h) he,
    padded (f := Option.map UScalar.val) @startEncoding hst, paddedVec element (fun h => h) hel, padded (f := Option.map UScalar.val) @startEncoding hdc,
    paddedVec code @entry hc, paddedVec dataEntry (fun h => h) hd, customs hcustom, ?_, ?_⟩
  · simp [bytes, magicVersion, WebAssembly.Binary.magicVersion, sourceByte, readerByte] <;> rfl
  · exact dataCountValid.mpr hv

theorem moduleEncoding {m bs} (h : ModuleEncodingWith CodeEntry.CodeEncoding m bs) :
    WebAssembly.Binary.ModuleEncoding (rawModule m) (bytes bs) := moduleEncodingWith @codeEncoding h

theorem declared_length (e : Itasca.Binary.Code) : (code e).declared.length = e.declared.length := by
  obtain ⟨ls, ops⟩ := e
  induction ls with
  | nil => rfl
  | cons x xs ih =>
    simpa [WebAssembly.Binary.Code.declared, Itasca.Binary.Code.declared, code, localDecl] using ih

theorem codeWithinLimits {e bs} (h : CodeEntry.CodeEncodingWithinLimits e bs) :
    CodeWithinLimits (code e) (bytes bs) := by
  obtain ⟨hloc, sz, ls, body, hs, hl, ⟨⟨ts, ht, hb⟩, hsize⟩, rfl⟩ := h
  refine ⟨by rwa [declared_length], bytes sz, bytes ls, bytes body, ?_, vec (f := localDecl) (fun h => h) hl,
    ⟨⟨_, WebAssembly.Binary.Rep.map token sourceByte @tokenEncoding ht, bodyTokens hb⟩, by simpa using hsize⟩, by simp [bytes]⟩
  simpa using (Leb128.encoding_iff _ _).mp hs

end Itasca.Binary.Source
