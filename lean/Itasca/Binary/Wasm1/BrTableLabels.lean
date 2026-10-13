import Itasca.Binary.Wasm1.Encoding

open Aeneas Aeneas.Std

namespace Itasca.BrTable

/-- Consecutive unsigned immediates, specified independently of the validator. -/
inductive LabelsDecoded (data : Slice U8) (start : Usize) : List U32 → Usize → Prop where
  | nil : LabelsDecoded data start [] start
  | snoc {depths pos next depth} : LabelsDecoded data start depths pos →
      Leb128.Decoded data pos depth next → LabelsDecoded data start (depths ++ [depth]) next

theorem LabelsDecoded.span {data start depths next}
    (h : LabelsDecoded data start depths next) (hb : start.val ≤ data.length) :
    start.val ≤ next.val ∧ next.val ≤ data.length := by
  induction h with
  | nil => exact ⟨le_rfl, hb⟩
  | snoc h hd ih =>
    have hs := hd.span
    omega

/-- The table immediate contains a count, exactly that many labels, and a default. -/
def Decoded (data : Slice U8) (start : Usize) (depths : List U32)
    (default : U32) (next : Usize) : Prop :=
  ∃ count first last, Leb128.Decoded data start count first ∧
    depths.length = count.val ∧ LabelsDecoded data first depths last ∧
    Leb128.Decoded data last default next

theorem Decoded.span {data start depths default next}
    (h : Decoded data start depths default next) :
    start.val < next.val ∧ next.val ≤ data.length := by
  obtain ⟨count, first, last, hc, _, hlabels, hd⟩ := h
  have hc' := hc.span
  have hl' := hlabels.span hc'.2.2
  have hd' := hd.span
  omega

/-- Consecutive decoded labels have an independent concatenated byte encoding. -/
theorem LabelsDecoded.bytes {data start depths next}
    (h : LabelsDecoded data start depths next) (hb : start.val ≤ data.length) :
    ∃ bytes, Wasm1.IndicesEncoding depths bytes ∧ Wasm1.BytesAt data start bytes next := by
  induction h with
  | nil => exact ⟨[], .nil, .nil data start hb⟩
  | snoc _ hd ih =>
    obtain ⟨before, he, hs⟩ := ih
    obtain ⟨last, hlast, hlen, hbound, hencoding⟩ := hd
    exact ⟨before ++ last, he.snoc hencoding, hs.append ⟨hlast, hlen, hbound⟩⟩

end Itasca.BrTable

namespace Itasca.Wasm1

/-- A branch table's declared count, consecutive labels, and final default label
compose to the independent Wasm byte grammar. -/
theorem At.of_br_table {data start pos first last next} (count : U32)
    (depths : List U32) (default : U32)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = 0x0E#u8)
    (hpos : pos.val = start.val + 1) (hcount : Leb128.Decoded data pos count first)
    (hlen : depths.length = count.val) (hdepths : BrTable.LabelsDecoded data first depths last)
    (hdefault : Leb128.Decoded data last default next) :
    At data start (.plain (.BR_TABLE (depths.map (fun d => .mk_uN d.val)) (.mk_uN default.val))) next := by
  obtain ⟨countBytes, hc, hcl, hcb, hce⟩ := hcount
  obtain ⟨depthBytes, hde, hds⟩ := hdepths.bytes hcb
  obtain ⟨defaultBytes, hd, hdl, hdb, hde'⟩ := hdefault
  exact .of_immediate hstart hbyte hpos (.brTable depths default (by simpa [hlen] using hce) hde hde')
    (((show BytesAt data pos countBytes first from ⟨hc, hcl, hcb⟩).append hds).append ⟨hd, hdl, hdb⟩)

theorem At.of_table_decoded {data start pos next} (depths : List U32) (default : U32)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = 0x0E#u8)
    (hpos : pos.val = start.val + 1) (hdecoded : BrTable.Decoded data pos depths default next) :
    At data start (.plain (.BR_TABLE (depths.map (fun d => .mk_uN d.val)) (.mk_uN default.val))) next := by
  obtain ⟨count, first, last, hc, hl, hd, hf⟩ := hdecoded
  exact .of_br_table count depths default hstart hbyte hpos hc hl hd hf

end Itasca.Wasm1
