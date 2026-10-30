import Itasca.Stream.Header

/-!
# Code section header completeness

`stream.read_code_header.complete`: an independently described code section header
(`StreamFraming.HeaderAt`) over an available source is accepted. Only the bounded header view of at
most 11 bytes is read.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- A code region with a valid header (`StreamFraming.HeaderAt`) is accepted by
`stream.read_code_header` over an available source. Only a view of at most 11 bytes is read, and
nonminimal LEB128 prefixes are accepted. An absent region and a present zero-entry section are
separate cases. -/
theorem stream.read_code_header.complete {S : Type} (source : stream.Source S) (state : S)
    (codeLen : Usize) (env : metadata.Env) (entries : Usize) (data : Slice U8)
    (environment tail : List U8)
    (havailable : StreamSource.Available source state environment data.val tail)
    (hsize : codeLen.val = data.length)
    (hbound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (hheader : StreamFraming.HeaderAt data env entries) :
    stream.read_code_header source state codeLen env = .ok (.Ok entries) := by
  rcases hheader with ⟨hempty, rfl, hfuncs⟩ | ⟨count, hsection, hentries⟩
  · have hzero : codeLen = 0#usize := by
      apply UScalar.eq_of_val_eq
      simpa [Slice.length, hempty] using hsize
    simp [stream.read_code_header, hzero, alloc.vec.Vec.is_empty, hfuncs]
  · obtain ⟨content, hsection, hcount, hcountval⟩ := hsection
    obtain ⟨pos, size, hbyte, hsizeDecoded, hend, _⟩ := hsection
    change Leb128.Decoded data content count entries at hcount
    change count.val = env.func_type_indices.val.length at hcountval
    change data.length = content.val + size.val at hend
    have hpos : pos = 1#usize := by
      have hp := hbyte.byte.length
      apply UScalar.eq_of_val_eq
      simpa using hp
    subst pos
    have hsizeSpan : 1 < content.val ∧ content.val ≤ 6 ∧ content.val ≤ data.length := by
      simpa using hsizeDecoded.span
    have hcountSpan := hcount.span
    have hnonzero : codeLen ≠ 0#usize := by
      intro he
      have := hbyte.byte.bound
      scalar_tac
    let viewEnd := core.cmp.impls.OrdUsize.min codeLen 11#usize
    have hviewEnd : viewEnd.val = Nat.min data.length 11 := by
      simp [viewEnd, hsize]
    have hviewbound : viewEnd.val ≤ data.length := by rw [hviewEnd]; exact Nat.min_le_left _ _
    have hsizeWithin : content.val ≤ viewEnd.val := by rw [hviewEnd]; apply Nat.le_min.mpr; constructor <;> omega
    have hcountWithin : entries.val ≤ viewEnd.val := by rw [hviewEnd]; apply Nat.le_min.mpr; constructor <;> omega
    have hbyteWithin : (1#usize).val ≤ viewEnd.val := by scalar_tac
    obtain ⟨header, hread, hview⟩ := havailable.code_read 0#usize viewEnd (by simp) hviewbound
    have hlen : header.length = viewEnd.val - (0#usize).val := by
      change header.val.length = _
      rw [hview, List.slice_length]
      simpa using Nat.min_eq_right hviewbound
    have hexact := stream.read_exact.complete source state 0#usize viewEnd header
      (by simp) hread hlen
    have hsizeHeader : Leb128.Decoded header 1#usize size content :=
      hsizeDecoded.to_slice_view (by simp) hviewbound hview (by simp) (by simp) hsizeWithin
    have hcountHeader : Leb128.Decoded header content count entries :=
      hcount.to_slice_view (by simp) hviewbound hview (by simp) (by simp) hcountWithin
    have hbyteHeader := (Wasm1.BytesAt.of_slice_view (by simp) hviewbound hview).restrict
      hbyte.byte (pos := 0#usize) (next := 1#usize) (by simp) (by simp) hbyteWithin
    have hpositive : (0#usize).val < header.length := by have := hbyteHeader.bound; scalar_tac
    have hindex : Slice.index_usize header 0#usize = .ok 10#u8 := by
      have hs := hbyteHeader.suffix
      rw [List.drop_eq_getElem_cons hpositive] at hs
      have hhead := (List.cons.inj hs).1
      obtain ⟨id, hi, hival⟩ := WP.spec_imp_exists (Slice.index_usize_spec header 0#usize hpositive)
      have hid : id = 10#u8 := hival.trans hhead
      exact hid ▸ hi
    obtain ⟨len, hlenread, hlenval⟩ := stream.read_len.complete header 1#usize content size hsizeHeader
    obtain ⟨countLen, hcountread, hcountlen⟩ := stream.read_len.complete header content entries count hcountHeader
    have hcap : content.val + len.val ≤ limits.MAX_MODULE_BYTES.val := by
      omega
    obtain ⟨finish, hfinish, hfinishval⟩ := limits.add_offset.complete content len hcap
    have hfinishEq : finish = codeLen := by
      apply UScalar.eq_of_val_eq
      omega
    have hcountEq : countLen = alloc.vec.Vec.len env.func_type_indices := by
      apply UScalar.eq_of_val_eq
      exact hcountlen.trans hcountval
    have hnotOver : entries.val ≤ codeLen.val := by omega
    simp only [viewEnd] at hexact
    simp [stream.read_code_header, hnonzero, StreamFraming.header_limit, lift,
      hexact, core.result.Result.Insts.CoreOpsTry.branch, hindex, metadata.SECTION_CODE,
      hlenread, hfinish, hfinishEq, hcountread, hnotOver, hcountEq]

end Itasca
