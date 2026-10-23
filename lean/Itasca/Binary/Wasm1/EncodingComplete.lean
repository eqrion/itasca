import Itasca.Binary.Wasm1.BrTableLabels

/-!
# Reading Wasm 1.0 encodings

Splitting lemmas for `BytesAt`, `Consumed` and `BrTable.LabelsDecoded`, and lemmas that turn a
`BytesAt` span into a successful run of the extracted readers (`reader.read_u32_leb`,
`code.read_op`, `code.take_index`, `code.read_memarg`, ...).
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm1

/-- A byte interval splits at any boundary of its bytes. -/
theorem BytesAt.split {data start next first rest}
    (h : BytesAt data start (first ++ rest) next) :
    ∃ middle, BytesAt data start first middle ∧ BytesAt data middle rest next := by
  have hlen := h.length
  simp only [List.length_append] at hlen
  let middle : Usize := Usize.ofNatCore (start.val + first.length)
    (by have := next.hmax; omega)
  have hm : middle.val = start.val + first.length := by simp [middle]
  have ht : data.val.drop middle.val = rest ++ data.val.drop next.val := by
    have hh := congrArg (List.drop first.length) h.suffix
    simpa [hm, List.drop_drop, List.drop_append, Nat.add_comm] using hh
  refine ⟨middle, ⟨?_, hm, by have := h.bound; omega⟩, ⟨ht, by omega, h.bound⟩⟩
  simpa [ht, List.append_assoc] using h.suffix

/-- An empty byte list occupies no input. -/
theorem BytesAt.empty {data start next} (h : BytesAt data start [] next) : next = start := by
  apply UScalar.eq_of_val_eq
  simpa using h.length

/-- A one-byte interval is the byte at the cursor. -/
theorem BytesAt.single {data start next byte} (h : BytesAt data start [byte] next) :
    ∃ hp : start.val < data.length, data.val[start.val] = byte ∧ next.val = start.val + 1 := by
  have hn : next.val = start.val + 1 := by simpa using h.length
  have hp : start.val < data.length := by have := h.bound; omega
  have hs := h.suffix
  rw [List.drop_eq_getElem_cons hp] at hs
  exact ⟨hp, (List.cons.inj hs).1, hn⟩

/-- `reader.read_byte` returns the byte of a one-byte interval. -/
theorem BytesAt.read_byte {data start next byte} (h : BytesAt data start [byte] next) :
    reader.read_byte data start = .ok (.Ok (byte, next)) := by
  obtain ⟨hp, hb, hn⟩ := h.single
  obtain ⟨_, hr, p, rfl, hp'⟩ := WP.spec_imp_exists (reader.read_byte.spec data start hp)
  have heq : p = next := UScalar.eq_of_val_eq (hp'.trans hn.symm)
  simpa [hb, heq] using hr

/-- A span with a `Leb128.Encoding` is a `Leb128.Decoded` span. -/
theorem BytesAt.u32_decoded {data start next bytes} (value : U32)
    (h : BytesAt data start bytes next) (he : Leb128.Encoding bytes value.val) :
    Leb128.Decoded data start value next := ⟨bytes, h.suffix, h.length, h.bound, he⟩

/-- `reader.read_u32_leb` reads an unsigned LEB128 span. -/
theorem BytesAt.read_u32 {data start next bytes} (value : U32)
    (h : BytesAt data start bytes next) (he : Leb128.Encoding bytes value.val) :
    reader.read_u32_leb data start = .ok (.Ok (value, next)) :=
  reader.read_u32_leb.complete data start value next (h.u32_decoded value he)

/-- `reader.read_f64_bits` reads an eight-byte span. -/
theorem BytesAt.read_f64 {data start next bytes} (bits : U64)
    (h : BytesAt data start bytes next) (he : FloatBits.Encoding 8 bytes bits.val) :
    reader.read_f64_bits data start = .ok (.Ok (bits, next)) :=
  reader.read_f64_bits.complete data start bits next
    ⟨bytes, h.suffix, by simpa [he.1] using h.length, h.bound, he⟩

/-- `code.take_index` reads an index span. -/
theorem BytesAt.take_index {data next bytes} (st : code.OpIterState) (idx : U32)
    (h : BytesAt data st.pos bytes next) (he : Leb128.Encoding bytes idx.val) :
    code.take_index st data = .ok (.Ok idx, { st with pos := next }) := by
  simp [code.take_index, h.read_u32 idx he, core.result.Result.Insts.CoreOpsTry.branch]

/-- `code.read_memarg` reads an alignment span followed by an offset span. -/
theorem BytesAt.read_memarg {data next alignment offset} (st : code.OpIterState)
    (arg : code.MemArg) (h : BytesAt data st.pos (alignment ++ offset) next)
    (ha : Leb128.Encoding alignment arg.align.val) (ho : Leb128.Encoding offset arg.offset.val) :
    code.read_memarg st data = .ok (.Ok arg, { st with pos := next }) := by
  obtain ⟨middle, hfirst, hrest⟩ := h.split
  have hr := hfirst.read_u32 arg.align ha
  have hr' := hrest.read_u32 arg.offset ho
  cases arg
  simp_all [code.read_memarg, core.result.Result.Insts.CoreOpsTry.branch]

end Itasca.Wasm1

namespace Itasca.BrTable

/-- Label runs compose. -/
theorem LabelsDecoded.append {data start middle next first rest}
    (hfirst : LabelsDecoded data start first middle)
    (hrest : LabelsDecoded data middle rest next) :
    LabelsDecoded data start (first ++ rest) next := by
  induction hrest with
  | nil => simpa using hfirst
  | snoc _ hd ih => simpa [List.append_assoc] using LabelsDecoded.snoc ih hd

private theorem labels_split {data start depths next} (h : LabelsDecoded data start depths next)
    (first rest : List U32) (heq : depths = first ++ rest) :
    ∃ middle, LabelsDecoded data start first middle ∧ LabelsDecoded data middle rest next := by
  induction h generalizing first rest with
  | nil =>
      have he : first = [] ∧ rest = [] := by simpa using heq.symm
      rcases he with ⟨rfl, rfl⟩
      exact ⟨start, .nil, .nil⟩
  | @snoc depths pos next depth hprefix hlast ih =>
      cases rest using List.reverseRecOn with
      | nil =>
          have hf : first = depths ++ [depth] := by simpa using heq.symm
          subst first
          exact ⟨next, .snoc hprefix hlast, .nil⟩
      | append_singleton rest last =>
          have heq' : depths ++ [depth] = (first ++ rest) ++ [last] := by
            simpa [List.append_assoc] using heq
          have ht : depth = last := by
            have := congrArg List.getLast? heq'
            simpa using this
          subst last
          obtain ⟨middle, hf, hr⟩ := ih first rest (List.append_cancel_right heq')
          exact ⟨middle, hf, .snoc hr hlast⟩

private theorem labels_empty {data start depths next}
    (h : LabelsDecoded data start depths next) (he : depths = []) : next = start := by
  cases h with
  | nil => rfl
  | snoc => simp at he

private theorem labels_single {data start next depth}
    (h : LabelsDecoded data start [depth] next) : Leb128.Decoded data start depth next := by
  generalize he : [depth] = depths at h
  cases h with
  | nil => simp at he
  | @snoc depths pos next last hp hl =>
      have hlen := congrArg List.length he
      simp only [List.length_cons, List.length_nil, List.length_append] at hlen
      have ht : depths = [] := List.length_eq_zero_iff.mp (by omega)
      have heq : last = depth := by simpa [ht] using he.symm
      have hpos := labels_empty hp ht
      simpa [heq, hpos] using hl

/-- A nonempty label run is its first label followed by the rest. -/
theorem LabelsDecoded.cons_iff {data start next depth depths} :
    LabelsDecoded data start (depth :: depths) next ↔
      ∃ middle, Leb128.Decoded data start depth middle ∧ LabelsDecoded data middle depths next := by
  constructor
  · intro h
    obtain ⟨middle, hh, ht⟩ := labels_split h [depth] depths rfl
    exact ⟨middle, labels_single hh, ht⟩
  · rintro ⟨middle, hh, ht⟩
    exact LabelsDecoded.append (.snoc .nil hh) ht

end Itasca.BrTable

namespace Itasca.Wasm1

/-- An `IndicesEncoding` over a byte span gives a run of decoded labels. -/
theorem IndicesEncoding.decoded {indices bytes} (he : IndicesEncoding indices bytes)
    {data start next} (h : BytesAt data start bytes next) :
    BrTable.LabelsDecoded data start indices next := by
  induction he generalizing start with
  | nil => have hn := h.empty; subst next; exact .nil
  | cons hidx _ ih =>
      obtain ⟨middle, hfirst, hrest⟩ := h.split
      have hhead := BrTable.LabelsDecoded.snoc .nil (hfirst.u32_decoded _ hidx)
      simpa using hhead.append (ih hrest)

/-- The count, entries and default label of a `br_table` immediate give a `BrTable.Decoded`. The
count's `u32` range follows from its own encoding. -/
theorem BytesAt.br_table_decoded {data start next count entries final}
    (indices : List U32) (default : U32)
    (h : BytesAt data start (count ++ entries ++ final) next)
    (hc : Leb128.Encoding count indices.length) (he : IndicesEncoding indices entries)
    (hf : Leb128.Encoding final default.val) :
    BrTable.Decoded data start indices default next := by
  obtain ⟨last, hprefix, hfinal⟩ := h.split
  obtain ⟨first, hcount, hentries⟩ := hprefix.split
  let n : U32 := U32.ofNatCore indices.length (by simpa using hc.value_lt)
  have hn : n.val = indices.length := by simp [n]
  exact ⟨n, first, last, hcount.u32_decoded n (by simpa [hn] using hc), hn.symm,
    he.decoded hentries, hfinal.u32_decoded default hf⟩

/-- A consumed span splits at any token boundary. -/
theorem Consumed.split_eq {data start tokens next} (h : Consumed data start tokens next)
    (first rest : List Token) (heq : tokens = first ++ rest) :
    ∃ middle, Consumed data start first middle ∧ Consumed data middle rest next := by
  induction h generalizing first rest with
  | nil hb =>
      have hempty : first = [] ∧ rest = [] := by simpa using heq.symm
      rcases hempty with ⟨rfl, rfl⟩
      exact ⟨start, .nil start hb, .nil start hb⟩
  | @snoc tokens pos token next hprefix hlast ih =>
      cases rest using List.reverseRecOn with
      | nil =>
          have hf : first = tokens ++ [token] := by simpa using heq.symm
          subst first
          exact ⟨next, .snoc hprefix hlast, .nil next hlast.span.2⟩
      | append_singleton rest last =>
          have heq' : tokens ++ [token] = (first ++ rest) ++ [last] := by
            simpa [List.append_assoc] using heq
          have ht : token = last := by
            have := congrArg List.getLast? heq'
            simpa using this
          subst last
          have hp : tokens = first ++ rest := List.append_cancel_right heq'
          obtain ⟨middle, hf, hr⟩ := ih first rest hp
          exact ⟨middle, hf, .snoc hr hlast⟩

/-- A consumed span of a concatenation splits into consecutive spans. -/
theorem Consumed.split {data start next first rest}
    (h : Consumed data start (first ++ rest) next) :
    ∃ middle, Consumed data start first middle ∧ Consumed data middle rest next :=
  h.split_eq first rest rfl

/-- An empty token list leaves the cursor in place. -/
theorem Consumed.empty_eq {data start tokens next}
    (h : Consumed data start tokens next) (he : tokens = []) : next = start := by
  cases h with
  | nil => rfl
  | snoc => simp at he

/-- A consumed span of one token is an `At`. -/
theorem Consumed.single {data start next token}
    (h : Consumed data start [token] next) : At data start token next := by
  generalize he : [token] = tokens at h
  cases h with
  | nil => simp at he
  | @snoc tokens pos last next hp hl =>
      have hlen := congrArg List.length he
      simp only [List.length_cons, List.length_nil, List.length_append] at hlen
      have ht : tokens = [] := List.length_eq_zero_iff.mp (by omega)
      have heq : last = token := by simpa [ht] using he.symm
      have hpos := hp.empty_eq ht
      simpa [heq, hpos] using hl

/-- A nonempty consumed span is its first token followed by the rest. -/
theorem Consumed.cons_iff {data start next token tokens} :
    Consumed data start (token :: tokens) next ↔
      ∃ middle, At data start token middle ∧ Consumed data middle tokens next := by
  constructor
  · intro h
    obtain ⟨middle, hh, ht⟩ := h.split_eq [token] tokens rfl
    exact ⟨middle, hh.single, ht⟩
  · rintro ⟨middle, hh, ht⟩
    have hb : start.val ≤ data.length := by have := hh.span; omega
    exact Consumed.append (.snoc (.nil start hb) hh) ht

end Itasca.Wasm1

namespace Itasca.Wasm1

end Itasca.Wasm1
