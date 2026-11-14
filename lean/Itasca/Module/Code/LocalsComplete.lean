import Itasca.Module.Code.Encoding
import Itasca.Profile.CodeEntry
import Itasca.Module.Readers.Utf8

/-!
Sections, each formerly its own module: Section, LocalsComplete.
-/

/-! ## Section -/

section

/-!
# Code section structure

Declarative notions for the code section. `Extent` is the size framing of one entry, `Section` is
the section header and entry count, and `EntriesTyped` says the entries are `CodeEntry.Typed`
against the defined functions in order. `Validated` is the independent encoding of the section
together with the typing of every entry. `EntriesTyped.append` and `entries_at_append` compose
adjacent batches, and `Section.encoding` assembles the section encoding.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleCode

/-- The entry at `start` has content starting at `content` and ending at `finish` within the data.
Entry framing is independent of local declarations and body validation. -/
def Extent (data : Slice U8) (start content finish : Usize) : Prop :=
  ∃ size, Leb128.Decoded data start size content ∧
    finish.val = content.val + size.val ∧ finish.val ≤ data.length

/-- An `Extent` is ordered and lies within the data. -/
theorem Extent.span {data start content finish} (h : Extent data start content finish) :
    start.val < content.val ∧ content.val ≤ finish.val ∧ finish.val ≤ data.length := by
  obtain ⟨size, hs, hn, hb⟩ := h
  have := hs.span
  omega

/-- A LEB128 size decoded at a position is unique, together with its end. -/
theorem decoded_unique {data start x y next last}
    (hx : Leb128.Decoded data start x next) (hy : Leb128.Decoded data start y last) :
    x = y ∧ next = last := by
  have h := (reader.read_u32_leb.complete data start x next hx).symm.trans
    (reader.read_u32_leb.complete data start y last hy)
  simpa using h

/-- The fields of a code section header: the entry count, the position of the first entry and the
end of the section. -/
structure Header where
  count : U32
  entries : Usize
  «end» : Usize

/-- The header `cs` is the code section header at `start`, with an entry count equal to the number
of defined functions. -/
def Section (data : Slice U8) (start : Usize) (env : metadata.Env) (cs : Header) : Prop :=
  ∃ content, ModuleBinary.SectionHeader data start 10#u8 content cs.end ∧
    Leb128.Decoded data content cs.count cs.entries ∧
    cs.count.val = env.func_type_indices.val.length

/-- The code entry is typed against the `i`-th defined function and has a declared local count
within `limits.MAX_LOCALS`. -/
def EntryAt (env : metadata.Env) (i : Nat) (entry : ModuleBinary.Code) : Prop :=
  ∃ hi : i < env.func_type_indices.val.length,
    CodeEntry.Typed env env.func_type_indices.val[i] entry ∧
    entry.declared.length ≤ limits.MAX_LOCALS.val

/-- The entries are `EntryAt` the defined functions in order, starting at function index `i`. -/
inductive EntriesTypedFor (env : metadata.Env) : Nat → List ModuleBinary.Code → Prop where
  | nil (i : Nat) : EntriesTypedFor env i []
  | cons {i entry entries} : EntryAt env i entry →
      EntriesTypedFor env (i + 1) entries → EntriesTypedFor env i (entry :: entries)

/-- Typed entries indexed by their function position. -/
abbrev EntriesTyped (env : metadata.Env) (i : Nat) (entries : List ModuleBinary.Code) : Prop := EntriesTypedFor env i entries

/-- Typed entries extend by one more entry at the next function index. -/
theorem EntriesTyped.snoc {env i entries entry}
    (h : EntriesTyped env i entries) (he : EntryAt env (i + entries.length) entry) :
    EntriesTyped env i (entries ++ [entry]) := by
  induction h with
  | nil i => exact .cons (by simpa using he) (.nil _)
  | @cons i first rest hfirst hrest ih =>
    exact .cons hfirst (ih (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he))

/-- An entry repetition extends by one more entry at its end position. -/
theorem entries_at_snoc {data start pos next entries entry} {R : ModuleBinary.Code → List U8 → Prop}
    (hp : ModuleBinary.At (ModuleBinary.Rep R) data start entries pos)
    (he : ModuleBinary.At R data pos entry next) :
    ModuleBinary.At (ModuleBinary.Rep R) data start (entries ++ [entry]) next := by
  obtain ⟨bs, hb, hs⟩ := hp
  obtain ⟨cs, hc, ht⟩ := he
  exact ⟨bs ++ cs, hb.snoc hc, hs.append ht⟩

/-- Typed entries covering all remaining functions are pointwise `CodeEntry.Typed` against the
function type indices from `i`. -/
theorem EntriesTyped.forall₂ {env i entries}
    (h : EntriesTyped env i entries) (hn : i + entries.length = env.func_type_indices.val.length) :
    List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry) (env.func_type_indices.val.drop i) entries := by
  induction h with
  | nil i =>
    have hb : env.func_type_indices.val.length ≤ i := by simpa using hn.symm.le
    simp [List.drop_eq_nil_of_le hb]
  | @cons i entry entries ht hs ih =>
    obtain ⟨hi, ht, _⟩ := ht
    rw [List.drop_eq_getElem_cons hi]
    exact .cons ht (ih (by simp only [List.length_cons] at hn; omega))

/-- Concatenate adjacent typed batches in defined-function order. -/
theorem EntriesTyped.append {env i first second}
    (hfirst : EntriesTyped env i first)
    (hsecond : EntriesTyped env (i + first.length) second) :
    EntriesTyped env i (first ++ second) := by
  induction hfirst with
  | nil i => simpa using hsecond
  | @cons i entry entries he hs ih =>
    exact .cons he (ih (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsecond))

/-- Independent entry encodings compose at their common byte boundary. -/
theorem entries_at_append {data start middle finish first second} {R : ModuleBinary.Code → List U8 → Prop}
    (hfirst : ModuleBinary.At (ModuleBinary.Rep R) data start first middle)
    (hsecond : ModuleBinary.At (ModuleBinary.Rep R) data middle second finish) :
    ModuleBinary.At (ModuleBinary.Rep R) data start (first ++ second) finish := by
  obtain ⟨bs, hb, hs⟩ := hfirst
  obtain ⟨cs, hc, ht⟩ := hsecond
  exact ⟨bs ++ cs, hb.append hc, hs.append ht⟩

/-- The independent encoding of the code section, which may be absent. -/
def Encoding := ModuleBinary.OptionalSectionEncoding 10#u8
  (ModuleBinary.VecEncoding (Profile.CodeEncoding)) []

/-- A section header and an independent entry repetition with the right count give the section
`Encoding`. -/
theorem Section.encoding {data start env cs entries}
    (h : Section data start env cs)
    (hb : ModuleBinary.At (ModuleBinary.Rep (Profile.CodeEncoding)) data cs.entries entries cs.end)
    (hn : entries.length = env.func_type_indices.val.length) :
    ModuleBinary.At (Encoding) data start entries cs.end := by
  obtain ⟨content, ⟨afterId, size, hid, hsize, hlen, _⟩, hcount, hcountval⟩ := h
  obtain ⟨countBytes, hc, hclen, hcbound, hcenc⟩ := hcount
  obtain ⟨entryBytes, he, hes⟩ := hb
  have payload : Wasm1.BytesAt data content (countBytes ++ entryBytes) cs.end :=
    (⟨hc, hclen, hcbound⟩ : Wasm1.BytesAt data content countBytes cs.entries).append hes
  obtain ⟨sizeBytes, hs, hslen, hsbound, hsenc⟩ := hsize
  have hsizeval : size.val = (countBytes ++ entryBytes).length := by
    have := payload.length
    omega
  have hpayload : ModuleBinary.VecEncoding (Profile.CodeEncoding) entries (countBytes ++ entryBytes) :=
    ⟨countBytes, entryBytes, by simpa [hcountval, hn] using hcenc, he, rfl⟩
  refine ⟨10#u8 :: (sizeBytes ++ (countBytes ++ entryBytes)), .present ?_, ?_⟩
  · exact ⟨sizeBytes, countBytes ++ entryBytes, by simpa [hsizeval] using hsenc, hpayload, rfl⟩
  · simpa using hid.byte.append
      ((⟨hs, hslen, hsbound⟩ : Wasm1.BytesAt data afterId sizeBytes content).append payload)

/-- A code section may be absent at `pos` when the input ends there or a complete non-code header
follows. The header must be complete because the implementation checks its extent before examining
its section id. -/
def AbsentAt (data : Slice U8) (pos : Usize) : Prop :=
  pos.val = data.length ∨
    ∃ id first last, ModuleBinary.SectionHeader data pos id first last ∧ id ≠ 10#u8

theorem module_room : limits.MAX_MODULE_BYTES.val + 11 ≤ Usize.max := by
  simp only [limits.MAX_MODULE_BYTES]
  scalar_tac

end Itasca.ModuleCode

namespace Itasca.ModuleBinary

/-- An independently encoded code entry has an `Extent`. -/
theorem At.code_extent {data pos entry next}
    (h : At (Profile.CodeEncoding) data pos entry next) :
    ∃ first, ModuleCode.Extent data pos first next := by
  obtain ⟨bytes, he, hs⟩ := h
  obtain ⟨sizeBytes, localBytes, bodyBytes, hsize, _, _, rfl⟩ := he
  obtain ⟨bodyStart, hprefix, hbody⟩ := hs.split
  obtain ⟨first, hhead, hlocals⟩ := hprefix.split
  let count : U32 := U32.ofNatCore (localBytes.length + bodyBytes.length) (by have := hsize.value_lt; scalar_tac)
  have hc : count.val = localBytes.length + bodyBytes.length := by simp [count]
  exact ⟨first, count, hhead.u32_decoded count (by simpa [hc] using hsize),
    by have := hlocals.length; have := hbody.length; omega, hs.bound⟩

end Itasca.ModuleBinary

end

/-! ## LocalsComplete -/

section

/-!
# Local declaration completeness

`metadata.decode_locals.complete` shows that `metadata.decode_locals` accepts any independent
`LocalEncoding` vector whose expansion fits in
`limits.MAX_LOCALS`, returning the expansion `ModuleLocals.declared`.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary

/-- The loop of `metadata.decode_locals` accepts the remaining encoded groups and returns the
output extended by their expansion. -/
theorem metadata.decode_locals_loop.complete (data : Slice U8) (groups : U32)
    (out : alloc.vec.Vec wasm_types.ValueType) (pos : Usize) (i : U32)
    (decoded : List (U32 × wasm_types.ValueType)) (next : Usize)
    (hcount : i.val + decoded.length = groups.val)
    (hbytes : At (Rep LocalEncoding) data pos decoded next)
    (hcap : out.val.length + (ModuleLocals.declared decoded).length ≤ limits.MAX_LOCALS.val) :
    ∃ locals, metadata.decode_locals_loop data groups out pos i = .ok (.Ok (locals, next)) ∧
      locals.val = out.val ++ ModuleLocals.declared decoded := by
  induction decoded generalizing out pos i with
  | nil =>
    have hi : i = groups := UScalar.eq_of_val_eq (by simpa using hcount)
    have hn := hbytes.rep_nil
    refine ⟨out, ?_, by simp [ModuleLocals.declared]⟩
    unfold metadata.decode_locals_loop
    rw [loop]
    simp [metadata.decode_locals_loop.body, hi, hn]
  | cons group rest ih =>
    obtain ⟨count, ty⟩ := group
    obtain ⟨middle, hlocal, hrest⟩ := hbytes.rep_cons
    obtain ⟨bytes, ⟨countBytes, hcountBytes, rfl⟩, hlocal⟩ := hlocal
    obtain ⟨valuePos, hcountSpan, htypeSpan⟩ := hlocal.split
    have hread := hcountSpan.read_u32 count hcountBytes
    have htype := metadata.decode_value_type.complete data valuePos ty middle
      ⟨[valueByte ty], rfl, htypeSpan⟩
    have hlt : i.val < groups.val := by simp only [List.length_cons] at hcount; omega
    have hstop : ¬ i ≥ groups := by scalar_tac
    have hdecl : ModuleLocals.declared ((count, ty) :: rest) =
        List.replicate count.val ty ++ ModuleLocals.declared rest := rfl
    have hroom : out.val.length + count.val + (ModuleLocals.declared rest).length ≤ limits.MAX_LOCALS.val := by
      simpa [hdecl, List.length_append, List.length_replicate, Nat.add_assoc] using hcap
    obtain ⟨space, hspace, hspaceVal⟩ := WP.spec_imp_exists
      (UScalar.sub_spec (x := limits.MAX_LOCALS) (y := alloc.vec.Vec.len out) (by scalar_tac))
    have hfits : ¬ UScalar.cast .Usize count > space := by
      have hc := U32.cast_Usize_val_eq count
      scalar_tac
    have hfitval : ¬ space.val < count.val := by scalar_tac
    have hmax : limits.MAX_LOCALS.val ≤ Usize.max := by
      simp only [limits.MAX_LOCALS]; scalar_tac
    obtain ⟨pushed, hpush, hpushed⟩ := WP.spec_imp_exists
      (metadata.push_locals.spec out count ty (by omega))
    obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x := i) (y := 1#u32) (by scalar_tac))
    obtain ⟨locals, hrec, hvals⟩ := ih pushed middle j
      (by simp only [List.length_cons] at hcount; scalar_tac) hrest
      (by simpa [hpushed, List.length_append, List.length_replicate] using hroom)
    refine ⟨locals, ?_, by simpa [hpushed, hdecl, List.append_assoc] using hvals⟩
    unfold metadata.decode_locals_loop
    rw [loop]
    simp only [metadata.decode_locals_loop.body, hstop, ↓reduceIte, hread, bind_ok,
      core.result.Result.Insts.CoreOpsTry.branch, lift, hspace, hj]
    simpa [metadata.decode_locals_loop, metadata.decode_locals_loop.body,
      core.result.Result.Insts.CoreOpsTry.branch, lift, htype, hfitval, hpush, hspace, hj] using hrec

/-- `metadata.decode_locals` accepts an independently encoded local vector within the limit and
returns its expansion. -/
theorem metadata.decode_locals.complete (data : Slice U8) (pos : Usize)
    (groups : List (U32 × wasm_types.ValueType)) (next : Usize)
    (hbytes : At (VecEncoding LocalEncoding) data pos groups next)
    (hcap : (ModuleLocals.declared groups).length ≤ limits.MAX_LOCALS.val) :
    ∃ locals, metadata.decode_locals data pos = .ok (.Ok (locals, next)) ∧
      locals.val = ModuleLocals.declared groups := by
  obtain ⟨count, first, hcount, hread, hrest⟩ := hbytes.vector_split
  obtain ⟨locals, hloop, hvals⟩ := metadata.decode_locals_loop.complete data count
    (alloc.vec.Vec.new _) first 0#u32 groups next (by simpa using hcount.symm) hrest (by simpa using hcap)
  refine ⟨locals, ?_, by simpa using hvals⟩
  simp [metadata.decode_locals, reader.read_u32_leb.complete data pos count first hread,
    core.result.Result.Insts.CoreOpsTry.branch, hloop]

end Itasca

end
