import Itasca.Module.Code.Context
import Itasca.Profile.CodeEntry
import Itasca.Module.Readers.FramingComplete

open Aeneas Aeneas.Std

namespace Itasca.ModuleCode

/-- Entry framing is independent of local declarations and body validation. -/
def Extent (data : Slice U8) (start content finish : Usize) : Prop :=
  ∃ size, Leb128.Decoded data start size content ∧
    finish.val = content.val + size.val ∧ finish.val ≤ data.length

theorem Extent.span {data start content finish} (h : Extent data start content finish) :
    start.val < content.val ∧ content.val ≤ finish.val ∧ finish.val ≤ data.length := by
  obtain ⟨size, hs, hn, hb⟩ := h
  have := hs.span
  omega

theorem decoded_unique {data start x y next last}
    (hx : Leb128.Decoded data start x next) (hy : Leb128.Decoded data start y last) :
    x = y ∧ next = last := by
  have h := (reader.read_u32_leb.complete data start x next hx).symm.trans
    (reader.read_u32_leb.complete data start y last hy)
  simpa using h

/-- Semantic code-header fields, independent of the legacy reader record. -/
structure Header where
  count : U32
  entries : Usize
  «end» : Usize

def Section (data : Slice U8) (start : Usize) (env : module.Env) (cs : Header) : Prop :=
  ∃ content, ModuleBinary.SectionHeader data start 10#u8 content cs.end ∧
    Leb128.Decoded data content cs.count cs.entries ∧
    cs.count.val = env.func_type_indices.val.length

def EntryAt (env : module.Env) (i : Nat) (entry : ModuleBinary.Code)
    (profile : ValidationProfile := .Wasm1) : Prop :=
  ∃ hi : i < env.func_type_indices.val.length,
    CodeEntry.Typed env env.func_type_indices.val[i] entry profile ∧
    entry.declared.length ≤ limits.MAX_LOCALS.val

inductive EntriesTypedFor (profile : ValidationProfile) (env : module.Env) : Nat → List ModuleBinary.Code → Prop where
  | nil (i : Nat) : EntriesTypedFor profile env i []
  | cons {i entry entries} : EntryAt (profile := profile) env i entry →
      EntriesTypedFor profile env (i + 1) entries → EntriesTypedFor profile env i (entry :: entries)

/-- The profile parameter selects the instruction restrictions of each entry;
legacy callers retain the established Wasm 1.0 specialization. -/
abbrev EntriesTyped (env : module.Env) (i : Nat) (entries : List ModuleBinary.Code)
    (profile : ValidationProfile := .Wasm1) : Prop := EntriesTypedFor profile env i entries

theorem EntriesTyped.snoc {env i entries entry} {profile : ValidationProfile}
    (h : EntriesTyped (profile := profile) env i entries) (he : EntryAt (profile := profile) env (i + entries.length) entry) :
    EntriesTyped (profile := profile) env i (entries ++ [entry]) := by
  induction h with
  | nil i => exact .cons (by simpa using he) (.nil _)
  | @cons i first rest hfirst hrest ih =>
    exact .cons hfirst (ih (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he))

theorem entries_at_snoc {data start pos next entries entry} {R : ModuleBinary.Code → List U8 → Prop}
    (hp : ModuleBinary.At (ModuleBinary.Rep R) data start entries pos)
    (he : ModuleBinary.At R data pos entry next) :
    ModuleBinary.At (ModuleBinary.Rep R) data start (entries ++ [entry]) next := by
  obtain ⟨bs, hb, hs⟩ := hp
  obtain ⟨cs, hc, ht⟩ := he
  exact ⟨bs ++ cs, hb.snoc hc, hs.append ht⟩

theorem EntriesTyped.forall₂ {env i entries} {profile : ValidationProfile}
    (h : EntriesTyped (profile := profile) env i entries) (hn : i + entries.length = env.func_type_indices.val.length) :
    List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry profile) (env.func_type_indices.val.drop i) entries := by
  induction h with
  | nil i =>
    have hb : env.func_type_indices.val.length ≤ i := by simpa using hn.symm.le
    simp [List.drop_eq_nil_of_le hb]
  | @cons i entry entries ht hs ih =>
    obtain ⟨hi, ht, _⟩ := ht
    rw [List.drop_eq_getElem_cons hi]
    exact .cons ht (ih (by simp only [List.length_cons] at hn; omega))

/-- Concatenate adjacent typed batches in defined-function order. -/
theorem EntriesTyped.append {env i first second} {profile : ValidationProfile}
    (hfirst : EntriesTyped (profile := profile) env i first)
    (hsecond : EntriesTyped (profile := profile) env (i + first.length) second) :
    EntriesTyped (profile := profile) env i (first ++ second) := by
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

def Encoding (profile : ValidationProfile := .Wasm1) := ModuleBinary.OptionalSectionEncoding 10#u8
  (ModuleBinary.VecEncoding (Profile.CodeEncoding profile)) []

def Validated (data : Slice U8) (start : Usize) (env : module.Env) (finish : Usize)
    (profile : ValidationProfile := .Wasm1) : Prop :=
  ∃ entries, ModuleBinary.At (Encoding (profile := profile)) data start entries finish ∧
    entries.length = env.func_type_indices.val.length ∧ EntriesTyped (profile := profile) env 0 entries

theorem Validated.padded {data start env finish} {profile : ValidationProfile} (h : Validated (profile := profile) data start env finish) :
    ∃ entries, ModuleBinary.At
      (ModuleBinary.PaddedEncoding 10#u8 (ModuleBinary.VecEncoding (Profile.CodeEncoding profile)) [])
      data start entries finish ∧
      List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry profile) env.func_type_indices.val entries := by
  obtain ⟨entries, ⟨bytes, he, hb⟩, hn, ht⟩ := h
  exact ⟨entries, ⟨bytes, ⟨[], bytes, .nil, he, rfl⟩, hb⟩,
    by simpa using ht.forall₂ (by simpa using hn)⟩

theorem Section.encoding {data start env cs entries} {profile : ValidationProfile}
    (h : Section data start env cs)
    (hb : ModuleBinary.At (ModuleBinary.Rep (Profile.CodeEncoding profile)) data cs.entries entries cs.end)
    (hn : entries.length = env.func_type_indices.val.length) :
    ModuleBinary.At (Encoding (profile := profile)) data start entries cs.end := by
  obtain ⟨content, ⟨afterId, size, hid, hsize, hlen, _⟩, hcount, hcountval⟩ := h
  obtain ⟨countBytes, hc, hclen, hcbound, hcenc⟩ := hcount
  obtain ⟨entryBytes, he, hes⟩ := hb
  have payload : Wasm1.BytesAt data content (countBytes ++ entryBytes) cs.end :=
    (⟨hc, hclen, hcbound⟩ : Wasm1.BytesAt data content countBytes cs.entries).append hes
  obtain ⟨sizeBytes, hs, hslen, hsbound, hsenc⟩ := hsize
  have hsizeval : size.val = (countBytes ++ entryBytes).length := by
    have := payload.length
    omega
  have hpayload : ModuleBinary.VecEncoding (Profile.CodeEncoding profile) entries (countBytes ++ entryBytes) :=
    ⟨countBytes, entryBytes, by simpa [hcountval, hn] using hcenc, he, rfl⟩
  refine ⟨10#u8 :: (sizeBytes ++ (countBytes ++ entryBytes)), .present ?_, ?_⟩
  · exact ⟨sizeBytes, countBytes ++ entryBytes, by simpa [hsizeval] using hsenc, hpayload, rfl⟩
  · simpa using hid.byte.append
      ((⟨hs, hslen, hsbound⟩ : Wasm1.BytesAt data afterId sizeBytes content).append payload)

/-- An absent code section is justified by EOF or a complete non-code header.
The header premise matters because the implementation checks its extent before
examining its section ID. -/
def AbsentAt (data : Slice U8) (pos : Usize) : Prop :=
  pos.val = data.length ∨
    ∃ id first last, ModuleBinary.SectionHeader data pos id first last ∧ id ≠ 10#u8

theorem module_room : limits.MAX_MODULE_BYTES.val + 11 ≤ Usize.max := by
  simp only [limits.MAX_MODULE_BYTES]
  scalar_tac

end Itasca.ModuleCode

namespace Itasca.ModuleBinary

theorem At.code_extent {data pos entry next} {profile : ValidationProfile}
    (h : At (Profile.CodeEncoding profile) data pos entry next) :
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
