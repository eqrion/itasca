import Itasca.Module.CodeMetadata
import Itasca.Module.Definitions
import Itasca.Results.Definitions.Validation
import Itasca.Module.Code.ContextTransport
import Itasca.CodeEntry.Encoding
import Itasca.Module.Readers.Syntax
import Itasca.Stream.Definitions
import Itasca.Binary.Scalar.MemoryMeaning
import Itasca.Results.Definitions.Streaming
import Itasca.Visitor.Total
import Itasca.Support.Translation

/-!
Proofs for Module / Code.

This module collects Section, Framing.
Each section documents its contracts and consumers.
-/

/-! ## Section -/

section

/-!
# Code-section framing and local completeness

Entry extents, repeated-entry typing and code-section encodings compose exact byte spans.
Local-declaration completeness constructs the decoded groups and expanded local context
used by entry validation.
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

namespace Itasca.Module.Code

/-- The entry at `start` has content starting at `content` and ending at `finish` within the data.
Entry framing is independent of local declarations and body validation. -/
def Extent (data : Slice U8) (start content finish : Usize) : Prop :=
  ∃ size, Binary.Leb128.Decoded data start size content ∧
    finish.val = content.val + size.val ∧ finish.val ≤ data.length

/-- An `Extent` is ordered and lies within the data. -/
theorem Extent.span {data start content finish} (h : Extent data start content finish) :
    start.val < content.val ∧ content.val ≤ finish.val ∧ finish.val ≤ data.length := by
  obtain ⟨size, hs, hn, hb⟩ := h
  have := hs.span
  omega

/-- A LEB128 size decoded at a position is unique, together with its end. -/
theorem decoded_unique {data start x y next last}
    (hx : Binary.Leb128.Decoded data start x next) (hy : Binary.Leb128.Decoded data start y last) :
    x = y ∧ next = last := by
  have h := (reader.read_u32_leb.complete data start x next hx).symm.trans
    (reader.read_u32_leb.complete data start y last hy)
  simpa using h

/-- Typed entries extend by one more entry at the next function index. -/
theorem EntriesTyped.snoc {env i entries entry}
    (h : EntriesTyped env i entries) (he : EntryAt env (i + entries.length) entry) :
    EntriesTyped env i (entries ++ [entry]) := by
  induction h with
  | nil i => exact .cons (by simpa using he) (.nil _)
  | @cons i first rest hfirst hrest ih =>
    exact .cons hfirst (ih (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he))

/-- An entry repetition extends by one more entry at its end position. -/
theorem entries_at_snoc {data start pos next entries entry} {R : Binary.Code → List U8 → Prop}
    (hp : Binary.At (Binary.Rep R) data start entries pos)
    (he : Binary.At R data pos entry next) :
    Binary.At (Binary.Rep R) data start (entries ++ [entry]) next := by
  obtain ⟨bs, hb, hs⟩ := hp
  obtain ⟨cs, hc, ht⟩ := he
  exact ⟨bs ++ cs, hb.snoc hc, hs.append ht⟩

/-- Typed entries covering all remaining functions are pointwise `CodeEntry.Typed` against the
function type indices from `i`. -/
theorem EntriesTyped.forall₂ {env i entries}
    (h : EntriesTyped env i entries) (hn : i + entries.length = (Translation.Environment.definedTypeIndices env).length) :
    List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry) ((Translation.Environment.definedTypeIndices env).drop i) entries := by
  induction h with
  | nil i =>
    have hb : (Translation.Environment.definedTypeIndices env).length ≤ i := by simpa using hn.symm.le
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
theorem entries_at_append {data start middle finish first second} {R : Binary.Code → List U8 → Prop}
    (hfirst : Binary.At (Binary.Rep R) data start first middle)
    (hsecond : Binary.At (Binary.Rep R) data middle second finish) :
    Binary.At (Binary.Rep R) data start (first ++ second) finish := by
  obtain ⟨bs, hb, hs⟩ := hfirst
  obtain ⟨cs, hc, ht⟩ := hsecond
  exact ⟨bs ++ cs, hb.append hc, hs.append ht⟩

/-- The independent encoding of the code section, which may be absent. -/
def Encoding := Binary.OptionalSectionEncoding 10#u8
  (Binary.VecEncoding (CodeEntry.CodeEncoding)) []

/-- A section header and an independent entry repetition with the right count give the section
`Encoding`. -/
theorem Section.encoding {data start env cs entries}
    (h : Section data start env cs)
    (hb : Binary.At (Binary.Rep (CodeEntry.CodeEncoding)) data cs.entries entries cs.end)
    (hn : entries.length = (Translation.Environment.definedTypeIndices env).length) :
    Binary.At (Encoding) data start entries cs.end := by
  obtain ⟨content, ⟨afterId, size, hid, hsize, hlen, _⟩, hcount, hcountval⟩ := h
  obtain ⟨countBytes, hc, hclen, hcbound, hcenc⟩ := hcount
  obtain ⟨entryBytes, he, hes⟩ := hb
  have payload : Body.Scalar.BytesAt data content (countBytes ++ entryBytes) cs.end :=
    (⟨hc, hclen, hcbound⟩ : Body.Scalar.BytesAt data content countBytes cs.entries).append hes
  obtain ⟨sizeBytes, hs, hslen, hsbound, hsenc⟩ := hsize
  have hsizeval : size.val = (countBytes ++ entryBytes).length := by
    have := payload.length
    omega
  have hpayload : Binary.VecEncoding (CodeEntry.CodeEncoding) entries (countBytes ++ entryBytes) :=
    ⟨countBytes, entryBytes, by simpa [hcountval, hn] using hcenc, he, rfl⟩
  refine ⟨10#u8 :: (sizeBytes ++ (countBytes ++ entryBytes)), .present ?_, ?_⟩
  · exact ⟨sizeBytes, countBytes ++ entryBytes, by simpa [hsizeval] using hsenc, hpayload, rfl⟩
  · simpa using hid.byte.append
      ((⟨hs, hslen, hsbound⟩ : Body.Scalar.BytesAt data afterId sizeBytes content).append payload)

/-- A code section may be absent at `pos` when the input ends there or a complete non-code header
follows. The header must be complete because the implementation checks its extent before examining
its section id. -/
def AbsentAt (data : Slice U8) (pos : Usize) : Prop :=
  pos.val = data.length ∨
    ∃ id first last, Binary.SectionHeader data pos id first last ∧ id ≠ 10#u8

theorem module_room : limits.MAX_MODULE_BYTES.val + 11 ≤ Usize.max := by
  simp only [limits.MAX_MODULE_BYTES]
  scalar_tac

end Itasca.Module.Code

namespace Itasca.Binary

/-- An independently encoded code entry has an `Extent`. -/
theorem At.code_extent {data pos entry next}
    (h : At (CodeEntry.CodeEncoding) data pos entry next) :
    ∃ first, Module.Code.Extent data pos first next := by
  obtain ⟨bytes, he, hs⟩ := h
  obtain ⟨sizeBytes, localBytes, bodyBytes, hsize, _, _, rfl⟩ := he
  obtain ⟨bodyStart, hprefix, hbody⟩ := hs.split
  obtain ⟨first, hhead, hlocals⟩ := hprefix.split
  let count : U32 := U32.ofNatCore (localBytes.length + bodyBytes.length) (by have := hsize.value_lt; scalar_tac)
  have hc : count.val = localBytes.length + bodyBytes.length := by simp [count]
  exact ⟨first, count, hhead.u32_decoded count (by simpa [hc] using hsize),
    by have := hlocals.length; have := hbody.length; omega, hs.bound⟩

end Itasca.Binary

end

/-! ## LocalsComplete -/

section

/-!
# Local declaration completeness

`metadata.decode_locals.complete` shows that `metadata.decode_locals` accepts any independent
`LocalEncoding` vector whose expansion fits in
`limits.MAX_LOCALS`, returning the expansion `CodeEntry.Locals.declared`.
-/

open Aeneas Aeneas.Std

namespace Itasca

open Binary

/-- The loop of `metadata.decode_locals` accepts the remaining encoded groups and returns the
output extended by their expansion. -/
theorem metadata.decode_locals_loop.complete (data : Slice U8) (groups : U32)
    (out : alloc.vec.Vec wasm_types.ValueType) (pos : Usize) (i : U32)
    (decoded : List (U32 × wasm_types.ValueType)) (next : Usize)
    (hcount : i.val + decoded.length = groups.val)
    (hbytes : At (Rep LocalEncoding) data pos decoded next)
    (hcap : out.val.length + (CodeEntry.Locals.declared decoded).length ≤ limits.MAX_LOCALS.val) :
    ∃ locals, metadata.decode_locals_loop data groups out pos i = .ok (.Ok (locals, next)) ∧
      locals.val = out.val ++ CodeEntry.Locals.declared decoded := by
  induction decoded generalizing out pos i with
  | nil =>
    have hi : i = groups := UScalar.eq_of_val_eq (by simpa using hcount)
    have hn := hbytes.rep_nil
    refine ⟨out, ?_, by simp [CodeEntry.Locals.declared]⟩
    unfold metadata.decode_locals_loop
    rw [loop]
    simp [metadata.decode_locals_loop.body, hi, hn]
  | cons group rest ih =>
    obtain ⟨count, ty⟩ := group
    obtain ⟨middle, hlocal, hrest⟩ := hbytes.rep_cons
    obtain ⟨bytes, he, hlocal⟩ := hlocal
    obtain ⟨countBytes, hcountBytes, rfl⟩ := LocalEncoding.reader_parts.mp he
    obtain ⟨valuePos, hcountSpan, htypeSpan⟩ := hlocal.split
    have hread := hcountSpan.read_u32 count hcountBytes
    have htype := metadata.decode_value_type.complete data valuePos ty middle
      ⟨_, ValueTypeEncoding.reader_bytes.mpr rfl, htypeSpan⟩
    have hlt : i.val < groups.val := by simp only [List.length_cons] at hcount; omega
    have hstop : ¬ i ≥ groups := by scalar_tac
    have hdecl : CodeEntry.Locals.declared ((count, ty) :: rest) =
        List.replicate count.val ty ++ CodeEntry.Locals.declared rest := rfl
    have hroom : out.val.length + count.val + (CodeEntry.Locals.declared rest).length ≤ limits.MAX_LOCALS.val := by
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
    (hcap : (CodeEntry.Locals.declared groups).length ≤ limits.MAX_LOCALS.val) :
    ∃ locals, metadata.decode_locals data pos = .ok (.Ok (locals, next)) ∧
      locals.val = CodeEntry.Locals.declared groups := by
  obtain ⟨count, first, hcount, hread, hrest⟩ := hbytes.vector_split
  obtain ⟨locals, hloop, hvals⟩ := metadata.decode_locals_loop.complete data count
    (alloc.vec.Vec.new _) first 0#u32 groups next (by simpa using hcount.symm) hrest (by simpa using hcap)
  refine ⟨locals, ?_, by simpa using hvals⟩
  simp [metadata.decode_locals, reader.read_u32_leb.complete data pos count first hread,
    core.result.Result.Insts.CoreOpsTry.branch, hloop]

end Itasca

end

end

/-! ## Framing -/

section

/-! ## Entry -/

section

/-!
# Code entry validation

For any visitor with total callbacks, `metadata.validate_code_entry_with.pipeline_of_body_total`
reduces termination to body termination and records successful calls as a `CodeEntry.Witness`.
The code-entry proofs combine these witnesses with body soundness.
-/

open Aeneas Aeneas.Std

namespace Itasca.CodeEntry

/-- The data of a successful run of the entry validator at `index`, from `start` to `finish`. It
records the size header, the locals bytes and bound, the context handed to the visitor, the
function-start callback and the body validation on the body slice. -/
structure Witness {V : Type} (visitor : code.OpVisitor V) (data : Slice U8)
    (env : metadata.CodeMetadata) (index start finish : Usize) (v v' : V)
     where
  typeIdx : U32
  ft : wasm_types.FuncType
  groups : List (U32 × wasm_types.ValueType)
  ctx : code.Context
  content : Usize
  bodyStart : Usize
  body : Slice U8
  size : U32
  startedState : V
  index_lt : index.val < (Translation.Environment.definedTypeIndices env).length
  index_type : (Translation.Environment.definedTypeIndices env)[index.val] = typeIdx
  type_lt : typeIdx.val < env.types.val.length
  function_type : env.types.val[typeIdx.val] = ft
  header : Binary.Leb128.Decoded data start size content
  extent : finish.val = content.val + size.val
  locals_bytes : Binary.At (Binary.VecEncoding Binary.LocalEncoding)
    data content groups bodyStart
  locals_bound : (CodeEntry.Locals.declared groups).length ≤ limits.MAX_LOCALS.val
  context_locals : ctx.locals.val = ft.params.val ++ CodeEntry.Locals.declared groups
  context_results : ctx.results.val = ft.results.val
  body_bytes : Body.Scalar.BytesAt data bodyStart body.val finish
  function_start : visitor.on_function_start v ctx typeIdx bodyStart finish = .ok (.Ok (), startedState)
  body_accepted : code.validate_body_with visitor body env ctx typeIdx startedState =
    .ok (.Ok (), v')

/-- Parameter counts bounded by the maximum module size give `Bounds`. -/
theorem Bounds.of_module_bound (env : metadata.CodeMetadata)
    (imports : env.num_imported_funcs.val ≤ env.funcs.val.length)
    (h : ∀ ft ∈ env.types.val, ft.params.val.length ≤ limits.MAX_MODULE_BYTES.val) : Bounds env := by
  refine ⟨imports, ?_⟩
  intro ft hm
  have := h ft hm
  have hcap : limits.MAX_MODULE_BYTES.val + limits.MAX_LOCALS.val ≤ Usize.max := by
    simp only [limits.MAX_MODULE_BYTES, limits.MAX_LOCALS]
    scalar_tac
  omega

end CodeEntry

/-- Given a body operation that terminates, `metadata.validate_code_entry_with` terminates and each
successful call has a `CodeEntry.Witness`. Rejecting callbacks are ordinary module errors. -/
theorem metadata.validate_code_entry_with.pipeline_of_body_total {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : Visitor.Total visitor) (data : Slice U8) (pos : Usize)
    (env : metadata.CodeMetadata) (index : Usize) (v : V) (hbound : CodeEntry.Bounds env)

    (hbody : ∀ body ctx typeIdx started,
      ∃ r, code.validate_body_with visitor body env ctx typeIdx started = .ok r) :
    metadata.validate_code_entry_with visitor data pos env index v ⦃ r =>
      ∀ finish, r.1 = .Ok finish →
        Nonempty (CodeEntry.Witness visitor data env index pos finish v r.2 ) ⦄ := by
  unfold metadata.validate_code_entry_with
  obtain ⟨count, hcount, hcountVal⟩ := WP.spec_imp_exists (metadata.CodeMetadata.num_func_defs.spec env hbound.imported)
  simp only [hcount, bind_ok]
  split
  · simp
  · rename_i hindex
    have hi : index.val < (Translation.Environment.definedTypeIndices env).length := by simp [Translation.Environment.definedTypeIndices]; scalar_tac
    obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
    rw [hr]
    cases r with
    | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          error.Error.Insts.CoreConvertFromOpError.from]
    | Ok pair =>
        obtain ⟨size, content⟩ := pair
        have hs := hp.span
        simp [core.result.Result.Insts.CoreOpsTry.branch]
        step
        obtain ⟨r, hh, hhpost⟩ := WP.spec_imp_exists (metadata.have_bytes.spec data content n hs.2.2)
        rw [hh]
        cases r with
        | Err e =>
            simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok u =>
            cases u
            have hbytes := hhpost.1.mp rfl
            simp
            step
            obtain ⟨r, hl, hlpost⟩ := WP.spec_imp_exists (metadata.decode_locals.spec data content )
            rw [hl]
            cases r with
            | Err e =>
                simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok pair =>
                obtain ⟨declared, bodyStart⟩ := pair
                obtain ⟨groups, hg, hd, hcap⟩ := hlpost
                simp
                split
                · simp
                · rename_i hbodyStart
                  obtain ⟨absolute, fd, hadd, hfd, htypeIdx⟩ := Translation.Environment.defined_descriptor env index hi
                  simp only [hadd, bind_ok, hfd]
                  let type_idx := fd.type_index
                  step
                  split
                  · simp
                  · rename_i htype
                    have hti : type_idx.val < env.types.val.length := by scalar_tac
                    step
                    have hftmem : ft ∈ env.types.val := by
                      rw [ft_post]
                      exact List.getElem_mem _
                    have hparams := hbound.locals ft hftmem
                    have hroom : ft.params.val.length + declared.val.length ≤ Usize.max := by omega
                    obtain ⟨v1, hv1, v1_post⟩ := WP.spec_imp_exists
                      (metadata.build_func_locals.spec (alloc.vec.Vec.deref ft.params)
                        (alloc.vec.Vec.deref declared) (by simpa [alloc.vec.Vec.deref] using hroom))
                    obtain ⟨v2, hv2, v2_post⟩ := WP.spec_imp_exists
                      (metadata.copy_value_types.spec (alloc.vec.Vec.deref ft.results))
                    rw [hv1]
                    simp only [bind_ok]
                    rw [hv2]
                    simp only [bind_ok]
                    obtain ⟨reply, started, hstart⟩ := hvisitor.on_function_start v
                      ⟨v1, v2⟩ type_idx bodyStart «end»
                    rw [hstart]
                    cases reply with
                    | Err e => simp
                    | Ok u =>
                        cases u
                        simp
                        step as ⟨s3, s3_post⟩
                        obtain ⟨⟨result, finished⟩, hb⟩ := hbody s3 ⟨v1, v2⟩ type_idx started
                        rw [hb]
                        cases result with
                        | Err e => simp
                        | Ok u =>
                            cases u
                            simp
                            refine ⟨{
                              typeIdx := type_idx, ft := ft, groups := groups, ctx := ⟨v1, v2⟩
                              content := content, bodyStart := bodyStart, body := s3, size := size
                              startedState := started, index_lt := hi, index_type := htypeIdx.symm
                              type_lt := hti, function_type := ?_, header := hp, extent := ?_
                              locals_bytes := hg, locals_bound := ?_, context_locals := ?_
                              context_results := ?_, body_bytes := ?_, function_start := hstart
                              body_accepted := hb }⟩
                            · simpa [t_post] using ft_post.symm
                            · scalar_tac
                            · simpa [hd] using hcap
                            · simpa [alloc.vec.Vec.deref, hd] using v1_post
                            · simpa [alloc.vec.Vec.deref] using v2_post
                            · exact Binary.slice_bytes (by scalar_tac) (by scalar_tac) s3_post

end Itasca

end

/-! ## EntryWitness -/

section

/-!
# Code entry witnesses

`metadata.validate_code_entry_with.witness` extracts a `CodeEntry.Witness` from any
successful call of `metadata.validate_code_entry_with`, for the unified validator. The witness records the
actual visitor calls and parser results. Other executions of the visitor need not terminate.
`metadata.validate_code_entry_with.witness` is the scalar form.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- A successful `metadata.validate_code_entry_with` call gives a `CodeEntry.Witness` of its visitor
calls and parser results. Other executions of the visitor need not terminate. -/
theorem metadata.validate_code_entry_with.witness {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (pos : Usize) (env : metadata.CodeMetadata) (index finish : Usize)
    (v v' : V) (hbound : CodeEntry.Bounds env)
    (h : metadata.validate_code_entry_with visitor data pos env index v = .ok (.Ok finish, v')) :
    Nonempty (CodeEntry.Witness visitor data env index pos finish v v' ) := by
  unfold metadata.validate_code_entry_with at h
  obtain ⟨count, hcount, hcountVal⟩ := WP.spec_imp_exists (metadata.CodeMetadata.num_func_defs.spec env hbound.imported)
  simp only [hcount, bind_ok] at h
  by_cases hi : index ≥ count
  · simp [hi] at h
  rw [if_neg hi] at h
  have hindex : index.val < (Translation.Environment.definedTypeIndices env).length := by
    simp [Translation.Environment.definedTypeIndices]; scalar_tac
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  rw [hr] at h
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from] at h
  | Ok pair =>
    obtain ⟨size, content⟩ := pair
    have hspan := hp.span
    simp [core.result.Result.Insts.CoreOpsTry.branch, lift] at h
    obtain ⟨r, hr, hh⟩ := WP.spec_imp_exists
      (metadata.have_bytes.spec data content (UScalar.cast .Usize size) hspan.2.2)
    rw [hr] at h
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
    | Ok u =>
      cases u
      have hbytes := hh.1.mp rfl
      obtain ⟨last, hlast, hlastval⟩ := WP.spec_imp_exists
        (UScalar.add_spec (x := content) (y := UScalar.cast .Usize size) (by scalar_tac))
      simp [hlast] at h
      obtain ⟨r, hr, hl⟩ := WP.spec_imp_exists (metadata.decode_locals.spec data content )
      rw [hr] at h
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      | Ok pair =>
        obtain ⟨declared, bodyStart⟩ := pair
        obtain ⟨groups, hg, hd, hcap⟩ := hl
        simp at h
        by_cases hbeyond : last.val < bodyStart.val
        · simp [hbeyond] at h
        rw [if_neg hbeyond] at h
        obtain ⟨absolute, fd, hadd, hfd, htypeIdx⟩ := Translation.Environment.defined_descriptor env index hindex
        simp only [hadd, bind_ok, hfd] at h
        generalize hidx : fd.type_index = typeIdx at h htypeIdx
        by_cases htype : env.types.val.length ≤ typeIdx.val
        · simp [htype] at h
        rw [if_neg htype] at h
        have htype_lt : typeIdx.val < env.types.val.length := by omega
        have hget : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice wasm_types.FuncType)
            env.types (UScalar.cast .Usize typeIdx) ⦃ ft => ft = env.types.val[typeIdx.val] ⦄ := by
          step*
        obtain ⟨ft, hget, hft⟩ := WP.spec_imp_exists hget
        have hget : env.types.index_usize (UScalar.cast .Usize typeIdx) = .ok ft := by simpa using hget
        simp only [hget, bind_ok] at h
        have hmem : ft ∈ env.types.val := by rw [hft]; exact List.getElem_mem _
        have hparams := hbound.locals ft hmem
        obtain ⟨locals, hlocals, hlocalsval⟩ := WP.spec_imp_exists
          (metadata.build_func_locals.spec (alloc.vec.Vec.deref ft.params)
            (alloc.vec.Vec.deref declared) (by simpa [alloc.vec.Vec.deref] using (show
              ft.params.val.length + declared.val.length ≤ Usize.max from by omega)))
        obtain ⟨results, hresults, hresultsval⟩ := WP.spec_imp_exists
          (metadata.copy_value_types.spec (alloc.vec.Vec.deref ft.results))
        simp only [hlocals, hresults, bind_ok] at h
        obtain ⟨⟨reply, started⟩, hstart, ht⟩ := Computation.bind_ok_inv _ _ _ h
        cases reply with
        | Err e => simp at ht
        | Ok u =>
          cases u
          all_goals
            try dsimp only at ht
            have hslice : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
                data ⟨bodyStart, last⟩ ⦃ body => body.val = data.val.slice bodyStart.val last.val ⦄ := by
              step*
            obtain ⟨body, hbody, hbodyval⟩ := WP.spec_imp_exists hslice
            have hbody : core.slice.index.SliceIndexRangeUsizeSlice.index
                ⟨bodyStart, last⟩ data = .ok body := by simpa using hbody
            simp [hbody, Std.bind_assoc] at ht
            obtain ⟨⟨reply, ended⟩, hrun, ht⟩ := Computation.bind_ok_inv _ _ _ ht
            cases reply with
            | Err e => simp at ht
            | Ok u =>
              cases u
              have he : last = finish ∧ ended = v' := by simpa using ht
              obtain ⟨rfl, rfl⟩ := he
              refine ⟨{
                typeIdx := typeIdx, ft := ft, groups := groups, ctx := ⟨locals, results⟩
                content := content, bodyStart := bodyStart, body := body, size := size
                startedState := started, index_lt := hindex, index_type := htypeIdx.symm
                type_lt := htype_lt, function_type := hft.symm, header := hp
                extent := ?_, locals_bytes := hg, locals_bound := ?_
                context_locals := ?_, context_results := ?_, body_bytes := ?_
                function_start := hstart, body_accepted := hrun }⟩
              · scalar_tac
              · simpa [hd] using hcap
              · simpa [alloc.vec.Vec.deref, hd] using hlocalsval
              · simpa [alloc.vec.Vec.deref] using hresultsval
              · exact Binary.slice_bytes (by omega) (by scalar_tac) hbodyval

end Itasca

end

/-! ## Framing -/

section

/-!
# Code entry framing

`metadata.code_entry_extent.spec` gives the `Module.Code.Extent` corresponding to the declared size,
content start, and entry end on success.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- `metadata.code_entry_extent` returns an `Extent` of the entry on success. -/
@[step]
theorem metadata.code_entry_extent.spec (data : Slice U8) (pos : Usize) :
    metadata.code_entry_extent data pos ⦃ r => match r with
      | .Ok (content, finish) => Module.Code.Extent data pos content finish
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  rw [metadata.code_entry_extent, hr]
  cases r with
  | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
      obtain ⟨size, content⟩ := pair
      have hs := hp.span
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      step
      obtain ⟨r, hh, hhpost⟩ := WP.spec_imp_exists (metadata.have_bytes.spec data content n hs.2.2)
      rw [hh]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok u =>
          cases u
          have hb := hhpost.1.mp rfl
          simp
          step
          exact ⟨size, hp, by scalar_tac, by scalar_tac⟩


end Itasca

end

end
