import Itasca.Stream.Definitions
import Itasca.Results.Definitions.Streaming
import Itasca.Stream.RetirementAndFraming
import Itasca.Stream.SubmissionSound
import Itasca.Module.CustomTrace
import Itasca.Module.Code.Framing
import Itasca.Stream.WorkersAndSource
import Itasca.Module.Env.Complete
import Itasca.Module.Elab.Requirements
import Itasca.Module.Layout
import Itasca.Module.Sections.TailComplete
import Itasca.Module.Code.FuncTyping
import Itasca.Support.Translation

open WebAssembly

/-!
Proofs for Stream.

This module collects DriverRegions, Completeness, SliceComplete.
Each section documents its contracts and consumers.
-/

/-! ## DriverRegions -/

section

/-! ## Stream / DriverRegions -/

section StreamDriverRegions

/-!
### Independent input regions

`Certificate` packages the environment, code and tail evidence used to construct streaming acceptance from independently encoded modules.
-/

open Aeneas Aeneas.Std
open Itasca.Binary Itasca.Module.Elaboration

namespace Itasca.Stream.CompleteRegions

/-- Region certificates are derived from independent encoding and typing. They give the results
of the shared environment and tail validators and the encoded, typed code entries. Body checking
is later obtained from the typed, bounded encodings by the streaming driver. -/
structure Certificate (data : Slice U8) (raw : Binary.Module)
    (source : stream.SliceSource) (env : metadata.ModuleMetadata metadata.CodeMetadata) (tail : alloc.vec.Vec metadata.Data) : Prop where
  split : ComputedSplit data source
  canonical : Split data source
  bytes : data.val = source.env.val ++ source.code.val ++ source.tail.val
  bounded : data.length ≤ limits.MAX_MODULE_BYTES.val
  environment : metadata.validate_env source.env = .ok (.Ok (env, Slice.len source.env))
  ready : ∃ decls, Module.Environment.Ready raw 10 decls env
  entry_bounds : CodeEntry.Bounds env.code
  signature_limits : Itasca.CodeEntry.EnvironmentWithinLimits env.code
  code : ∃ entries, Stream.Framing.HeaderAt source.code env.code entries ∧
    At (Rep (Itasca.CodeEntry.CodeEncodingWithinLimits )) source.code entries raw.codes (Slice.len source.code)
  typed : Module.Code.EntriesTyped env.code 0 raw.codes
  code_count : raw.codes.length = (Translation.Environment.definedTypeIndices env.code).length
  tail_accepted : metadata.validate_tail source.tail 0#usize env.code = .ok (.Ok tail)
  realization : Matches {env with data := tail} raw
  metadata : AccessorTypes {env with data := tail} raw

end Itasca.Stream.CompleteRegions

end StreamDriverRegions

/-!
# Driver Regions

Scheduler and header completeness construct the complete driver-region certificate.
-/

/-! ## SchedulerComplete -/

section

/-!
# Accepting schedulers

Consequences of `Stream.Scheduler.Accepts`, the scheduler policy under which completeness
holds, and of `Stream.Scheduler.Valid`, the internal validity evidence for issued work.
The scheduler contract is public; batch validity lives in `Stream/Definitions`. `Stream.Scheduler.retire_complete` and
`Stream.Scheduler.drain_complete` show that valid queued work retires and drains
successfully.
-/

open Aeneas Aeneas.Std

namespace Itasca.Stream.Scheduler
/-- Running `validate_all` on the seed of a `Valid` batch gives a worker with the issued identity
that `stream.StreamingBatch.finish` accepts. -/
theorem Valid.finished {issued : Stream.Batch.Issued} (h : Valid issued)
    {after : stream.StreamingBatch} (hr : stream.StreamingBatch.validate_all issued.seed = .ok after) :
    Stream.Batch.Identity issued after ∧ stream.StreamingBatch.finish after = .ok (.Ok ()) := by
  obtain ⟨entries, hn, ht, hb⟩ := h.entries
  obtain ⟨result, hrun, hreachable, hfinish⟩ := stream.StreamingBatch.validate_all.complete_at_seed
    issued entries h.bounded hn ht h.limits h.entry_bounds hb
  have he : result = after := by simpa using hrun.symm.trans hr
  subst result
  exact ⟨hreachable.validation.1, hfinish⟩

end Itasca.Stream.Scheduler

namespace Itasca

/-- A polled batch of the right module, whose ID is pending and whose finish check succeeds, is
retired successfully by `stream.retire_code_batch`. -/
theorem stream.retire_code_batch.complete {V : Type} (visitor : stream.StreamingVisitor V)
    (id : U64) (v v' : V) (pending : alloc.vec.Vec Usize) (batch : stream.StreamingBatch)
    (hpoll : visitor.poll_code_batch v = .ok (.Ok batch, v'))
    (hmodule : batch.module_id = id) (hmem : batch.batch_id ∈ pending.val)
    (hfinish : stream.StreamingBatch.finish batch = .ok (.Ok ())) :
    ∃ remaining, stream.retire_code_batch visitor id v pending = .ok (.Ok (), v', remaining) ∧
      (batch.batch_id :: remaining.val).Perm pending.val := by
  obtain ⟨found, hfind, hf⟩ := WP.spec_imp_exists
    (stream.retire_code_batch_loop.spec pending batch.batch_id 0#usize (by simp))
  have hlt : found.val < pending.length := by
    by_contra hnot
    have hend : found.val = pending.length := by have := hf.2.1; omega
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hmem
    exact hf.2.2.1 i hi (by simp) (by simpa [hend] using hi) he
  have hmatch := hf.2.2.2 hlt
  have hne : found ≠ alloc.vec.Vec.len pending := by scalar_tac
  have hs : stream.retire_code_batch visitor id v pending ⦃ r =>
      r.1 = .Ok () ∧ r.2.1 = v' ∧ (batch.batch_id :: r.2.2.val).Perm pending.val ⦄ := by
    simp [stream.retire_code_batch, hpoll, core.result.Result.Insts.CoreOpsTry.branch,
      hmodule, hfind, hne]
    step
    step
    step
    simp only [alloc.vec.Vec.pop, bind_ok, hfinish]
    refine ⟨rfl, rfl, ?_⟩
    have hlast : last.val = pending.val.length - 1 := by scalar_tac
    simpa only [index_mut_back_post, i3_post, hlast, alloc.vec.Vec.set_val_eq,
      alloc.vec.Vec.from_val, hmatch] using
      (Stream.Retirement.swap_pop_perm pending.val found.val hlt)
  obtain ⟨⟨r, state, remaining⟩, hr, hsuccess, hstate, hperm⟩ := WP.spec_imp_exists hs
  dsimp only at hsuccess hstate hperm
  subst r
  subst state
  exact ⟨remaining, hr, hperm⟩

end Itasca

namespace Itasca.Stream.Scheduler
/-- Valid pending work retires in any scheduler-selected order. Successful finish follows from the
actual worker execution on independently typed encodings. -/
theorem retire_complete {V : Type} (visitor : stream.StreamingVisitor V)
    (config : stream.StreamingConfig) (Queued : U64 → List Stream.Batch.Issued → V → Prop)
    (hp : Accepts visitor config Queued) (id : U64)
    (queue : List Stream.Batch.Issued) (v : V) (pending : alloc.vec.Vec Usize)
    (hv : Queued id queue v) (hvalid : ValidQueue id queue)
    (hids : pending.val.Perm (queue.map Stream.Batch.Issued.batch_id))
    (hnonempty : pending.val ≠ []) :
    ∃ v' remaining rest,
      stream.retire_code_batch visitor id v pending = .ok (.Ok (), v', remaining) ∧
      Queued id rest v' ∧ ValidQueue id rest ∧
      remaining.val.Perm (rest.map Stream.Batch.Issued.batch_id) ∧
      remaining.length + 1 = pending.length := by
  have hqueue : queue ≠ [] := by
    intro he
    have := hids.length_eq
    simp [he] at this
    exact hnonempty this
  obtain ⟨issued, rest, after, v', hperm, hpoll, hrun, hv'⟩ := hp.poll id queue v hv hqueue
  have hm : issued ∈ queue := hperm.mem_iff.mp (by simp)
  obtain ⟨hmodule, hissued⟩ := hvalid issued hm
  obtain ⟨hid, hfinish⟩ := hissued.finished hrun
  have hids' : (issued.batch_id :: rest.map Stream.Batch.Issued.batch_id).Perm pending.val := by
    exact (hperm.map Stream.Batch.Issued.batch_id).trans hids.symm
  obtain ⟨remaining, hr, hremoved⟩ := stream.retire_code_batch.complete visitor id v v'
    pending after hpoll (hid.1.trans hmodule)
    (by rw [hid.2.1]; exact hids'.mem_iff.mp (by simp)) hfinish
  refine ⟨v', remaining, rest, hr, hv', ?_, ?_, ?_⟩
  · intro entry he
    exact hvalid entry (hperm.mem_iff.mp (by simp [he]))
  · rw [hid.2.1] at hremoved
    exact List.Perm.cons_inv (hremoved.trans hids'.symm)
  · have := hremoved.length_eq
    simp only [List.length_cons] at this
    exact this

/-- Draining a valid queue terminates successfully and leaves no queued work. -/
theorem drain_complete {V : Type} (visitor : stream.StreamingVisitor V)
    (config : stream.StreamingConfig) (Queued : U64 → List Stream.Batch.Issued → V → Prop)
    (hp : Accepts visitor config Queued) (id : U64)
    (queue : List Stream.Batch.Issued) (v : V) (pending : alloc.vec.Vec Usize)
    (hv : Queued id queue v) (hvalid : ValidQueue id queue)
    (hids : pending.val.Perm (queue.map Stream.Batch.Issued.batch_id)) :
    ∃ v' remaining,
      stream.retire_all_code_batches visitor id v pending = .ok (.Ok (), v', remaining) ∧
      remaining.val = [] ∧ Queued id [] v' := by
  generalize hn : pending.val.length = n
  induction n using Nat.strong_induction_on generalizing queue v pending with
  | h n ih =>
    by_cases hempty : pending.val = []
    · have hqueue : queue = [] := by
        have hl := hids.length_eq
        simp [hempty] at hl
        exact hl
      refine ⟨v, pending, ?_, hempty, by simpa [hqueue] using hv⟩
      rw [stream.retire_all_code_batches, stream.retire_all_code_batches_loop, loop]
      simp [stream.retire_all_code_batches_loop.body, alloc.vec.Vec.is_empty, hempty]
    · obtain ⟨v1, remaining, rest, hr, hv1, hrest, hids1, hlen⟩ :=
        retire_complete visitor config Queued hp id queue v pending hv hvalid hids hempty
      change remaining.val.length + 1 = pending.val.length at hlen
      obtain ⟨v', final, hrun, hnil, hv'⟩ := ih remaining.val.length (by omega)
        rest v1 remaining hv1 hrest hids1 rfl
      refine ⟨v', final, ?_, hnil, hv'⟩
      rw [stream.retire_all_code_batches, stream.retire_all_code_batches_loop, loop]
      have hnon : pending.val.isEmpty = false := by simpa using hempty
      simpa [stream.retire_all_code_batches_loop.body, alloc.vec.Vec.is_empty, hnon, hr,
        core.result.Result.Insts.CoreOpsTry.branch, stream.retire_all_code_batches,
        stream.retire_all_code_batches_loop] using hrun

end Itasca.Stream.Scheduler

end

/-! ## HeaderComplete -/

section

/-!
# Code section header completeness

`stream.read_code_header.complete`: an independently described code section header
(`Stream.Framing.HeaderAt`) over an available source is accepted. Only the bounded header view of at
most 11 bytes is read.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- A code region with a valid header (`Stream.Framing.HeaderAt`) is accepted by
`stream.read_code_header` over an available source. Only a view of at most 11 bytes is read, and
nonminimal LEB128 prefixes are accepted. An absent region and a present zero-entry section are
separate cases. -/
theorem stream.read_code_header.complete {S : Type} (source : stream.StreamingSource S) (state : S)
    (codeLen : Usize) (env : metadata.CodeMetadata) (entries : Usize) (data : Slice U8)
    (environment tail : List U8)
    (havailable : Stream.Source.Available source state environment data.val tail)
    (hsize : codeLen.val = data.length)
    (hbound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (imports : env.num_imported_funcs.val ≤ env.funcs.val.length)
    (hheader : Stream.Framing.HeaderAt data env entries) :
    stream.read_code_header source state codeLen env = .ok (.Ok entries) := by
  rcases hheader with ⟨hempty, rfl, hfuncs⟩ | ⟨count, hsection, hentries⟩
  · have hzero : codeLen = 0#usize := by
      apply UScalar.eq_of_val_eq
      simpa [Slice.length, hempty] using hsize
    simp [stream.read_code_header, hzero, env.num_func_defs_eq imports, show env.definedCount = 0#usize by apply UScalar.eq_of_val_eq; simp [hfuncs]]
  · obtain ⟨content, hsection, hcount, hcountval⟩ := hsection
    obtain ⟨pos, size, hbyte, hsizeDecoded, hend, _⟩ := hsection
    change Binary.Leb128.Decoded data content count entries at hcount
    change count.val = (Translation.Environment.definedTypeIndices env).length at hcountval
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
    have hsizeHeader : Binary.Leb128.Decoded header 1#usize size content :=
      hsizeDecoded.to_slice_view (by simp) hviewbound hview (by simp) (by simp) hsizeWithin
    have hcountHeader : Binary.Leb128.Decoded header content count entries :=
      hcount.to_slice_view (by simp) hviewbound hview (by simp) (by simp) hcountWithin
    have hbyteHeader := (Body.Scalar.BytesAt.of_slice_view (by simp) hviewbound hview).restrict
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
    have hcountEq : countLen = env.definedCount := by
      apply UScalar.eq_of_val_eq
      exact hcountlen.trans hcountval
    have hnotOver : entries.val ≤ codeLen.val := by omega
    simp only [viewEnd] at hexact
    simp [stream.read_code_header, hnonzero, Stream.Framing.header_limit, lift,
      hexact, core.result.Result.Insts.CoreOpsTry.branch, hindex, metadata.SECTION_CODE,
      hlenread, hfinish, hfinishEq, hcountread, env.num_func_defs_eq imports, hnotOver, hcountEq]

end Itasca

end

/-! ## DriverRegions -/

section

/-!
# Region certificates for streaming completeness

`Stream.CompleteRegions.prepare` derives, from independent premises about a module (bounded
encoding, signature limits, elaboration, `Module_ok` typing and module restrictions), a
`Stream.CompleteRegions.Certificate` for the canonical split of its bytes produced by
`stream.find_code_region`. The certificate gives the environment, code header and entries, tail,
and public metadata of the same raw module. It does not assume parser success or prevalidated
bodies. The file also transports independent encodings onto the split regions
(`Binary.At.on_region`).
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary

/-- An independent encoding of a complete region remains the same encoding
when that region is supplied as its own streaming buffer. -/
theorem At.on_region {α : Type} {R : α → List U8 → Prop}
    {data region : Slice U8} {start next : Usize} {value : α}
    (hregion : Body.Scalar.BytesAt data start region.val next)
    (h : At R data start value next) :
    At R region 0#usize value (Slice.len region) := by
  obtain ⟨bytes, he, hs⟩ := h
  refine ⟨bytes, he, hregion.restrict hs ?_ ?_ (Nat.le_refl _)⟩
  · simp
  · simpa using hregion.length

/-- Entries encoded within the implementation limits declare at most `limits.MAX_LOCALS` locals. -/
theorem Rep.locals_within_limits {entries bytes }
    (h : Rep (Itasca.CodeEntry.CodeEncodingWithinLimits ) entries bytes) :
    ∀ entry ∈ entries, entry.declared.length ≤ limits.MAX_LOCALS.val := by
  induction h with
  | nil => simp
  | @cons entry entries first rest he hs ih =>
    intro value hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact he.1
    · exact ih value hv

end Itasca.Binary

namespace Itasca.Module.Code

/-- Generated typing of the code entries in index order and the local-count limit give the entry
certificates that streaming batches use. -/
theorem EntriesTyped.of_forall₂ {env entries i }
    (ht : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry ) ((Translation.Environment.definedTypeIndices env).drop i) entries)
    (hb : ∀ entry ∈ entries, entry.declared.length ≤ limits.MAX_LOCALS.val) :
    EntriesTyped env i entries := by
  induction entries generalizing i with
  | nil => exact .nil _
  | cons entry entries ih =>
    have hlen := ht.length_eq
    have hi : i < (Translation.Environment.definedTypeIndices env).length := by
      simp only [List.length_drop, List.length_cons] at hlen
      omega
    rw [List.drop_eq_getElem_cons hi] at ht
    cases ht with
    | cons he hs =>
      exact .cons ⟨hi, he, hb _ (by simp)⟩
        (ih hs (fun value hv => hb value (by simp [hv])))

end Itasca.Module.Code

namespace Itasca.Stream.CompleteRegions

open Itasca.Binary Module.Elaboration

/-- A byte-span witness identifies the corresponding mathematical list slice. -/
theorem span_slice {data : Slice U8} {first last : Usize} {bytes : List U8}
    (span : Body.Scalar.BytesAt data first bytes last) :
    bytes = data.val.slice first.val last.val := by
  rw [List.slice, span.suffix]
  have length : last.val - first.val = bytes.length := by
    have exactLength := span.length
    omega
  simp only [length, List.take_left]

private theorem slice_spec (data : Slice U8) (first last : Usize)
    (hfirst : first.val ≤ last.val) (hlast : last.val ≤ data.length) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      data ⟨first, last⟩ ⦃ region => Body.Scalar.BytesAt data first region.val last ⦄ := by
  step
  apply Body.Scalar.BytesAt.of_slice_view hfirst hlast
  assumption

/-- Component completeness for the canonical streaming regions of an independently encoded,
elaborated, typed module. No assumption of parser or body success is made. -/
theorem prepare (data : Slice U8) (raw : Binary.Module)
    (hb : ModuleEncodingWithinLimits raw data.val )
    (hsignatures : ModuleSignaturesWithinLimits raw)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Restrictions raw ) :
    ∃ source env tail, Certificate data raw source env tail := by
  have hs := sections_of_typing he ht
  have hr := requirements_of_typing he hs hp.toModuleConditions hsignatures
  obtain ⟨decls, codePos, tailPos, hl⟩ := Module.normalize data raw hb
  have hsplit := stream.find_code_region.complete_layout hl
  obtain ⟨hcodePos, htailPos⟩ := stream.find_code_region.bounds data codePos tailPos hsplit
  obtain ⟨environment, henvSlice, henvSpan⟩ := WP.spec_imp_exists
    (slice_spec data 0#usize codePos (by simp) (by omega))
  obtain ⟨code, hcodeSlice, hcodeSpan⟩ := WP.spec_imp_exists
    (slice_spec data codePos tailPos hcodePos htailPos)
  obtain ⟨tailBytes, htailSlice, htailSpan⟩ := WP.spec_imp_exists
    (slice_spec data tailPos (Slice.len data) (by simpa using htailPos) (by simp))
  have henvEnc := hl.environment.on_region henvSpan
  obtain ⟨env, finalDecls, henv, hready⟩ := metadata.validate_env.complete
    environment raw decls (Slice.len environment) henvEnc hl.raw_eq (.inl rfl) hr
  have henvSize : environment.length ≤ limits.MAX_MODULE_BYTES.val := by
    have := henvSpan.length
    have := hb.1
    have := hl.environment.span.2
    simp only [Slice.length] at *
    omega
  obtain ⟨hbounds, hlimits⟩ := Module.Environment.accepted_entry_conditions
    environment env (Slice.len environment) henvSize henv
  have htailEnc := hl.tail.on_region htailSpan
  obtain ⟨segments, hsegments, hvalid⟩ := Module.Tail.materialize
    tailBytes 0#usize (Slice.len tailBytes) raw finalDecls env htailEnc hs hready
  have rawEq := hready.fromEnv_eq hsegments
  have hsemantic := metadata.validate_env.semantic_spec environment
  rw [henv] at hsemantic
  simp only [WP.spec_ok] at hsemantic
  obtain ⟨_, hrep, hv, flags, _, _, hprefix⟩ := hsemantic
  have hmatches := matches_from_env (codes := raw.codes) segments hready.represents hv flags hvalid
  rw [rawEq] at hmatches
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, validCount⟩ := hb.2
  have hguards := Binary.Source.dataCountValid.mp validCount
  have hdeclared : ∀ entry ∈ raw.codes, Spec.DeclaredReferences.Instructions
      (Translation.Environment.declaredReferences env.code) entry.body := by
    intro entry hm
    obtain ⟨j, hj, hjentry⟩ := List.mem_iff_getElem.mp hm
    have hidx : j < raw.functions.length := by rw [he.code_count]; exact hj
    have hfun : CodeEntry.function raw.functions[j] entry ∈
        List.zipWith CodeEntry.function raw.functions raw.codes := by
      apply List.mem_iff_getElem.mpr
      refine ⟨j, by simp only [List.length_zipWith]; omega, ?_⟩
      simp [List.getElem_zipWith, hjentry]
    have hd := hp.declared _ hfun
    apply hd.mono
    intro index hx
    exact (hmatches.refs index).mpr hx
  have hdataCount : ∀ count, env.code.data_count = some count → count.val = segments.val.length := by
    intro count hc
    have he : raw.dataCount = some count := (hready.data_count_eq (by decide)).symm.trans hc
    have hv := hguards
    simpa [DataCountValid, WebAssembly.Binary.DataCountValidWith, he, ← hsegments] using hv
  have htail := metadata.validate_tail.complete segments (by simpa [hsegments] using htailEnc) hvalid hdataCount
  have htypes := Module.CodeAt.typed hready hs hguards hdeclared
  have hcount : raw.codes.length = (Translation.Environment.definedTypeIndices env.code).length := htypes.length_eq.symm
  have hcode : ∃ entries, Stream.Framing.HeaderAt code env.code entries ∧
      At (Rep (Itasca.CodeEntry.CodeEncodingWithinLimits )) code entries raw.codes (Slice.len code) := by
    rcases hl.code with hcode | ⟨hempty, hsame, _⟩
    · have henc := hcode.on_region hcodeSpan
      obtain ⟨content, hheader, hpayload⟩ := henc.section_split
      obtain ⟨count, entries, hn, hdecoded, hentries⟩ := hpayload.vector_split
      exact ⟨entries, .inr ⟨count, ⟨content, hheader, hdecoded, hn.trans hcount⟩,
        hentries.span.1.trans hentries.span.2⟩, hentries⟩
    · have hzero : code.val = [] := by
        apply List.eq_nil_of_length_eq_zero
        have := hcodeSpan.length
        rw [hsame] at this
        omega
      have hfuncs : (Translation.Environment.definedTypeIndices env.code) = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa [hempty] using hcount.symm
      refine ⟨0#usize, .inl ⟨hzero, rfl, hfuncs⟩, [], ?_, ?_⟩
      · simpa [hempty] using (WebAssembly.Binary.Rep.nil : Rep (Itasca.CodeEntry.CodeEncodingWithinLimits ) [] [])
      · exact ⟨by simp [hzero], by simp [hzero], by simp⟩
  have htyped : Module.Code.EntriesTyped env.code 0 raw.codes := by
    obtain ⟨_, _, bytes, henc, _⟩ := hcode
    apply Module.Code.EntriesTyped.of_forall₂ (by simpa using htypes)
    exact Rep.locals_within_limits henc
  obtain ⟨bytes, hprefix, _⟩ := hprefix
  have hnames : ∀ entry ∈ env.exports.val, wf_name (Binary.nameOfBytes entry.name.val) := by
    intro entry hentry
    exact hprefix.export_names_wf (Module.Environment.rawExport entry)
      (by rw [hrep.exports]; exact List.mem_map.mpr ⟨entry, hentry, rfl⟩)
  have importBound : finalDecls.imports.length ≤ U32.max := by
    have lengths := congrArg List.length (hready.represents.imports.symm.trans hrep.imports)
    simp only [List.length_map] at lengths
    exact lengths ▸ hprefix.import_count_bound
  have hmeta := accessor_types segments hready.represents hv importBound hnames
    (codes := raw.codes) (segments := segments.val)
  rw [rawEq] at hmeta
  refine ⟨⟨environment, code, tailBytes⟩, env, segments, ?_⟩
  exact ⟨⟨codePos, tailPos, hsplit, henvSlice, hcodeSlice, htailSlice⟩,
    ⟨codePos, tailPos, hl.canonical, span_slice henvSpan, span_slice hcodeSpan, span_slice htailSpan⟩,
    by simpa using ((henvSpan.append hcodeSpan).append htailSpan).suffix,
    hb.1, henv, ⟨finalDecls, hready⟩, hbounds, hlimits, hcode, htyped, hcount,
    htail, hmatches, hmeta⟩

end Itasca.Stream.CompleteRegions

end

end

/-! ## Completeness -/

section

/-!
# Streaming completeness and synchronous embedding

Source-valid regions, an accepting queued scheduler and actual worker runs construct
successful streaming validation. The synchronous contiguous-source adapter discharges the
generic premises for whole-module validation.
-/

/-! ## SubmissionComplete -/

section

/-!
# Submission completeness

Completeness of `stream.submit_code_batches` over an available source and an accepting scheduler
(`Stream.Scheduler.Accepts`). `Stream.Submission.CompleteInvariant` pairs the remaining
independently encoded and typed entries with the scheduler's queue and the pending vector.
`stream.submit_code_batches.complete` shows that submission succeeds and leaves a valid queue
whose batch IDs are exactly the pending IDs, ready for the final drain. The argument applies to Wasm 2.0.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Code
/-- Typed entries of a concatenated list split into typed entries of each part. -/
theorem EntriesTyped.split {env i first second}
    (h : EntriesTyped env i (first ++ second)) :
    EntriesTyped env i first ∧ EntriesTyped env (i + first.length) second := by
  induction first generalizing i with
  | nil => exact ⟨.nil i, by simpa using h⟩
  | cons entry rest ih =>
    cases h with
    | cons he hs =>
      obtain ⟨hfirst, hsecond⟩ := ih hs
      exact ⟨.cons he hfirst, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsecond⟩

end Itasca.Module.Code

namespace Itasca.Stream.Submission
open Itasca.Binary Stream.Scheduler

/-- The scheduler's queue of valid work matches the pending vector, and the remaining bytes and
entries keep their independent encoding and typing. -/
def CompleteInvariant {V : Type} (Queued : U64 → List Stream.Batch.Issued → V → Prop)
    (code : Slice U8) (env : metadata.CodeMetadata) (id : U64) (config : stream.StreamingConfig)
    (v : V) (pending : alloc.vec.Vec Usize) (pos func batchId : Usize) : Prop :=
  batchId.val ≤ func.val ∧ pending.length ≤ batchId.val ∧ pending.length ≤ config.max_batches.val ∧
    ∃ queue entries, Queued id queue v ∧ ValidQueue id queue ∧
      pending.val.Perm (queue.map Stream.Batch.Issued.batch_id) ∧
      func.val + entries.length = (Translation.Environment.definedTypeIndices env).length ∧
      Module.Code.EntriesTyped env func.val entries ∧
      At (Rep (CodeEntry.CodeEncodingWithinLimits )) code pos entries (Slice.len code)

/-- A successful submission leaves a valid queue whose batch IDs are a permutation of the pending
IDs, so the final drain can retire exactly this queue. Errors are excluded. -/
def CompletePost {V : Type} (Queued : U64 → List Stream.Batch.Issued → V → Prop)
    (id : U64) (config : stream.StreamingConfig) :
    (core.result.Result (alloc.vec.Vec Usize) error.Error × V) → Prop
  | (.Ok pending, v) => ∃ queue, Queued id queue v ∧ ValidQueue id queue ∧
      pending.val.Perm (queue.map Stream.Batch.Issued.batch_id) ∧ pending.length ≤ config.max_batches.val
  | (.Err _, _) => False

private def CompleteBodyPost {V : Type} (Queued : U64 → List Stream.Batch.Issued → V → Prop)
    (code : Slice U8) (env : metadata.CodeMetadata) (id : U64) (config : stream.StreamingConfig) (func : Usize) :
    ControlFlow (V × alloc.vec.Vec Usize × Usize × Usize × Usize)
      (core.result.Result (alloc.vec.Vec Usize) error.Error × V) → Prop
  | .done result => CompletePost Queued id config result
  | .cont (v, pending, pos, next, batchId) =>
      CompleteInvariant Queued code env id config v pending pos next batchId ∧ func.val < next.val

private theorem increment (n bound : Usize) (h : n.val < bound.val) :
    ∃ next, (n + 1#usize : Result Usize) = .ok next ∧ next.val = n.val + 1 := by
  obtain ⟨next, hr, hv⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x := n) (y := 1#usize) (by scalar_tac))
  exact ⟨next, hr, by simpa using hv⟩

private theorem resume_complete {S V : Type} (source : stream.StreamingSource S)
    (visitor : stream.StreamingVisitor V) (Queued : U64 → List Stream.Batch.Issued → V → Prop)
    (config : stream.StreamingConfig) (ha : Accepts visitor config Queued )
    (state : S) (moduleId : U64) (env : metadata.CodeMetadata) (code : Slice U8)
    (environment tail : List U8) (hs : Stream.Source.Available source state environment code.val tail)
    (henv : CodeEntry.Bounds env)
    (hlimits : CodeEntry.EnvironmentWithinLimits env)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (v : V) (pending : alloc.vec.Vec Usize) (pos func batchId : Usize)
    (queue : List Stream.Batch.Issued) (entries : List Code)
    (hv : Queued moduleId queue v) (hq : ValidQueue moduleId queue )
    (hp : pending.val.Perm (queue.map Stream.Batch.Issued.batch_id))
    (hcount : func.val + entries.length = (Translation.Environment.definedTypeIndices env).length)
    (htyped : Module.Code.EntriesTyped env func.val entries)
    (hbytes : At (Rep (CodeEntry.CodeEncodingWithinLimits )) code pos entries (Slice.len code))
    (hbatch : batchId.val ≤ func.val) (hpending : pending.length ≤ batchId.val)
    (hfunc : func.val < (Translation.Environment.definedTypeIndices env).length)
    (hroom : pending.length < config.max_batches.val) :
    (do
      let r ← stream.get_next_batch source state (Slice.len code) pos func (env.definedCount) config.batch_bytes
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let (finish, next) := val
        let r1 ← stream.read_exact source state pos finish
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue bytes =>
          let pending1 ← alloc.vec.Vec.push pending batchId
          let shared ← stream.share_code env
          let count ← next - func
          let (r2, v') ← visitor.submit_code_batch v
            { module_id := moduleId, batch_id := batchId, env := shared, code := bytes,
              code_offset := pos, first_func := func, num_funcs := count,
              num_dispatched := 0#usize, dispatch_end := 0#usize,
              num_validated := 0#usize, validated_end := 0#usize, error := none }
          let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
          match cf2 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let nextId ← batchId + 1#usize
            Result.ok (ControlFlow.cont (v', pending1, finish, next, nextId))
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r3 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              (alloc.vec.Vec Usize) (core.convert.FromSame error.Error) residual
            Result.ok (ControlFlow.done (r3, v'))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (alloc.vec.Vec Usize) (core.convert.FromSame error.Error) residual
          Result.ok (ControlFlow.done (r2, v))
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          (alloc.vec.Vec Usize) (core.convert.FromSame error.Error) residual
        Result.ok (ControlFlow.done (r1, v))) ⦃ out => CompleteBodyPost Queued code env moduleId config func out ⦄ := by
  obtain ⟨finish, next, taken, rest, view, hframe, hframepost, heq, hne, hnext, hrestcount,
      htakenbytes, hrestbytes, hread, hspan, hrep⟩ := stream.get_next_batch.complete_view source state
    environment tail code hs (Slice.len code) pos func (env.definedCount)
    config.batch_bytes entries rfl (by simpa using hcap) (by simpa using hfunc)
    (by simpa using hcount) hbytes
  obtain ⟨hprogress, hfinishbound, hnextprogress, hnextbound⟩ := hframepost
  rw [heq] at htyped
  obtain ⟨htaken, hrest⟩ := htyped.split
  have hnexttyped : Module.Code.EntriesTyped env next.val rest := by simpa [hnext] using hrest
  obtain ⟨nextPending, hpush, hpushval⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec pending batchId (by scalar_tac))
  obtain ⟨count, hsub, hsubval⟩ := WP.spec_imp_exists
    (UScalar.sub_spec (x := next) (y := func) (by scalar_tac))
  have hcountval : count.val = taken.length := by omega
  let issued : Stream.Batch.Issued := ⟨moduleId, batchId, env, view, pos, func, count⟩
  have hbounded : issued.Bounded := by
    have hlen := hspan.length
    change finish.val = pos.val + view.length at hlen
    dsimp [issued, Stream.Batch.Issued.Bounded]
    have hfunctions : next.val ≤ (Translation.Environment.definedTypeIndices env).length := by simpa using hnextbound
    have hfinishcap : finish.val ≤ limits.MAX_MODULE_BYTES.val :=
      le_trans (by simpa using hfinishbound) hcap
    simp only [Slice.length] at hlen ⊢
    omega
  have hvalid : Valid issued :=
    ⟨hbounded, henv, hlimits, taken, hcountval.symm, htaken, hrep⟩
  have hqueuelen : queue.length = pending.length := by
    simpa [alloc.vec.Vec.length] using hp.length_eq.symm
  obtain ⟨v', hsubmit, hv'⟩ := ha.submit moduleId queue issued v hv hvalid.bounded hvalid.entry_bounds rfl (by omega)
  obtain ⟨nextId, hinc, hnextId⟩ := increment batchId (env.definedCount)
    (by simpa using (show batchId.val < (Translation.Environment.definedTypeIndices env).length by omega))
  simp only [issued, Stream.Batch.Issued.seed] at hsubmit
  simp [hframe, core.result.Result.Insts.CoreOpsTry.branch, hread, hpush, stream.share_code, hsub, hsubmit, hinc]
  change CompleteInvariant Queued code env moduleId config v' nextPending finish next nextId ∧ _
  constructor
  · refine ⟨by omega, ?_, ?_, queue ++ [issued], rest, hv', ?_, ?_, ?_, hnexttyped, hrestbytes⟩
    · change nextPending.val.length ≤ _
      rw [hpushval, List.length_append, List.length_singleton]
      change pending.val.length ≤ _ at hpending
      omega
    · change nextPending.val.length ≤ _
      rw [hpushval, List.length_append, List.length_singleton]
      change pending.val.length < _ at hroom
      omega
    · intro old hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hq old hm
      · have he : old = issued := by simpa using hm
        exact he ▸ ⟨rfl, hvalid⟩
    · rw [hpushval, List.map_append, List.map_cons, List.map_nil]
      exact hp.append_right [batchId]
    · simpa using hrestcount.symm
  · simpa using hnextprogress

end Itasca.Stream.Submission

namespace Itasca.Stream.Submission
open Itasca.Binary Stream.Scheduler

private theorem body_complete {S V : Type} (source : stream.StreamingSource S)
    (visitor : stream.StreamingVisitor V) (Queued : U64 → List Stream.Batch.Issued → V → Prop)
    (config : stream.StreamingConfig) (ha : Accepts visitor config Queued )
    (state : S) (moduleId : U64) (env : metadata.CodeMetadata) (code : Slice U8)
    (environment tail : List U8) (hs : Stream.Source.Available source state environment code.val tail)
    (henv : CodeEntry.Bounds env)
    (hlimits : CodeEntry.EnvironmentWithinLimits env)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (v : V) (pending : alloc.vec.Vec Usize) (pos func batchId : Usize)
    (hinv : CompleteInvariant Queued code env moduleId config v pending pos func batchId) :
    stream.submit_code_batches_loop.body source visitor moduleId state env
      (Slice.len code) config (env.definedCount) v pending pos func batchId
        ⦃ CompleteBodyPost Queued code env moduleId config func ⦄ := by
  obtain ⟨hbatch, hpending, hmax, queue, entries, hv, hq, hp, hcount, htyped, hbytes⟩ := hinv
  unfold stream.submit_code_batches_loop.body
  by_cases hmore : func < env.definedCount
  · rw [if_pos hmore]
    have hfunc : func.val < (Translation.Environment.definedTypeIndices env).length := by simpa using hmore
    by_cases hfull : alloc.vec.Vec.len pending ≥ config.max_batches
    · rw [if_pos hfull]
      have hnonempty : pending.val ≠ [] := by
        intro he
        have hz : pending.length = 0 := by simp [alloc.vec.Vec.length, he]
        have hp := ha.capacity_positive
        have hge : config.max_batches.val ≤ pending.length := by simpa using hfull
        omega
      obtain ⟨v', remaining, rest, hr, hv', hvalid, hids, hlen⟩ :=
        retire_complete visitor config Queued ha moduleId queue v pending hv hq hp hnonempty
      rw [hr]
      simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
      have hresume := resume_complete source visitor Queued config ha state moduleId env code
        environment tail hs henv hlimits hcap v' remaining pos func batchId rest entries
        hv' hvalid hids hcount htyped hbytes hbatch (by omega) hfunc (by omega)
      simp [core.result.Result.Insts.CoreOpsTry.branch] at hresume ⊢
      convert hresume using 1
      rfl
    · rw [if_neg hfull]
      exact resume_complete source visitor Queued config ha state moduleId env code
        environment tail hs henv hlimits hcap v pending pos func batchId queue entries
        hv hq hp hcount htyped hbytes hbatch hpending hfunc (by scalar_tac)
  · rw [if_neg hmore]
    have hn : (Translation.Environment.definedTypeIndices env).length ≤ func.val := by scalar_tac
    have he : entries = [] := by simpa using (show entries.length = 0 by omega)
    subst entries
    have hpos : pos = Slice.len code := hbytes.rep_nil.symm
    simp only [hpos, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨queue, hv, hq, hp, hmax⟩

end Itasca.Stream.Submission

namespace Itasca
open Itasca.Binary Stream.Scheduler

/-- The submission loop accepts independently encoded and typed entries, maintaining the queue of
outstanding work as its function cursor advances. -/
theorem stream.submit_code_batches_loop.complete_spec {S V : Type} (source : stream.StreamingSource S)
    (visitor : stream.StreamingVisitor V) (Queued : U64 → List Stream.Batch.Issued → V → Prop)
    (config : stream.StreamingConfig) (ha : Accepts visitor config Queued )
    (state : S) (moduleId : U64) (env : metadata.CodeMetadata) (code : Slice U8)
    (environment tail : List U8) (hs : Stream.Source.Available source state environment code.val tail)
    (henv : CodeEntry.Bounds env)
    (hlimits : CodeEntry.EnvironmentWithinLimits env)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (v : V) (pending : alloc.vec.Vec Usize) (pos func batchId : Usize)
    (hinv : Stream.Submission.CompleteInvariant Queued code env moduleId config v pending pos func batchId) :
    stream.submit_code_batches_loop source visitor moduleId state env
      (Slice.len code) config v pending pos func batchId (env.definedCount)
        ⦃ Stream.Submission.CompletePost Queued moduleId config ⦄ := by
  unfold stream.submit_code_batches_loop
  apply loop.spec_decr_nat (fun s => (Translation.Environment.definedTypeIndices env).length - s.2.2.2.1.val)
    (fun s => Stream.Submission.CompleteInvariant Queued code env moduleId config
      s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2)
  · rintro ⟨v', pending', pos', func', batchId'⟩ h
    apply WP.spec_mono (Stream.Submission.body_complete source visitor Queued config ha state moduleId env
      code environment tail hs henv hlimits hcap v' pending' pos' func' batchId' h)
    intro out hout
    cases out with
    | done result => exact hout
    | cont next =>
      obtain ⟨v'', pending'', pos'', func'', batchId''⟩ := next
      obtain ⟨hinv'', hprogress⟩ := hout
      refine ⟨hinv'', ?_⟩
      obtain ⟨_, _, _, queue, entries, _, _, _, hcount, _, _⟩ := hinv''
      dsimp only
      omega
  · exact hinv

/-- From an independently encoded and typed code region and an accepting scheduler policy,
`stream.submit_code_batches` submits and retires batches successfully. The remaining valid queue
matches the pending IDs for the final drain. -/
theorem stream.submit_code_batches.complete {S V : Type} (source : stream.StreamingSource S)
    (visitor : stream.StreamingVisitor V) (Queued : U64 → List Stream.Batch.Issued → V → Prop)
    (config : stream.StreamingConfig) (ha : Accepts visitor config Queued )
    (state : S) (moduleId : U64) (env : metadata.CodeMetadata) (code : Slice U8) (start : Usize)
    (environment tail : List U8) (hs : Stream.Source.Available source state environment code.val tail)
    (henv : CodeEntry.Bounds env)
    (hlimits : CodeEntry.EnvironmentWithinLimits env)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (entries : List Code) (hcount : entries.length = (Translation.Environment.definedTypeIndices env).length)
    (htyped : Module.Code.EntriesTyped env 0 entries)
    (hbytes : At (Rep (CodeEntry.CodeEncodingWithinLimits )) code start entries (Slice.len code))
    (v : V) (hv : Queued moduleId [] v) :
    ∃ pending v' queue,
      stream.submit_code_batches source visitor moduleId state env (Slice.len code) start config v =
        .ok (.Ok pending, v') ∧ Queued moduleId queue v' ∧ ValidQueue moduleId queue ∧
      pending.val.Perm (queue.map Stream.Batch.Issued.batch_id) ∧
      pending.length ≤ config.max_batches.val := by
  have hi : Stream.Submission.CompleteInvariant Queued code env moduleId config v
      (alloc.vec.Vec.new _) start 0#usize 0#usize := by
    refine ⟨by simp, by simp [alloc.vec.Vec.new], by simp [alloc.vec.Vec.new],
      [], entries, hv, ?_, ?_, by simpa using hcount, htyped, hbytes⟩
    · simp [ValidQueue]
    · simp [alloc.vec.Vec.new]
  obtain ⟨⟨r, v'⟩, hr, hp⟩ := WP.spec_imp_exists
    (stream.submit_code_batches_loop.complete_spec source visitor Queued config ha state moduleId env code
      environment tail hs henv hlimits hcap v (alloc.vec.Vec.new _) start 0#usize 0#usize hi)
  cases r with
  | Err e => exact False.elim hp
  | Ok pending =>
    obtain ⟨queue, hv', hvalid, hids, hmax⟩ := hp
    exact ⟨pending, v', queue, by simpa only [stream.submit_code_batches, alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, env.num_func_defs_eq henv.1, bind_ok] using hr, hv', hvalid, hids, hmax⟩

end Itasca

end

/-! ## DriverComplete -/

section

/-!
# Streaming driver completeness

`stream.validate_streaming.complete_core`: an independently encoded, elaborated and typed
module within the implementation limits is accepted by `stream.validate_streaming`, provided
the source makes the canonical split of the input available (`Stream.Source.CanonicalAvailable`)
and the scheduler is accepting (`Stream.Scheduler.Accepts`). The returned descriptors and data segments describe the raw module
(`Matches`, `AccessorTypes`). Both premises on the embedding are required: completeness fails if
reads are unavailable or workers do not accept. `Itasca/Results/Stream` states the public
`complete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Stream.Run
/-- The recorded phase calls compose to the returned metadata. -/
theorem Accepted.run {S V : Type} {source : stream.StreamingSource S}
    {visitor : stream.StreamingVisitor V} {id state before after env}
    (h : Accepted source visitor id state before after env) :
    stream.validate_streaming source visitor id state before = .ok (.Ok env, after) := by
  obtain ⟨_, shared, same⟩ := WP.spec_imp_exists (metadata.ModuleMetadataCodeMetadata.share.spec h.decodedPrefix)
  rw [same] at shared
  simp [stream.validate_streaming, h.environment_call, h.environment_bound, h.region_call,
    h.decode_environment, shared, alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref,
    h.remaining.length_call, h.remaining.code_bound, h.remaining.header_call,
    h.remaining.configured_call, h.remaining.batch_bytes_positive, h.remaining.max_batches_positive,
    h.remaining.submit_call, h.remaining.end_call, h.remaining.tail_call, h.remaining.module_bound,
    h.remaining.region_call, h.remaining.decode_tail, h.remaining.drain_call, h.published,
    core.result.Result.Insts.CoreOpsTry.branch]

end Itasca.Stream.Run

namespace Itasca.Stream.CompleteRegions
/-- The concrete splitter and slice operations determine a unique source. -/
theorem ComputedSplit.unique {data : Slice U8} {first second : stream.SliceSource}
    (hfirst : ComputedSplit data first) (hsecond : ComputedSplit data second) : first = second := by
  obtain ⟨a, b, hs, he, hc, ht⟩ := hfirst
  obtain ⟨a', b', hs', he', hc', ht'⟩ := hsecond
  have hb : a = a' ∧ b = b' := by simpa using hs.symm.trans hs'
  obtain ⟨rfl, rfl⟩ := hb
  have heq : first.env = second.env := by simpa using he.symm.trans he'
  have hcq : first.code = second.code := by simpa using hc.symm.trans hc'
  have htq : first.tail = second.tail := by simpa using ht.symm.trans ht'
  cases first
  cases second
  simp_all

end Itasca.Stream.CompleteRegions

namespace Itasca.Stream.Source

/-- Canonical availability transfers to any split of `data` produced by the splitter. -/
theorem CanonicalAvailable.for_split {S : Type} {source : stream.StreamingSource S} {state data regions}
    (h : CanonicalAvailable source state data) (hsplit : Stream.CompleteRegions.Split data regions) :
    Available source state regions.env.val regions.code.val regions.tail.val := by
  obtain ⟨other, hother, ha⟩ := h
  rw [hsplit.computed.unique hother.computed]
  exact ha

end Itasca.Stream.Source

namespace Itasca.Stream.CompleteRegions
open Stream.Scheduler

private theorem remaining_of_submission {S V : Type} (source : stream.StreamingSource S)
    (visitor : stream.StreamingVisitor V) (config : stream.StreamingConfig)
    (Queued : U64 → List Stream.Batch.Issued → V → Prop)
    (hp : Accepts visitor config Queued ) (id : U64) (state : S)
    (data : Slice U8) (raw : Binary.Module) (regions : stream.SliceSource)
    (env : metadata.ModuleMetadata metadata.CodeMetadata) (tail : alloc.vec.Vec metadata.Data) (hc : Certificate data raw regions env tail )
    (ha : Stream.Source.Available source state regions.env.val regions.code.val regions.tail.val)
    (before configured submitted : V) (entries : Usize) (codeEnd : Usize)
    (pending : alloc.vec.Vec Usize) (queue : List Stream.Batch.Issued)
    (hlen : source.code_len state = .ok (Slice.len regions.code))
    (hbound : limits.add_offset (Slice.len regions.env) (Slice.len regions.code) = .ok (.Ok codeEnd))
    (hend : codeEnd.val = regions.env.length + regions.code.length)
    (hheader : stream.read_code_header source state (Slice.len regions.code) env.code = .ok (.Ok entries))
    (hconfig : visitor.environment_ready before env = .ok (.Ok config, configured))
    (hsubmit : stream.submit_code_batches source visitor id state env.code (Slice.len regions.code)
      entries config configured = .ok (.Ok pending, submitted))
    (hv : Queued id queue submitted) (hq : ValidQueue id queue )
    (hids : pending.val.Perm (queue.map Stream.Batch.Issued.batch_id)) :
    ∃ after, ∃ run : Stream.Run.Remaining source visitor id state env (Slice.len regions.env) before after ,
      run.tail = tail ∧ Queued id [] after := by
  obtain ⟨ended, he, hve⟩ := hp.code_end id queue submitted hv
  obtain ⟨bytes, hread, hbytes⟩ := ha.tail_read
  have heq : bytes = regions.tail := Slice.ext _ _ hbytes
  subst bytes
  have hwhole : codeEnd.val + regions.tail.length ≤ limits.MAX_MODULE_BYTES.val := by
    have hh := congrArg List.length hc.bytes
    have hb := hc.bounded
    simp only [List.length_append, Slice.length] at hh hb hend ⊢
    omega
  obtain ⟨moduleEnd, hmodule, _⟩ := limits.add_offset.complete codeEnd (Slice.len regions.tail)
    (by simpa using hwhole)
  obtain ⟨region, hr, hvr⟩ := hp.region id queue ended .Tail hve
  obtain ⟨decoded, hd⟩ := metadata.validate_tail_with.accepted_lift
    visitor.metadataModuleVisitorInst hp.custom_accepts regions.tail 0#usize env.code region tail hc.tail_accepted
  have hvd := metadata.validate_tail_with.accepted_invariant visitor.metadataModuleVisitorInst
    (Queued id queue) (hp.custom_preserves id queue) regions.tail 0#usize env.code region tail decoded hd hvr
  obtain ⟨after, remaining, hfinish, _, hva⟩ :=
    drain_complete visitor config Queued hp id queue decoded pending hvd hq hids
  refine ⟨after, ⟨Slice.len regions.code, codeEnd, entries, config, configured, pending,
    submitted, ended, regions.tail, moduleEnd, region, tail, decoded, remaining,
    hlen, hbound, hheader, hconfig, ?_, ?_, hsubmit, he, hread, hmodule, hr, hd, hfinish⟩,
    rfl, hva⟩
  · have := hp.batch_positive
    scalar_tac
  · have := hp.capacity_positive
    scalar_tac

end Itasca.Stream.CompleteRegions

namespace Itasca.Stream.CompleteRegions
open Stream.Scheduler

/-- Independent region certificates drive every phase after the environment, including workers
retired in any order and data segments parsed from the tail. -/
theorem remaining_complete {S V : Type} (source : stream.StreamingSource S)
    (visitor : stream.StreamingVisitor V) (config : stream.StreamingConfig)
    (Queued : U64 → List Stream.Batch.Issued → V → Prop)
    (hp : Accepts visitor config Queued ) (id : U64) (state : S)
    (data : Slice U8) (raw : Binary.Module) (regions : stream.SliceSource)
    (env : metadata.ModuleMetadata metadata.CodeMetadata) (tail : alloc.vec.Vec metadata.Data) (hc : Certificate data raw regions env tail )
    (ha : Stream.Source.Available source state regions.env.val regions.code.val regions.tail.val)
    (before : V) (hv : Queued id [] before) :
    ∃ after, ∃ run : Stream.Run.Remaining source visitor id state env (Slice.len regions.env) before after ,
      run.tail = tail ∧ Queued id [] after := by
  obtain ⟨len, hlen, hlenval⟩ := ha.code_len_read
  have hlenEq : len = Slice.len regions.code := UScalar.eq_of_val_eq hlenval
  subst len
  have hcap : regions.env.length + regions.code.length ≤ limits.MAX_MODULE_BYTES.val := by
    have hh := congrArg List.length hc.bytes
    have hb := hc.bounded
    simp only [List.length_append, Slice.length] at hh hb ⊢
    omega
  have hcodeCap : regions.code.length ≤ limits.MAX_MODULE_BYTES.val := by omega
  obtain ⟨codeEnd, hbound, hend⟩ := limits.add_offset.complete
    (Slice.len regions.env) (Slice.len regions.code) (by simpa using hcap)
  obtain ⟨entries, hheader, hbytes⟩ := hc.code
  have hheaderRun := stream.read_code_header.complete source state (Slice.len regions.code)
    env.code entries regions.code regions.env.val regions.tail.val ha rfl hcodeCap hc.entry_bounds.1 hheader
  obtain ⟨configured, hconfig, hconfigured⟩ := hp.environment id [] before env hv
  obtain ⟨pending, submitted, queue, hsubmit, hqueued, hvalid, hids, _⟩ :=
    stream.submit_code_batches.complete source visitor Queued config hp state id env.code regions.code
      entries regions.env.val regions.tail.val ha hc.entry_bounds hc.signature_limits hcodeCap
      raw.codes hc.code_count hc.typed hbytes configured hconfigured
  exact remaining_of_submission source visitor config Queued hp id state data raw regions env tail
    hc ha before configured submitted entries codeEnd pending queue hlen hbound
    (by simpa using hend) hheaderRun hconfig hsubmit hqueued hvalid hids

/-- `stream.validate_streaming` accepts the regions of a `Certificate`. The returned module contains the certified data segments. -/
theorem complete_certificate {S V : Type} (source : stream.StreamingSource S)
    (visitor : stream.StreamingVisitor V) (config : stream.StreamingConfig)
    (Queued : U64 → List Stream.Batch.Issued → V → Prop)
    (hp : Accepts visitor config Queued ) (id : U64) (state : S)
    (data : Slice U8) (raw : Binary.Module) (regions : stream.SliceSource)
    (env : metadata.ModuleMetadata metadata.CodeMetadata) (tail : alloc.vec.Vec metadata.Data) (hc : Certificate data raw regions env tail )
    (ha : Stream.Source.Available source state regions.env.val regions.code.val regions.tail.val)
    (before : V) (hv : Queued id [] before) :
    ∃ after, ∃ run : Stream.Run.Accepted source visitor id state before after {env with data := tail} ,
      stream.validate_streaming source visitor id state before = .ok (.Ok {env with data := tail}, after) ∧
      run.remaining.tail = tail ∧ Queued id [] after := by
  obtain ⟨bytes, hread, hbytes⟩ := ha.environment_read
  have heq : bytes = regions.env := Slice.ext _ _ hbytes
  subst bytes
  have hcap : regions.env.length ≤ limits.MAX_MODULE_BYTES.val := by
    have hh := congrArg List.length hc.bytes
    have hb := hc.bounded
    simp only [List.length_append, Slice.length] at hh hb ⊢
    omega
  obtain ⟨envLen, hbound, hlen⟩ := limits.add_offset.complete 0#usize (Slice.len regions.env)
    (by simpa using hcap)
  have hlenEq : envLen = Slice.len regions.env := by apply UScalar.eq_of_val_eq; simpa using hlen
  subst envLen
  obtain ⟨region, hregion, hvregion⟩ := hp.region id [] before .Environment hv
  obtain ⟨decoded, hdecode⟩ := metadata.validate_env_with.accepted_lift
    visitor.metadataModuleVisitorInst hp.custom_accepts regions.env region env
    (Slice.len regions.env) hc.environment
  have hvdecoded := metadata.validate_env_with.accepted_invariant visitor.metadataModuleVisitorInst
    (Queued id []) (hp.custom_preserves id []) regions.env region env (Slice.len regions.env)
    decoded hdecode hvregion
  obtain ⟨after, remaining, htail, hvafter⟩ := remaining_complete source visitor config Queued hp
    id state data raw regions env tail hc ha decoded hvdecoded
  let run : Stream.Run.Accepted source visitor id state before after {env with data := tail} :=
    ⟨regions.env, Slice.len regions.env, env, region, decoded, hread, hbound, hregion, hdecode, remaining, by rw [htail]⟩
  exact ⟨after, run, run.run, htail, hvafter⟩

end Itasca.Stream.CompleteRegions

namespace Itasca
open Itasca.Binary Module.Elaboration

/-- Independently encoded, elaborated, typed modules within the implementation limits are
accepted by `stream.validate_streaming` under canonical available reads and an accepting
scheduler. The returned descriptors and data segments match the raw module. -/
theorem stream.validate_streaming.complete_core {S V : Type}
    (source : stream.StreamingSource S) (visitor : stream.StreamingVisitor V)
    (config : stream.StreamingConfig) (Queued : U64 → List Stream.Batch.Issued → V → Prop)
    (ha : Stream.Scheduler.Accepts visitor config Queued )
    (id : U64) (state : S) (before : V)
    (data : Slice U8) (raw : Binary.Module)
    (hb : ModuleEncodingWithinLimits raw data.val )
    (hsignatures : ModuleSignaturesWithinLimits raw)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Restrictions raw )
    (hs : Stream.Source.CanonicalAvailable source state data) (hv : Queued id [] before) :
    ∃ env after, ∃ run : Stream.Run.Accepted source visitor id state before after env ,
      stream.validate_streaming source visitor id state before = .ok (.Ok env, after) ∧
      Matches env raw ∧ AccessorTypes env raw ∧ Queued id [] after := by
  obtain ⟨regions, env, tail, hc⟩ := Stream.CompleteRegions.prepare data raw hb hsignatures he ht hp
  obtain ⟨after, run, hrun, htail, hvafter⟩ := Stream.CompleteRegions.complete_certificate
    source visitor config Queued ha id state data raw regions env tail hc
    (hs.for_split hc.canonical) before hv
  exact ⟨_, after, run, hrun, hc.realization, hc.metadata, hvafter⟩

end Itasca

end

/-! ## Sync -/

section

/-!
# Synchronous worker

The private synchronous scheduler `stream.SyncVisitor` that `validate_module` supplies to the
driver. It has one `completed` slot: submission runs `stream.StreamingBatch.validate_all` on the seed
immediately and stores the result, and polling takes it. `Stream.Sync.provenance` and
`Stream.Sync.callbacks_total` show that it meets the `Stream.Scheduler.Provenance` and
`Stream.Scheduler.CallbacksTotal` contracts for module validation, so no embedding obligation remains
for it.
-/

open Aeneas Aeneas.Std

namespace Itasca.Stream.Sync

local notation "sync" => stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor

/-- The stored worker is reachable from every historical issued batch matching its identity. The
invariant does not assume that the worker has finished. -/
def Tracks (_id : U64) (history : List Stream.Batch.Issued) (state : stream.SyncVisitor) : Prop :=
  ∀ batch, state.completed = some batch → ∀ issued ∈ history,
    issued.module_id = batch.module_id → issued.batch_id = batch.batch_id →
    Stream.Batch.Reachable issued batch

theorem tracks_empty (id : U64) (state : stream.SyncVisitor) : Tracks id [] state := by
  simp [Tracks]

theorem tracks_cleared (id : U64) (history : List Stream.Batch.Issued) (state : stream.SyncVisitor)
    (h : state.completed = none) : Tracks id history state := by
  simp [Tracks, h]

/-- Polling takes the stored worker out of the completed slot. -/
theorem poll_some (state : stream.SyncVisitor) (batch : stream.StreamingBatch)
    (h : state.completed = some batch) :
    (sync).poll_code_batch state = .ok (.Ok batch, { state with completed := none }) := by
  simp [stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor.poll_code_batch,
    core.option.Option.take, h]

theorem poll_none (state : stream.SyncVisitor) (h : state.completed = none) :
    (sync).poll_code_batch state = .ok (.Err .Host, { state with completed := none }) := by
  simp [stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor.poll_code_batch,
    core.option.Option.take, h]

theorem poll_accepted (state after : stream.SyncVisitor) (batch : stream.StreamingBatch)
    (h : (sync).poll_code_batch state = .ok (.Ok batch, after)) :
    state.completed = some batch ∧ after = { state with completed := none } := by
  cases he : state.completed with
  | none => rw [poll_none state he] at h; simp at h
  | some current =>
    rw [poll_some state current he] at h
    have hh : current = batch ∧ { state with completed := none } = after := by simpa using h
    exact ⟨by simp [hh.1], hh.2.symm⟩

theorem poll_total : Stream.Retirement.PollTotal sync := by
  intro state
  cases he : state.completed with
  | none => exact ⟨_, poll_none state he⟩
  | some batch => exact ⟨_, poll_some state batch he⟩

theorem environment_ready (state : stream.SyncVisitor) (env : metadata.ModuleMetadata metadata.CodeMetadata) :
    (sync).environment_ready state env =
      .ok (.Ok { batch_bytes := 25000#usize, max_batches := 1#usize }, state) := rfl

theorem custom_accepts : Module.Tail.HooksAccept (sync).metadataModuleVisitorInst := by
  intro state chunk
  exact ⟨state, rfl⟩

theorem custom_region (state : stream.SyncVisitor) (region : stream.StreamingRegion) :
    (sync).custom_region state region = .ok state := rfl

theorem code_end (state : stream.SyncVisitor) :
    (sync).code_end state = .ok (.Ok (), state) := rfl

/-- Submission runs the extracted worker even on malformed bytes and stores its reachable result.
Submission succeeding does not mean that `stream.StreamingBatch.finish` passes. -/
theorem submit (state : stream.SyncVisitor) (issued : Stream.Batch.Issued)
    (hissued : issued.Bounded) (hbound : CodeEntry.Bounds issued.env) :
    ∃ batch, (sync).submit_code_batch state issued.seed =
      .ok (.Ok (), { state with completed := some batch }) ∧
      Stream.Batch.Reachable issued batch := by
  obtain ⟨batch, hr, hp⟩ := WP.spec_imp_exists
    (stream.StreamingBatch.validate_all.reachable issued issued.seed hissued hbound .seed)
  exact ⟨batch, by simp [stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor.submit_code_batch, hr], hp⟩

/-- The synchronous scheduler satisfies `Stream.Scheduler.Provenance` across every callback,
including callbacks from the tail parser. -/
theorem provenance : Stream.Scheduler.Provenance sync Tracks := by
  constructor
  · intro id history state chunk after hcall
    have he : state = after := by
      simpa [stream.SyncVisitor.Insts.ItascaMetadataModuleVisitor,
        metadata.ModuleVisitor.on_custom_section.default] using hcall
    subst after
    exact fun h => h
  · intro id history state region after hs hcall
    have he : state = after := by
      simpa [stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor.custom_region] using hcall
    exact he ▸ hs
  · intro id history state env config after hs hcall
    rw [environment_ready] at hcall
    simp only [Result.ok.injEq, Prod.mk.injEq] at hcall
    exact hcall.2 ▸ hs
  · intro id history issued state after _ _ hissued hbound hfresh hcall
    obtain ⟨batch, hr, hreach⟩ := submit state issued hissued hbound
    rw [hr] at hcall
    have he : { state with completed := some batch } = after := by simpa using hcall
    subst after
    intro actual hslot old hold _ hbatch
    have he : actual = batch := by simpa using hslot.symm
    subst actual
    rcases List.mem_append.mp hold with hold | hold
    · have hb := hreach.validation.1.2.1
      exact False.elim (hfresh old hold (hbatch.trans hb))
    · have he : old = issued := by simpa using hold
      exact he ▸ hreach
  · intro id history state batch after hs hcall
    obtain ⟨hslot, rfl⟩ := poll_accepted state after batch hcall
    exact ⟨tracks_cleared id history _ rfl, hs batch hslot⟩
  · intro id history state after hs hcall
    have he : state = after := by
      simpa [stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor.code_end] using hcall
    exact he ▸ hs
/-- All callbacks of the synchronous scheduler return on seeds of bounded issued batches.
Submission needs neither valid bytes nor successful worker completion. -/
theorem callbacks_total : Stream.Scheduler.CallbacksTotal sync := by
  constructor
  · intro state chunk
    exact ⟨(.Ok (), state), rfl⟩
  · intro state region
    exact ⟨state, rfl⟩
  · intro state env
    exact ⟨_, environment_ready state env⟩
  · intro state issued hissued hbound
    obtain ⟨batch, hr, _⟩ := submit state issued hissued hbound
    exact ⟨_, hr⟩
  · exact poll_total
  · intro state
    exact ⟨(.Ok (), state), rfl⟩
end Itasca.Stream.Sync

end

/-! ## SliceSound -/

section

/-!
# Contiguous adapter soundness and termination

`stream.validate_module_slice` splits a contiguous module with `stream.find_code_region` and runs
`stream.validate_streaming` over a `stream.SliceSource` and the synchronous scheduler; the public
`metadata.validate_module` is this function. `total` shows it returns on arbitrary bytes and
`sound` shows that acceptance gives `Module.Sound.Validated`. Source and scheduler
obligations are discharged by `stream.SliceSource.coherent` and `Stream.Sync.provenance`, so no
embedding premise remains. `spec` combines both.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- `stream.validate_module_slice` returns on arbitrary input bytes. Its slice source and
synchronous scheduler satisfy every callback premise. -/
theorem stream.validate_module_slice.total (bytes : Slice U8) :
    ∃ r, stream.validate_module_slice bytes = .ok r := by
  obtain ⟨⟨first, last⟩, hsplit, _⟩ := WP.spec_imp_exists (stream.find_code_region.spec bytes)
  obtain ⟨environment, code, tail, he, hc, ht, _⟩ := stream.find_code_region.slices bytes first last hsplit
  obtain ⟨⟨r, visitor⟩, hr⟩ := stream.validate_streaming.total_core
    stream.SliceSource.Insts.ItascaStreamStreamingSource stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor
    0#u64 ⟨environment, code, tail⟩ ⟨none⟩
    (stream.SliceSource.callbacks_total _) Stream.Sync.callbacks_total
  exact ⟨r, by simp only [stream.validate_module_slice, hsplit, bind_ok, Std.uncurry, he, hc, ht, hr]⟩

/-- If `stream.validate_module_slice` accepts, the returned environment and tail are those of the
accepted streaming run, and they validate the input bytes. -/
theorem stream.validate_module_slice.sound (bytes : Slice U8) (decoded : metadata.ModuleMetadata metadata.CodeMetadata)
    (h : stream.validate_module_slice bytes = .ok (.Ok decoded)) :
    Module.Sound.Validated bytes decoded := by
  obtain ⟨⟨first, last⟩, hsplit, _⟩ := WP.spec_imp_exists (stream.find_code_region.spec bytes)
  obtain ⟨environment, code, tail, he, hc, ht, hbytes⟩ := stream.find_code_region.slices bytes first last hsplit
  simp only [stream.validate_module_slice, hsplit, bind_ok, Std.uncurry, he, hc, ht] at h
  obtain ⟨⟨r, visitor⟩, hrun, h⟩ := Computation.bind_ok_inv _ _ _ h
  have eq : r = .Ok decoded := by simpa using h
  subst r
  exact (stream.validate_streaming.sound_core
    stream.SliceSource.Insts.ItascaStreamStreamingSource stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor
    Stream.Sync.Tracks Stream.Sync.provenance 0#u64 ⟨environment, code, tail⟩ ⟨none⟩ visitor
    decoded bytes environment code tail (stream.SliceSource.coherent _) hbytes
    (Stream.Sync.tracks_empty _ _) hrun).2.1

/-- Arbitrary inputs return normally, and every accepted result is `Module.Sound.Validated`, which
includes the independent module certificate and the returned metadata. -/
theorem stream.validate_module_slice.spec (bytes : Slice U8) :
    stream.validate_module_slice bytes ⦃ r => match r with
      | .Ok decoded => Module.Sound.Validated bytes decoded
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr⟩ := stream.validate_module_slice.total bytes
  rw [hr]
  simp only [WP.spec_ok]
  cases r with
  | Err _ => trivial
  | Ok decoded => exact stream.validate_module_slice.sound bytes decoded hr

end Itasca

end

/-! ## SyncComplete -/

section

/-!
# Synchronous worker completeness

`Stream.Sync.accepts` shows that the synchronous scheduler `stream.SyncVisitor` satisfies the
accepting policy `Stream.Scheduler.Accepts`, with batch size 25000 bytes and capacity one,
so completeness for `validate_module` has no scheduler premise.
-/

open Aeneas Aeneas.Std

namespace Itasca.Stream.Sync

local notation "sync" => stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor

/-- The synchronous worker has a single slot. A nonempty logical queue identifies that slot as the
result of `stream.StreamingBatch.validate_all` on its seed. -/
def Queued (_id : U64) (queue : List Stream.Batch.Issued) (state : stream.SyncVisitor) : Prop :=
  match queue with
  | [] => state.completed = none
  | [issued] => ∃ batch, state.completed = some batch ∧
      stream.StreamingBatch.validate_all issued.seed = .ok batch
  | _ => False

/-- The synchronous scheduler satisfies the accepting scheduler policy. Capacity one prevents a
queued batch from being overwritten. -/
theorem accepts : Stream.Scheduler.Accepts sync
    { batch_bytes := 25000#usize, max_batches := 1#usize } Queued := by
  constructor
  · decide
  · decide
  · exact custom_accepts
  · intro id queue state chunk after hcall hqueue
    have he : state = after := by
      simpa [stream.SyncVisitor.Insts.ItascaMetadataModuleVisitor,
        metadata.ModuleVisitor.on_custom_section.default] using hcall
    exact he ▸ hqueue
  · intro id queue state region hqueue
    exact ⟨state, custom_region state region, hqueue⟩
  · intro id queue state env hqueue
    exact ⟨state, environment_ready state env, hqueue⟩
  · intro id queue issued state hqueue hbounded hentry _ hroom
    have hnil : queue = [] := by simpa using hroom
    subst queue
    obtain ⟨after, hr, _⟩ := WP.spec_imp_exists
      (stream.StreamingBatch.validate_all.reachable issued issued.seed hbounded hentry .seed)
    refine ⟨{ state with completed := some after }, ?_, after, rfl, hr⟩
    simp [stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor.submit_code_batch, hr]
  · intro id queue state hqueue hnonempty
    cases queue with
    | nil => contradiction
    | cons issued rest =>
      cases rest with
      | cons _ _ => exact False.elim hqueue
      | nil =>
        obtain ⟨batch, hslot, hr⟩ := hqueue
        exact ⟨issued, [], batch, { state with completed := none }, .refl _,
          poll_some state batch hslot, hr, rfl⟩
  · intro id queue state hqueue
    exact ⟨state, code_end state, hqueue⟩
end Itasca.Stream.Sync

end

end

/-! ## SliceComplete -/

section

/-!
# Contiguous adapter completeness

`stream.validate_module_slice.complete_with_metadata`: every independently encoded,
elaborated and typed module within the implementation limits is accepted by
`stream.validate_module_slice`, and the returned environment and tail match the raw module and its
public accessor types. The slice source (`stream.SliceSource.available`) and synchronous scheduler
(`Stream.Sync.accepts`) discharge the source availability and accepting scheduler premises of the
streaming driver. The `wasm_` theorems are the scalar instances.
-/

open Aeneas Aeneas.Std

namespace Itasca

open Itasca.Binary Module.Elaboration

/-- `stream.validate_module_slice` accepts every independently encoded, elaborated, typed module
within the implementation limits. Its slice source and synchronous
scheduler discharge all embedding premises. The returned environment and tail match the raw
module and its public accessor types. -/
theorem stream.validate_module_slice.complete_with_metadata
    (data : Slice U8) (raw : Binary.Module)
    (hb : ModuleEncodingWithinLimits raw data.val)
    (hsignatures : ModuleSignaturesWithinLimits raw)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Restrictions raw) :
    ∃ decoded, stream.validate_module_slice data = .ok (.Ok decoded) ∧
      Matches decoded raw ∧ AccessorTypes decoded raw := by
  obtain ⟨⟨first, last⟩, hsplit, _⟩ := WP.spec_imp_exists (stream.find_code_region.spec data)
  obtain ⟨environment, code, tail, henvironment, hcode, htail, _⟩ :=
    stream.find_code_region.slices data first last hsplit
  let regions : stream.SliceSource := ⟨environment, code, tail⟩
  obtain ⟨prepared, _, _, certificate⟩ := Stream.CompleteRegions.prepare data raw hb hsignatures he ht hp
  have same : regions = prepared :=
    Stream.CompleteRegions.ComputedSplit.unique
      ⟨first, last, hsplit, henvironment, hcode, htail⟩ certificate.split
  have canonical : Stream.CompleteRegions.Split data regions := by
    rw [same]
    exact certificate.canonical
  have hcanonical : Stream.Source.CanonicalAvailable stream.SliceSource.Insts.ItascaStreamStreamingSource
      regions data :=
    ⟨regions, canonical, stream.SliceSource.available regions⟩
  obtain ⟨env, after, run, hrun, hmatches, hmetadata, _⟩ := stream.validate_streaming.complete_core
    stream.SliceSource.Insts.ItascaStreamStreamingSource stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor
    { batch_bytes := 25000#usize, max_batches := 1#usize } Stream.Sync.Queued Stream.Sync.accepts
    0#u64 regions ⟨none⟩ data raw hb hsignatures he ht hp hcanonical rfl
  refine ⟨env, ?_, hmatches, hmetadata⟩
  unfold stream.validate_module_slice
  simp only [hsplit, bind_ok, Std.uncurry]
  simp only [henvironment, hcode, htail, bind_ok]
  dsimp only [regions] at hrun
  simp [hrun]

/-- `stream.validate_module_slice.complete_with_metadata` without the accessor types. -/
theorem stream.validate_module_slice.complete
    (data : Slice U8) (raw : Binary.Module)
    (hb : ModuleEncodingWithinLimits raw data.val)
    (hsignatures : ModuleSignaturesWithinLimits raw)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Restrictions raw) :
    ∃ decoded, stream.validate_module_slice data = .ok (.Ok decoded) ∧
      Matches decoded raw := by
  obtain ⟨decoded, hr, hm, _⟩ := stream.validate_module_slice.complete_with_metadata data raw hb hsignatures he ht hp
  exact ⟨decoded, hr, hm⟩

end Itasca

end
