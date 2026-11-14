import Itasca.Profile.CodeEntry
import Itasca.Wasm2.Completeness
import Itasca.Wasm2.Visitor.ReachedTableLoop
import Itasca.Module.Code.Framing
import Itasca.Wasm2.Visitor.Total
import Itasca.Module.Code.LocalsComplete
import Itasca.Binary.Wasm2.EncodingUnique
import Itasca.Binary.ModuleUnique

/-!
Sections, each formerly its own module: Body, BodyVisitor, EntryPipeline, EntryComplete, EntrySound, BinaryUnique.
-/

/-! ## Body -/

section

/-!
# Profile body contracts

`Profile.run` is the visitor-free body validator `code.bodyCore`, with `run.sound`
and `run.complete` stating soundness for `Wasm2.Validated` and completeness under
the implementation bounds.
-/

open Aeneas Aeneas.Std

namespace Itasca.Profile

/-- The body grammar describes Wasm 2.0 body bytes. -/
theorem BodyEncoding.to_wasm2 {data ops} (h : BodyEncoding data ops) :
    Wasm2.BodyEncoding data ops := h

/-- The visitor-free body validator for Wasm 2.0. -/
def run (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) :=
  code.bodyCore data env ctx.locals ctx.results index

/-- If the body validator accepts, the body meets `Wasm2.Validated`. -/
theorem run.sound (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32)
    (haccepted : run data env ctx index = .ok (.Ok ())) :
    Wasm2.Validated data env ctx.locals index :=
  code.bodyCore.sound data env ctx.locals ctx.results index haccepted

/-- If the body meets `Wasm2.Validated` and the implementation bounds hold, the body validator
accepts. -/
theorem run.complete (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (hlimits : EnvironmentWithinLimits env)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hbody : Wasm2.Validated data env ctx.locals index) :
    run data env ctx index = .ok (.Ok ()) := by
  exact code.bodyCore.complete data env ctx.locals ctx.results index hlimits hsize
    hbody

end Itasca.Profile

end

/-! ## BodyVisitor -/

section

/-!
# Profile body contracts with visitors

Transfers the `Profile.run` contracts to `code.validate_body_with` for an arbitrary
`code.OpVisitor`: `profile_sound` and `profile_complete` give `Wasm2.Validated` soundness and
completeness.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- If the body validator accepts, the body meets
`Wasm2.Validated`. -/
theorem code.validate_body_with.profile_sound {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
     (v v' : V)
    (h : code.validate_body_with visitor data env ctx index v = .ok (.Ok (), v')) :
    Wasm2.Validated data env ctx.locals index :=
  Profile.run.sound data env ctx index
    (code.validate_body_with.accepted_erase visitor data env ctx index _ v v' h)

/-- If the body meets `Wasm2.Validated` and the bounds hold, the body validator accepts with
accepting callbacks. -/
theorem code.validate_body_with.profile_complete {V : Type} (visitor : code.OpVisitor V)
    (ha : FullVisitor.Accepts visitor) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (index : U32) (v : V)
    (hlimits : Profile.EnvironmentWithinLimits env)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hbody : Wasm2.Validated data env ctx.locals index) :
    ∃ v', code.validate_body_with visitor data env ctx index v = .ok (.Ok (), v') :=
  code.validate_body_with.accepted_lift visitor ha data env ctx index _ v
    (Profile.run.complete data env ctx index hlimits hsize hbody)

end Itasca

end

/-! ## EntryPipeline -/

section

/-!
# Profile code-entry pipeline

Totality of the extracted `metadata.validate_code_entry_with` for Wasm 2.0:
`profile_pipeline` gives an execution witness (`CodeEntry.Witness`) for every accepting run, and
`profile_total` and `metadata.validate_code_entry.profile_total` show that the visitor and
visitor-free entry validators return.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- Every accepting run of the entry validator, for Wasm 2.0, has a `CodeEntry.Witness`
recording the type lookup, locals, body slice and visitor calls. -/
theorem metadata.validate_code_entry_with.profile_pipeline {V : Type} (visitor : code.OpVisitor V)
    (hv : FullVisitor.Total visitor) (data : Slice U8) (pos : Usize)
    (env : metadata.Env) (index : Usize) (v : V) (hbound : CodeEntry.Bounds env)
     :
    metadata.validate_code_entry_with visitor data pos env index v ⦃ r =>
      ∀ finish, r.1 = .Ok finish →
        Nonempty (CodeEntry.Witness visitor data env index pos finish v r.2 ) ⦄ :=
  metadata.validate_code_entry_with.pipeline_of_body_total visitor hv data pos env index v hbound
    (fun body ctx typeIdx started => code.validate_body_with.total visitor hv body env ctx typeIdx started)

/-- The entry validator with a total visitor returns a result. -/
theorem metadata.validate_code_entry_with.profile_total {V : Type} (visitor : code.OpVisitor V)
    (hv : FullVisitor.Total visitor) (data : Slice U8) (pos : Usize)
    (env : metadata.Env) (index : Usize) (v : V) (hbound : CodeEntry.Bounds env)
     :
    ∃ r, metadata.validate_code_entry_with visitor data pos env index v = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists
    (metadata.validate_code_entry_with.profile_pipeline visitor hv data pos env index v hbound )
  exact ⟨r, hr⟩

end Itasca

end

/-! ## EntryComplete -/

section

/-!
# Profile code-entry completeness

Completeness of `metadata.validate_code_entry_with`: a code entry that meets the independent
specification (`Profile.EntryTyped`, `CodeEncodingWithinLimits`) is accepted.
`complete_spec_of_body` takes a body completeness hypothesis, and `profile_complete_spec` and
`profile_complete` discharge it for Wasm 2.0.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary

/-- Code-entry validation succeeds with end offset `next` when the entry has exact bytes, is typed
and meets the byte and local limits, given a completeness hypothesis for the body
step. -/
theorem metadata.validate_code_entry_with.complete_spec_of_body {V : Type} (visitor : code.OpVisitor V)
    (haccept : FullVisitor.Accepts visitor) (data : Slice U8) (pos : Usize)
    (env : metadata.Env) (index : Usize) (entry : Code) (next : Usize) (v : V)

    (hi : index.val < env.func_type_indices.val.length)
    (htyped : Profile.EntryTyped env env.func_type_indices.val[index.val] entry)
    (hbound : CodeEntry.Bounds env)
    (hbytes : At (Profile.CodeEncodingWithinLimits ) data pos entry next)
    (hcomplete : ∀ body ctx typeIdx ft,
      env.types.val[typeIdx.val]? = some ft → ctx.results.val = ft.results.val →
      body.length ≤ limits.MAX_FUNCTION_BYTES.val → Wasm2.Validated body env ctx.locals typeIdx →
      ∀ started, ∃ ended,
        code.validate_body_with visitor body env ctx typeIdx started = .ok (.Ok (), ended)) :
    metadata.validate_code_entry_with visitor data pos env index v ⦃ r => r.1 = .Ok next ⦄ := by
  obtain ⟨bytes, he, hspan⟩ := hbytes
  obtain ⟨hcap, sizeBytes, localBytes, bodyBytes, hsize, hlocals, hbody, hbodyCap, rfl⟩ := he
  obtain ⟨bodyStart, hprefix, hbodySpan⟩ := hspan.split
  obtain ⟨content, hhead, hlocalsSpan⟩ := hprefix.split
  let size : U32 := U32.ofNatCore (localBytes.length + bodyBytes.length) (by have := hsize.value_lt; scalar_tac)
  have hsizeval : size.val = localBytes.length + bodyBytes.length := by simp [size]
  have hread := hhead.read_u32 size (by simpa [hsizeval] using hsize)
  have hend : next.val = content.val + size.val := by
    have := hlocalsSpan.length
    have := hbodySpan.length
    omega
  obtain ⟨declared, hdeclared, hdeclaredVal⟩ := metadata.decode_locals.complete data content entry.locals bodyStart
    ⟨localBytes, hlocals, hlocalsSpan⟩ hcap
  have hindex : ¬ index ≥ alloc.vec.Vec.len env.func_type_indices := by scalar_tac
  unfold metadata.validate_code_entry_with
  simp [hindex, hread, core.result.Result.Insts.CoreOpsTry.branch]
  step
  obtain ⟨hr, hhave, hhavePost⟩ := WP.spec_imp_exists
    (metadata.have_bytes.spec data content n (by have := hhead.bound; omega))
  have hgood : hr = .Ok () := hhavePost.1.mpr (by have := hspan.bound; scalar_tac)
  rw [hgood] at hhave
  simp [hhave]
  step
  have hendEq : «end» = next := by scalar_tac
  simp [hdeclared]
  have hbodyStart : ¬ «end».val < bodyStart.val := by have := hbodySpan.length; scalar_tac
  simp only [hbodyStart, ↓reduceIte]
  step
  have ht : Profile.EntryTyped env type_idx entry := by simpa [type_idx_post] using htyped
  step
  have htype : ¬ env.types.val.length ≤ t.val := by have := ht.type_lt; scalar_tac
  simp only [htype, ↓reduceIte]
  step
  have hti := ht.type_lt
  have hft : env.types.val[type_idx.val] = ft := by simpa [t_post] using ft_post.symm
  have hmem : ft ∈ env.types.val := by rw [← hft]; exact List.getElem_mem _
  have hroom : ft.params.val.length + declared.val.length ≤ Usize.max := by
    have := hbound ft hmem
    rw [hdeclaredVal]
    have hc : (ModuleLocals.declared entry.locals).length ≤ limits.MAX_LOCALS.val := hcap
    omega
  obtain ⟨locals, hbuild, hbuildVal⟩ := WP.spec_imp_exists
    (metadata.build_func_locals.spec (alloc.vec.Vec.deref ft.params) (alloc.vec.Vec.deref declared)
      (by simpa [alloc.vec.Vec.deref] using hroom))
  obtain ⟨results, hcopy, hcopyVal⟩ := WP.spec_imp_exists
    (metadata.copy_value_types.spec (alloc.vec.Vec.deref ft.results))
  rw [hbuild]
  simp only [bind_ok]
  rw [hcopy]
  simp only [bind_ok]
  obtain ⟨started, hstart⟩ := haccept.on_function_start v ⟨locals, results⟩ type_idx bodyStart «end»
  rw [hstart]
  simp only [bind_ok]
  step as ⟨r, r_post⟩
  have hactual := ModuleBinary.slice_bytes (by have := hbodySpan.length; scalar_tac)
    (by rw [hendEq]; exact hbodySpan.bound) r_post
  have hslice : r.val = bodyBytes := by
    rw [hendEq] at hactual
    exact List.append_cancel_right (hactual.suffix.symm.trans hbodySpan.suffix)
  have hctxlocals : (⟨locals, results⟩ : code.Context).locals.val =
      env.types.val[type_idx.val].params.val ++ entry.declared := by
    rw [hft]
    simpa [alloc.vec.Vec.deref, hdeclaredVal, ModuleBinary.Code.declared, ModuleLocals.declared] using hbuildVal
  have hctxresults : (⟨locals, results⟩ : code.Context).results.val = ft.results.val := by
    simpa [alloc.vec.Vec.deref] using hcopyVal
  have hlookup : env.types.val[type_idx.val]? = some ft := by simp [List.getElem?_eq_getElem hti, hft]
  have hencoding := Profile.BodyBytes.body (data := r) (by simpa [hslice] using hbody)
  have hcert := ht.body r locals hctxlocals hencoding
  obtain ⟨finished, hfinished⟩ := hcomplete r ⟨locals, results⟩ type_idx ft hlookup hctxresults
    (by simpa [Slice.length, hslice] using hbodyCap) hcert started
  rw [hfinished]
  simp [hendEq]

/-- Entry validation succeeds, as a weakest-precondition statement, for Wasm 2.0 under the
environment and size bounds. -/
theorem metadata.validate_code_entry_with.profile_complete_spec {V : Type} (visitor : code.OpVisitor V)
    (haccept : FullVisitor.Accepts visitor) (data : Slice U8) (pos : Usize)
    (env : metadata.Env) (index : Usize) (entry : Code) (next : Usize) (v : V)
     (hi : index.val < env.func_type_indices.val.length)
    (htyped : CodeEntry.Typed env env.func_type_indices.val[index.val] entry )
    (hlimits : Profile.EnvironmentWithinLimits env)
    (hbound : CodeEntry.Bounds env)
    (hbytes : At (Profile.CodeEncodingWithinLimits ) data pos entry next) :
    metadata.validate_code_entry_with visitor data pos env index v ⦃ r => r.1 = .Ok next ⦄ := by
  apply metadata.validate_code_entry_with.complete_spec_of_body visitor haccept data pos env index entry next v
     hi (Profile.EntryTyped.of_core htyped) hbound hbytes
  intro body ctx typeIdx ft hlookup hresults hsize hcert started
  exact code.validate_body_with.profile_complete visitor haccept body env ctx typeIdx started
    hlimits hsize hcert

/-- Entry validation returns `.Ok next` for Wasm 2.0 under the environment and size
bounds. -/
theorem metadata.validate_code_entry_with.profile_complete {V : Type} (visitor : code.OpVisitor V)
    (haccept : FullVisitor.Accepts visitor) (data : Slice U8) (pos : Usize)
    (env : metadata.Env) (index : Usize) (entry : Code) (next : Usize) (v : V)
     (hi : index.val < env.func_type_indices.val.length)
    (htyped : CodeEntry.Typed env env.func_type_indices.val[index.val] entry )
    (hlimits : Profile.EnvironmentWithinLimits env)
    (hbound : CodeEntry.Bounds env)
    (hbytes : At (Profile.CodeEncodingWithinLimits ) data pos entry next) :
    ∃ v', metadata.validate_code_entry_with visitor data pos env index v = .ok (.Ok next, v') := by
  obtain ⟨⟨r, v'⟩, hr, hok⟩ := WP.spec_imp_exists
    (metadata.validate_code_entry_with.profile_complete_spec visitor haccept data pos env index entry next v
       hi htyped hlimits hbound hbytes)
  dsimp only at hok
  exact ⟨v', by simpa only [hok] using hr⟩

end Itasca

end

/-! ## EntrySound -/

section

/-!
# Profile code-entry soundness

Acceptance by `metadata.validate_code_entry_with` yields the specification `Profile.Entry`
(`metadata.validate_code_entry_with.profile_sound`), for Wasm 2.0 and any visitor.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- An execution witness and a `Wasm2.Validated` fact for its body give `Profile.Entry`. The entry
parser supplies framing and locals, and the body fact supplies the decoded and typed tree. -/
theorem CodeEntry.Witness.profile_validated
    {V : Type} {visitor : code.OpVisitor V} {data env index start finish v v' }
    (w : CodeEntry.Witness visitor data env index start finish v v' )
    (hbody : Wasm2.Validated w.body env w.ctx.locals w.typeIdx) :
    Profile.Entry data env index start finish := by
  obtain ⟨ft, ops, hlookup, hbytes, htyped, hdeclared⟩ := hbody
  have hlookup' : env.types.val[w.typeIdx.val]? = some w.ft := by
    rw [List.getElem?_eq_getElem w.type_lt, w.function_type]
  have hft : ft = w.ft := Option.some.inj (hlookup.symm.trans hlookup')
  subst ft
  refine ⟨⟨w.groups, ops⟩, Profile.codeEncoding_of_parts w.header w.extent
    w.locals_bytes w.body_bytes hbytes, w.index_lt, ?_, w.locals_bound⟩
  rw [w.index_type]
  exact Profile.EntryTyped.of_body hlookup w.context_locals htyped hdeclared

/-- If the entry validator accepts, the entry satisfies `Profile.Entry`. This needs no visitor
totality assumption. -/
theorem metadata.validate_code_entry_with.profile_sound {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (pos : Usize) (env : metadata.Env) (index finish : Usize)
    (v v' : V) (hbound : CodeEntry.Bounds env)
    (h : metadata.validate_code_entry_with visitor data pos env index v = .ok (.Ok finish, v')) :
    Profile.Entry data env index pos finish := by
  obtain ⟨w⟩ := metadata.validate_code_entry_with.witness_profile visitor data pos env index finish v v'
    hbound h
  apply w.profile_validated
  exact code.validate_body_with.profile_sound visitor w.body env w.ctx w.typeIdx w.startedState v'
    w.body_accepted

end Itasca

end

/-! ## BinaryUnique -/

section

/-!
# Profile binary uniqueness

Lifts the uniqueness of the binary grammars to the body and entry contracts: `BodyBytes.unique` for body bytes
and `code_prefix_unique` for code entries. `Itasca/Results/Unique` gives the complete-module
result.
-/

open Aeneas Aeneas.Std

namespace Itasca.Profile

open ModuleBinary

/-- The body bytes determine one instruction tree, independently of typing and
implementation bounds. -/
theorem BodyBytes.unique : Unique BodyBytes := by
  rintro xs ys bytes ⟨xt, hx, hxs⟩ ⟨yt, hy, hys⟩
  obtain rfl := Wasm2.tokens_unique hx hy
  exact hxs.unique hys

/-- Code entries, with their size prefix and local declarations, are prefix-unique under Wasm 2.0. -/
theorem code_prefix_unique : PrefixUnique CodeEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨xn, xl, xb, hn, hl, hb, rfl⟩ := hx
  obtain ⟨yn, yl, yb, hn', hl', hb', rfl⟩ := hy
  obtain ⟨hlen, rfl, hcontent⟩ := leb_prefix_unique hn hn'
    (by simpa [List.append_assoc] using he)
  obtain ⟨hpayload, rfl⟩ := split_of_length
    (by simpa [List.append_assoc] using hcontent : (xl ++ xb) ++ rest = (yl ++ yb) ++ tail)
    (by simpa using hlen)
  obtain ⟨hlv, rfl, rfl⟩ := local_prefix_unique.vec hl hl' hpayload
  have hbv := BodyBytes.unique hb hb'
  have hv : x = y := by cases x; cases y; simp_all
  exact ⟨hv, rfl, rfl⟩

end Itasca.Profile

end
