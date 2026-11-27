import Itasca.Module.Env.Externals
import Itasca.Module.Readers.Syntax
import Itasca.Module.Const.Parser
import Itasca.Module.Elab.SegmentTyping

/-!
# Section and element headers

Type-vector parsing, section order and data-count checks supply framing facts. Element
initializer/header decoding retains its exact grammar and validity conditions for complete
element sections.
-/

/-! ## Type -/

section

/-!
# Type section parser

Soundness of `metadata.decode_type_section` and its loop. `TypesAdded` says the environment gains
exactly the decoded signatures. The `spec` forms give a `VecEncoding FuncTypeEncoding`
span whose signatures satisfy the completeness caps. Completeness is in `Module/Sections/IndexSpacesComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary

/-- A repetition span extends by one element at its end. -/
theorem At.snoc {α : Type} {R : α → List U8 → Prop} {data start pos next values value}
    (h : At (Rep R) data start values pos) (h' : At R data pos value next) :
    At (Rep R) data start (values ++ [value]) next := by
  obtain ⟨bytes, hr, hs⟩ := h
  obtain ⟨last, he, ht⟩ := h'
  exact ⟨bytes ++ last, hr.snoc he, hs.append ht⟩

/-- A decoded count, a repetition of that many elements and their span form a `VecEncoding`. -/
theorem At.vector {α : Type} {R : α → List U8 → Prop} {data start pos next count values}
    (hc : Binary.Leb128.Decoded data start count pos)
    (he : At (Rep R) data pos values next) (hlen : values.length = count.val) :
    At (VecEncoding R) data start values next := by
  obtain ⟨bytes, hr, hs⟩ := he
  obtain ⟨countBytes, hcs, hcl, hcb, hce⟩ := hc
  exact ⟨countBytes ++ bytes,
    ⟨countBytes, bytes, by simpa [hlen] using hce, hr, rfl⟩,
    (show Body.Scalar.BytesAt data start countBytes pos from ⟨hcs, hcl, hcb⟩).append hs⟩

/-- A function type encoding consumes at least one byte. -/
theorem At.func_type_progress {data start ty next} (h : At FuncTypeEncoding data start ty next) :
    start.val < next.val := by
  obtain ⟨bytes, he, hs⟩ := h
  obtain ⟨params, results, _, _, rfl⟩ := FuncTypeEncoding.reader_parts.mp he
  have := hs.length
  simp only [List.length_cons, List.length_append] at this
  omega

end Itasca.Binary

namespace Itasca.Module.Sections

/-- `result` is `env` with the signatures `added` appended to its type table and nothing else
changed. -/
def TypesAdded (env result : metadata.CodeMetadata) (added : List wasm_types.FuncType) : Prop :=
  result = { env with types := result.types } ∧ result.types.val = env.types.val ++ added

end Itasca.Module.Sections

namespace Itasca

open Binary Module.Sections

/-- The type loop adds `count` signatures forming a `Rep FuncTypeEncoding` span. Each satisfies the
completeness caps. -/
@[step]
theorem metadata.decode_type_section_loop.spec (data : Slice U8) (env : metadata.CodeMetadata)
     (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hsize : env.types.val.length ≤ start.val) :
    metadata.decode_type_section_loop data env count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ added, added.length = count.val ∧ TypesAdded env r.2 added ∧
          At (Rep FuncTypeEncoding) data start added next ∧
          (∀ ft ∈ added, CodeEntry.FuncTypeWithinLimits ft) ∧ r.2.types.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  unfold metadata.decode_type_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ added, added.length = s.2.2.val ∧
      TypesAdded env s.1 added ∧ At (Rep FuncTypeEncoding) data start added s.2.1 ∧
      (∀ ft ∈ added, CodeEntry.FuncTypeWithinLimits ft) ∧ s.1.types.val.length ≤ s.2.1.val)
  · rintro ⟨current, pos, i⟩ ⟨hi, added, hlen, henv, hbytes, hvalid, hsize⟩
    dsimp only at hi hlen henv hbytes hvalid hsize
    unfold metadata.decode_type_section_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : i.val = count.val := by scalar_tac
      exact ⟨added, by omega, henv, hbytes, hvalid, hsize⟩
    · rename_i hmore
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (metadata.decode_func_type.spec data pos)
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        obtain ⟨ft, next⟩ := pair
        obtain ⟨hb, ht⟩ := hp
        have hprogress := hb.func_type_progress
        have hbound := hb.span.2
        have hcapacity : current.types.val.length < Usize.max := by scalar_tac
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step
        step
        refine ⟨?_, ⟨added ++ [ft], ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · scalar_tac
        · simp only [List.length_append, List.length_singleton]; scalar_tac
        · constructor
          · rw [henv.1]
          · simp [r_post, henv.2, List.append_assoc]
        · exact hbytes.snoc hb
        · intro ty hm
          rcases List.mem_append.mp hm with hm | hm
          · exact hvalid ty hm
          · simpa [List.mem_singleton.mp hm] using ht
        · simp only [r_post, List.length_append, List.length_singleton]; omega
        · scalar_tac
  · exact ⟨by simp, [], by simp, ⟨by cases env; rfl, by simp⟩,
      ⟨[], .nil, Body.Scalar.BytesAt.nil data start hstart⟩, by simp, hsize⟩

/-- `metadata.decode_type_section` adds the signatures of a `VecEncoding FuncTypeEncoding` span, each
satisfying the completeness caps. -/
@[step]
theorem metadata.decode_type_section.spec (data : Slice U8) (pos : Usize) (env : metadata.CodeMetadata)
     (hsize : env.types.val.length ≤ pos.val) :
    metadata.decode_type_section data pos env ⦃ r => match r.1 with
      | .Ok next => ∃ added, TypesAdded env r.2 added ∧
          At (VecEncoding FuncTypeEncoding) data pos added next ∧
          (∀ ft ∈ added, CodeEntry.FuncTypeWithinLimits ft) ∧ r.2.types.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e => simp [metadata.decode_type_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨count, start⟩ := pair
    have hs := hc.span
    obtain ⟨⟨r, result⟩, hloop, hp⟩ := WP.spec_imp_exists
      (metadata.decode_type_section_loop.spec data env count start hs.2.2 (by omega))
    simp [metadata.decode_type_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok next =>
      obtain ⟨added, hlen, henv, hb, ht, hsize⟩ := hp
      exact ⟨added, henv, At.vector hc hb hlen, by simpa only [and_assoc, List.mem_append] using ht, hsize⟩

end Itasca

end

/-! ## DataCount -/

section

/-!
# Section order and data count section

`Binary.sectionRank` is the Wasm 2.0 section order, and `metadata.section_order` computes it
and rejects ids outside `1` to `12` (spec and `.complete`). `metadata.decode_data_count` reads the
data count section, which only Wasm 2.0 accepts, and records the count in the environment.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary

/-- The position of a section id in the Wasm 2.0 order, which places the data count section (`12`)
before code (`10`) and data (`11`). Custom sections have no rank. -/
def sectionRank (id : U8) : U8 :=
  match id.val with
  | 12 => 10#u8
  | 10 => 11#u8
  | 11 => 12#u8
  | _ => id

/-- Ranks `1` to `10` belong to the ids `1` to `9` and `12`. -/
theorem section_rank_prefix {id : U8} (hlo : 1 ≤ (sectionRank id).val)
    (hhi : (sectionRank id).val ≤ 10) :
    id.val = 1 ∨ id.val = 2 ∨ id.val = 3 ∨ id.val = 4 ∨ id.val = 5 ∨
      id.val = 6 ∨ id.val = 7 ∨ id.val = 8 ∨ id.val = 9 ∨ id.val = 12 := by
  by_cases h12 : id.val = 12
  · omega
  by_cases h10 : id.val = 10
  · have : (11#u8).val ≤ 10 := by simpa only [sectionRank, h10] using hhi
    change 11 ≤ 10 at this
    omega
  by_cases h11 : id.val = 11
  · have : (12#u8).val ≤ 10 := by simpa only [sectionRank, h11] using hhi
    change 12 ≤ 10 at this
    omega
  have he : sectionRank id = id := by simp [sectionRank]
  rw [he] at hlo hhi
  omega

end Itasca.Binary

namespace Itasca

/-- `metadata.section_order` returns the rank of an id from `1` to `12` and rejects other ids. -/
@[step]
theorem metadata.section_order.spec (id : U8) :
    metadata.section_order id ⦃ result => match result with
      | .Ok rank => rank = Binary.sectionRank id ∧ 1 ≤ id.val ∧ id.val ≤ 12
      | .Err _ => id.val = 0 ∨ 12 < id.val ⦄ := by
  have h10 : (10#uscalar : U8).val = 10 := rfl
  have h11 : (11#uscalar : U8).val = 11 := rfl
  have h12 : (12#uscalar : U8).val = 12 := rfl
  unfold metadata.section_order
  repeat' first | split
  all_goals simp_all [Binary.sectionRank, global_simps]
  all_goals first | omega | (split <;> simp_all; omega)

/-- `metadata.section_order` accepts every id from `1` to `12`. -/
theorem metadata.section_order.complete (id : U8) (hlo : 1 ≤ id.val) (hhi : id.val ≤ 12) :
    metadata.section_order id = .ok (.Ok (Binary.sectionRank id)) := by
  obtain ⟨result, hr, hp⟩ := WP.spec_imp_exists (metadata.section_order.spec id)
  cases result with
  | Err e => rcases hp with hz | hh <;> omega
  | Ok rank => simpa only [hp.1] using hr

/-- An accepted `metadata.decode_data_count` reads a `u32` count, sets only `data_count`, and
happens under Wasm 2.0. -/
@[step]
theorem metadata.decode_data_count.spec (data : Slice U8) (pos : Usize) (env : metadata.CodeMetadata) :
    metadata.decode_data_count data pos env ⦃ result => match result.1 with
      | .Ok next => ∃ count,
          Binary.At Binary.StartEncoding data pos (some count) next ∧
          result.2 = { env with data_count := some count }
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e =>
    simp [metadata.decode_data_count, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨count, next⟩ := pair
    simp only [metadata.decode_data_count, hr, bind_ok,
      core.result.Result.Insts.CoreOpsTry.branch]
    obtain ⟨bytes, hs, hl, hb, he⟩ := hd
    exact ⟨count, ⟨bytes, ⟨count, rfl, he⟩, hs, hl, hb⟩, rfl⟩

/-- Under Wasm 2.0, `metadata.decode_data_count` accepts a count span and sets `data_count`. -/
theorem metadata.decode_data_count.complete (data : Slice U8) (pos : Usize) (env : metadata.CodeMetadata)
    (count : U32) (next : Usize)
    (hb : Binary.At Binary.StartEncoding data pos (some count) next) :
    metadata.decode_data_count data pos env = .ok (.Ok next, {env with data_count := some count}) := by
  obtain ⟨bytes, ⟨idx, hi, he⟩, hs⟩ := hb
  have hidx : idx = count := Option.some.inj hi.symm
  subst idx
  simp [metadata.decode_data_count, hs.read_u32 count he,
    core.result.Result.Insts.CoreOpsTry.branch]

end Itasca

end

/-! ## ElementInit -/

section

/-!
# Element initializer parsers

Soundness of `metadata.decode_element_initializer` and `metadata.decode_element_initializers`, which
read the initializers of an element segment either as function indices (`ref.func`) or as full
constant expressions. `InitializerEncoding` is the independent grammar of one initializer.
Accepted values are `Module.Constants.Valid` at the segment's reference type, and the declared
function references grow by exactly those of the initializers (`Module.References.Added`).
Completeness is in `Module/Sections/DeclarationsComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Elements

/-- One initializer: either a function index standing for `ref.func`, or, when `expressions` is
set, a whole constant expression including its terminating `end`. -/
abbrev InitializerEncoding := Binary.ElementInitializerEncoding

/-- The value type of an initializer: the element type for expressions, and `funcref` for
function indices. -/
def initializerType (elem : wasm_types.ElemType) (expressions : Bool) : wasm_types.ValueType :=
  if expressions then Module.Constants.referenceValueType elem else .FuncRef

/-- An initializer encoding consumes at least one byte. -/
theorem InitializerEncoding.nonempty {expressions value bytes}
    (h : InitializerEncoding expressions value bytes) : 0 < bytes.length := by
  cases expressions with
  | true =>
    apply List.length_pos_iff.mpr
    rintro rfl
    exact WebAssembly.Binary.ConstEncoding.nonempty h rfl
  | false =>
    obtain ⟨_, _, _, _, rfl, _⟩ := Binary.ElementInitializerEncoding.index_parts.mp h
    simp

end Itasca.Module.Elements

namespace Itasca.Module.Constants

/-- Constant validity depends only on the function types, global types and imported global count. -/
theorem Valid.same_caches {env result value ty} (h : Valid env value ty)
    (hf : result.funcs.val.length = env.funcs.val.length)
    (hg : result.globals = env.globals)
    (hn : result.num_imported_globals = env.num_imported_globals) : Valid result value ty := by
  cases h with
  | i32 v => exact .i32 v
  | i64 v => exact .i64 v
  | f32 v => exact .f32 v
  | f64 v => exact .f64 v
  | v128 low high => exact .v128 low high
  | refNull t => exact .refNull t
  | refFunc idx hi => exact .refFunc idx (by simpa [hf] using hi)
  | globalGet idx gt hi he hb hc =>
    exact .globalGet idx gt (by simpa [hg] using hi) (by simpa [hg] using he)
      (by simpa [hn] using hb) hc

end Itasca.Module.Constants

namespace Itasca.Module.References

/-- Validity after adding declared references implies validity before. -/
theorem Added.valid_before {before after refs value ty} (h : Added before after refs)
    (hv : Module.Constants.Valid after value ty) : Module.Constants.Valid before value ty := by
  apply hv.same_caches
  · simp [h.funcs]
  · rw [h.fields]
  · rw [h.fields]

theorem Added.refl (env : metadata.CodeMetadata) : Added env env [] := by
  refine ⟨rfl, ?_⟩
  apply List.ext_getElem <;> simp

/-- Reference additions compose, including repeated references. -/
theorem Added.trans {before middle after xs ys} (h : Added before middle xs)
    (h' : Added middle after ys) : Added before after (xs ++ ys) := by
  constructor
  · calc after = { middle with funcs := after.funcs } := h'.fields
         _ = { before with funcs := after.funcs } := by rw [h.fields]
  · rw [h'.funcs, h.funcs]
    apply List.ext_getElem <;> simp [Bool.or_assoc]

end Itasca.Module.References

namespace Itasca

open Module.Elements Module.References

private def initValues : metadata.ElementInit → List wasm_types.ConstExpr
  | .Expressions values => values.val
  | .Functions indices => indices.val.map wasm_types.ConstExpr.RefFunc

private def InitPost (env : metadata.CodeMetadata) (data : Slice U8) (start : Usize)
    (exprs : Bool) (elem : wasm_types.ElemType) (count : U32)
    (r : core.result.Result (metadata.ElementInit × Usize) error.Error × metadata.CodeMetadata) : Prop :=
  match r.1 with
  | .Err _ => True
  | .Ok (values, next) =>
    (initValues values).length = count.val ∧
    Added env r.2 ((initValues values).flatMap initializer) ∧
    Binary.At (Binary.Rep (InitializerEncoding exprs)) data start (initValues values) next ∧
    ∀ v ∈ initValues values, Module.Constants.Valid env v (initializerType elem exprs)

private theorem expr_loop (data : Slice U8) (env : metadata.CodeMetadata) (elem : wasm_types.ElemType)
    (count : U32) (start : Usize) (hs : start.val ≤ data.length) :
    metadata.decode_element_initializers_loop0 data env elem count start 0#u32 (alloc.vec.Vec.new _)
      ⦃ r => InitPost env data start true elem count r ⦄ := by
  unfold metadata.decode_element_initializers_loop0
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.1.val)
    (fun (current, pos, i, values) => i.val ≤ count.val ∧ values.val.length = i.val ∧
      Added env current (values.val.flatMap initializer) ∧
      Binary.At (Binary.Rep (InitializerEncoding true)) data start values.val pos ∧
      ∀ v ∈ values.val, Module.Constants.Valid env v (initializerType elem true))
  · rintro ⟨current,pos,i,values⟩ ⟨hi,hlen,henv,hbytes,hvalid⟩
    simp only [metadata.decode_element_initializers_loop0.body]
    split
    · have ht : wasm_types.ElemType.value_type elem = .ok (Module.Constants.referenceValueType elem) := by
        cases elem <;> rfl
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists
        (metadata.decode_const_expr.spec data pos current (Module.Constants.referenceValueType elem))
      simp only [ht, hr, bind_ok]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, InitPost]
      | Ok pair =>
        obtain ⟨v,next⟩ := pair
        obtain ⟨hv,typed⟩ := hp
        have validIndex : ∀ idx ∈ initializer v, idx.val < current.funcs.val.length := by
          generalize Module.Constants.referenceValueType elem = ty at typed
          cases typed <;> simp_all [initializer]
        have hcap : values.val.length < Usize.max := by scalar_tac
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step with metadata.declare_initializer.spec current v validIndex as ⟨updated, hu⟩
        step as ⟨values', hv'⟩
        step as ⟨i', hi'⟩
        refine ⟨by scalar_tac, by simp [hv',hi',hlen], ?_, ?_, ?_, by scalar_tac⟩
        · simpa [hv'] using henv.trans hu
        · simpa [hv'] using hbytes.snoc (R := InitializerEncoding true) hv
        · intro x hx
          rcases (by simpa [hv'] using hx : x ∈ values.val ∨ x = v) with hx | rfl
          · exact hvalid x hx
          · exact henv.valid_before typed
    · exact ⟨by change values.val.length = count.val; scalar_tac, henv, hbytes, hvalid⟩
  · exact ⟨by simp, by simp, Added.refl _, ⟨[], .nil, Body.Scalar.BytesAt.nil data start hs⟩, by simp⟩

private theorem index_loop (data : Slice U8) (env : metadata.CodeMetadata) (elem : wasm_types.ElemType)
    (count : U32) (start : Usize) (hs : start.val ≤ data.length) :
    metadata.decode_element_initializers_loop1 data env count start 0#u32 (alloc.vec.Vec.new _)
      ⦃ r => InitPost env data start false elem count r ⦄ := by
  unfold metadata.decode_element_initializers_loop1
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.1.val)
    (fun (current,pos,i,indices) => i.val ≤ count.val ∧ indices.val.length = i.val ∧
      Added env current indices.val ∧
      Binary.At (Binary.Rep (InitializerEncoding false)) data start (indices.val.map wasm_types.ConstExpr.RefFunc) pos ∧
      ∀ idx ∈ indices.val, idx.val < env.funcs.val.length)
  · rintro ⟨current,pos,i,indices⟩ ⟨hi,hlen,henv,hbytes,hvalid⟩
    simp only [metadata.decode_element_initializers_loop1.body]
    split
    · obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
      rw [hr]
      cases r with
      | Err e => simp [InitPost, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, error.Error.Insts.CoreConvertFromOpError.from]
      | Ok pair =>
        obtain ⟨idx,next⟩ := pair
        by_cases hb : idx.val < current.funcs.val.length
        · have cap : indices.val.length < Usize.max := by scalar_tac
          have validIndex : ∀ j ∈ initializer (.RefFunc idx), j.val < current.funcs.val.length := by simp [initializer, hb]
          obtain ⟨updated, hu, ha⟩ := WP.spec_imp_exists (metadata.declare_initializer.spec current (.RefFunc idx) validIndex)
          obtain ⟨⟨fd,back⟩,hmut,hfd,hback⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_mut_usize_spec current.funcs
            (UScalar.cast .Usize idx) (by simpa using hb))
          simp [metadata.declare_initializer, lift, hmut] at hu
          subst updated
          simp [core.result.Result.Insts.CoreOpsTry.branch, lift, Nat.not_le_of_gt hb, hmut]
          step as ⟨indices', hv'⟩
          step as ⟨i', hi'⟩
          refine ⟨by scalar_tac, by simp [hv',hi',hlen], ?_, ?_, ?_, by scalar_tac⟩
          · simpa [hv',initializer] using henv.trans ha
          · obtain ⟨bytes, he, span⟩ := Binary.At.of_u32 hp
            have hv : Binary.At (InitializerEncoding false) data pos (.RefFunc idx) next :=
              ⟨bytes, Binary.ElementInitializerEncoding.index_parts.mpr ⟨idx,rfl,he⟩,span⟩
            simpa [hv'] using hbytes.snoc hv
          · have hb' : idx.val < env.funcs.val.length := by simpa [henv.funcs] using hb
            intro x hx
            rcases (by simpa [hv'] using hx : x ∈ indices.val ∨ x = idx) with hx | rfl
            · exact hvalid x hx
            · exact hb'
        · simp [core.result.Result.Insts.CoreOpsTry.branch, lift, Nat.le_of_not_gt hb, InitPost]
    · refine ⟨by simp [initValues]; scalar_tac, ?_, hbytes, ?_⟩
      · simpa [initValues, initializer, List.flatMap_map] using henv
      · simpa [initValues, initializerType] using fun idx h => Module.Constants.Valid.refFunc idx (hvalid idx h)
  · exact ⟨by simp, by simp, Added.refl _, ⟨[], .nil, Body.Scalar.BytesAt.nil data start hs⟩, by simp⟩

theorem metadata.decode_element_initializers.spec (data : Slice U8) (pos : Usize)
    (env : metadata.CodeMetadata) (elem : wasm_types.ElemType) (expressions : Bool) :
    metadata.decode_element_initializers data pos env elem expressions ⦃ r => match r.1 with
      | .Ok (values, next) =>
          Binary.At (Binary.VecEncoding (InitializerEncoding expressions)) data pos (initValues values) next ∧
          Added env r.2 ((initValues values).flatMap initializer) ∧
          ∀ v ∈ initValues values, Module.Constants.Valid env v (initializerType elem expressions)
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e => simp [metadata.decode_element_initializers, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨count,start⟩ := pair
    unfold metadata.decode_element_initializers
    simp only [hr, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    cases expressions <;> simp only [Bool.false_eq_true, ↓reduceIte]
    all_goals
      first | apply WP.spec_mono (index_loop data env elem count start hp.span.2.2)
            | apply WP.spec_mono (expr_loop data env elem count start hp.span.2.2)
      rintro ⟨r,result⟩ h
      cases r with
      | Err e => trivial
      | Ok pair =>
        obtain ⟨values,next⟩ := pair
        obtain ⟨hlen,ha,hbytes,hv⟩ := h
        exact ⟨Binary.At.vector hp hbytes hlen, ha, hv⟩

end Itasca

end

/-! ## ElementHeader -/

section

/-!
# Element segment header and entry parser

`Module.Elements.HeaderEncoding` is the independent grammar of the flag word and prefix of an
element segment in one of the eight Wasm 2.0 forms.
`metadata.decode_element_header.spec` shows an accepted header is a `HeaderEncoding` span whose
table and offset are valid. `metadata.decode_element.spec` assembles a full entry: an
`ElementEncoding` span that is valid, extends the declared functions by its references and
consumes input. Completeness is in `Module/Sections/DeclarationsComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Elements
open Binary

/-- The bytes of an element segment header for a mode, element type and initializer
form (`true` for expressions). The first argument of each constructor is the flag word. -/
abbrev HeaderEncoding := Binary.ElementHeaderEncoding

/-- An active segment names an in-range table of the segment's element type with a valid `i32`
offset. Passive and declarative segments have no condition. -/
def HeaderValid (env : metadata.CodeMetadata) (mode : metadata.ElementMode) (elem : wasm_types.ElemType) : Prop :=
  match mode with
  | .Active index offset => ∃ hi : index.val < env.tables.val.length,
      env.tables.val[index.val].ty.elem = elem ∧ Module.Constants.Valid env offset .I32
  | .Passive | .Declarative => True

theorem HeaderEncoding.append {mode elem expressions header init bytes}
    (h : HeaderEncoding mode elem expressions header)
    (hi : VecEncoding (InitializerEncoding expressions) init bytes) :
    ElementEncoding ⟨elem, mode, init⟩ (header ++ bytes) :=
  ElementEncoding.reader_parts.mpr ⟨_, _, _, h, hi, rfl⟩

/-- The initializer type of a header is the reference type of its element type. -/
theorem HeaderEncoding.initializer_type {mode elem expressions bytes}
    (h : HeaderEncoding mode elem expressions bytes) :
    initializerType elem expressions = Module.Constants.referenceValueType elem := by
  cases expressions with
  | true => rfl
  | false =>
    change WebAssembly.Binary.ElementHeaderEncoding _ _ _ _ at h
    generalize Source.elementMode mode = m at h
    generalize eq : Translation.referenceType elem = t at h
    generalize Source.bytes bytes = bs at h
    cases h <;> cases elem <;> first | rfl | contradiction

end Itasca.Module.Elements

namespace Itasca
open Binary Module.Elements

/-- An accepted `metadata.decode_element_header` is a `HeaderEncoding` span with a `HeaderValid`
mode and element type. -/
@[step]
theorem metadata.decode_element_header.spec (data : Slice U8) (pos : Usize)
    (env : metadata.CodeMetadata) :
    metadata.decode_element_header data pos env ⦃ r => match r with
      | .Ok (mode, elem, expressions, next) =>
          At (fun value => HeaderEncoding value.1 value.2.1 value.2.2)
            data pos (mode, elem, expressions) next ∧ HeaderValid env mode elem
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e => simp [metadata.decode_element_header, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨tag, first⟩ := pair
    obtain ⟨fb, hf, hfs⟩ := At.of_u32 hp
    simp only [metadata.decode_element_header, hr, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    change (if tag > 7#u32 then _ else _) ⦃_⦄
    by_cases htag : tag > 7#u32
    · rw [if_pos htag]
      simp
    · rw [if_neg htag]
      have hc : tag = 0#u32 ∨ tag = 1#u32 ∨ tag = 2#u32 ∨ tag = 3#u32 ∨
          tag = 4#u32 ∨ tag = 5#u32 ∨ tag = 6#u32 ∨ tag = 7#u32 := by scalar_tac
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        simp only [show (0#u32 % 2#u32 : Result U32) = .ok 0#u32 from by rfl,
          show (1#u32 % 2#u32 : Result U32) = .ok 1#u32 from by rfl,
          show (2#u32 % 2#u32 : Result U32) = .ok 0#u32 from by rfl,
          show (3#u32 % 2#u32 : Result U32) = .ok 1#u32 from by rfl,
          show (4#u32 % 2#u32 : Result U32) = .ok 0#u32 from by rfl,
          show (5#u32 % 2#u32 : Result U32) = .ok 1#u32 from by rfl,
          show (6#u32 % 2#u32 : Result U32) = .ok 0#u32 from by rfl,
          show (7#u32 % 2#u32 : Result U32) = .ok 1#u32 from by rfl, bind_ok]
        simp
      · step
        split
        · simp
        · obtain ⟨r, hconst, hc⟩ := WP.spec_imp_exists
            (metadata.decode_const_expr.spec data first env .I32)
          rw [hconst]
          cases r with
          | Err e => simp [
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok pair =>
            obtain ⟨offset, offsetNext⟩ := pair
            obtain ⟨⟨ob, ho, hos⟩, hv⟩ := hc
            simp only [bind_ok]
            step
            split
            · simp
            · have hi : (0#u32).val < env.tables.val.length := by scalar_tac
              simp only [wasm_types.ElemType.value_type, bind_ok]
              step as ⟨tt, tt_post⟩
              cases ht : tt.ty.elem <;>
                simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
                  wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq]
              all_goals
                exact ⟨⟨fb ++ ob, by
                      simp only [HeaderEncoding, ElementHeaderEncoding, Source.bytes, List.map_append, List.map_cons, List.map_nil]
                      exact WebAssembly.Binary.ElementHeaderEncoding.activeIndices ((Leb128.encoding_iff _ _).mp hf) ho, hfs.append hos⟩,
                  hi, (by
                    have hrval : r.val = (0#u32).val := by scalar_tac
                    simpa [tt_post, hrval] using ht), hv⟩
      · obtain ⟨r, hkind, hk⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data first)
        change (reader.read_byte data _ >>= _) ⦃_⦄
        rw [hkind]
        cases r with
        | Err e => simp [
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          error.Error.Insts.CoreConvertFromOpError.from]
        | Ok pair =>
          obtain ⟨kind, kindNext⟩ := pair
          by_cases hz : kind = 0#u8
          · subst kind
            have hks := At.byte hk
            simp
            exact ⟨⟨fb ++ [0#u8], by
                      simp only [HeaderEncoding, ElementHeaderEncoding, Source.bytes, List.map_append, List.map_cons, List.map_nil]
                      exact WebAssembly.Binary.ElementHeaderEncoding.passiveIndices ((Leb128.encoding_iff _ _).mp hf), hfs.append hks⟩, trivial⟩
          · have hn : kind.val ≠ 0 := fun h => hz (UScalar.eq_of_val_eq h)
            simp [hn]
      · obtain ⟨r, hindex, hi⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data first)
        rw [hindex]
        cases r with
        | Err e => simp [
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          error.Error.Insts.CoreConvertFromOpError.from]
        | Ok pair =>
          obtain ⟨index, indexNext⟩ := pair
          obtain ⟨ib, hindexEnc, his⟩ := At.of_u32 hi
          simp only [bind_ok]
          step
          split
          · simp
          · obtain ⟨r, hconst, hc⟩ := WP.spec_imp_exists
              (metadata.decode_const_expr.spec data indexNext env .I32)
            rw [hconst]
            cases r with
            | Err e => simp [
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from]
            | Ok pair =>
              obtain ⟨offset, offsetNext⟩ := pair
              obtain ⟨⟨ob, ho, hos⟩, hv⟩ := hc
              simp only [bind_ok]
              obtain ⟨r, hkind, hk⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data offsetNext)
              change (reader.read_byte data _ >>= _) ⦃_⦄
              rw [hkind]
              cases r with
              | Err e => simp [
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                error.Error.Insts.CoreConvertFromOpError.from]
              | Ok pair =>
                obtain ⟨kind, kindNext⟩ := pair
                by_cases hz : kind = 0#u8
                · subst kind
                  have hks := At.byte hk
                  simp
                  step
                  split
                  · simp
                  · have hi : (index).val < env.tables.val.length := by scalar_tac
                    simp only [wasm_types.ElemType.value_type, bind_ok]
                    step as ⟨tt, tt_post⟩
                    cases ht : tt.ty.elem <;>
                      simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
                        wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq]
                    all_goals
                      exact ⟨⟨fb ++ ib ++ ob ++ [0#u8], by
                      simp only [HeaderEncoding, ElementHeaderEncoding, Source.bytes, List.map_append, List.map_cons, List.map_nil]
                      exact WebAssembly.Binary.ElementHeaderEncoding.explicitIndices ((Leb128.encoding_iff _ _).mp hf) ((Leb128.encoding_iff _ _).mp hindexEnc) ho, ((hfs.append his).append hos).append hks⟩,
                        hi, (by
                          have hentry : tt = env.tables.val[index.val] := by
                            rw [tt_post]
                            congr 1
                            scalar_tac
                          simpa [hentry] using ht), hv⟩
                · have hn : kind.val ≠ 0 := fun h => hz (UScalar.eq_of_val_eq h)
                  simp [hn]
      · obtain ⟨r, hkind, hk⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data first)
        change (reader.read_byte data _ >>= _) ⦃_⦄
        rw [hkind]
        cases r with
        | Err e => simp [
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          error.Error.Insts.CoreConvertFromOpError.from]
        | Ok pair =>
          obtain ⟨kind, kindNext⟩ := pair
          by_cases hz : kind = 0#u8
          · subst kind
            have hks := At.byte hk
            simp
            exact ⟨⟨fb ++ [0#u8], by
                      simp only [HeaderEncoding, ElementHeaderEncoding, Source.bytes, List.map_append, List.map_cons, List.map_nil]
                      exact WebAssembly.Binary.ElementHeaderEncoding.declarativeIndices ((Leb128.encoding_iff _ _).mp hf), hfs.append hks⟩, trivial⟩
          · have hn : kind.val ≠ 0 := fun h => hz (UScalar.eq_of_val_eq h)
            simp [hn]
      · step
        split
        · simp
        · obtain ⟨r, hconst, hc⟩ := WP.spec_imp_exists
            (metadata.decode_const_expr.spec data first env .I32)
          rw [hconst]
          cases r with
          | Err e => simp [
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok pair =>
            obtain ⟨offset, offsetNext⟩ := pair
            obtain ⟨⟨ob, ho, hos⟩, hv⟩ := hc
            simp only [bind_ok]
            step
            split
            · simp
            · have hi : (0#u32).val < env.tables.val.length := by scalar_tac
              simp only [wasm_types.ElemType.value_type, bind_ok]
              step as ⟨tt, tt_post⟩
              cases ht : tt.ty.elem <;>
                simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
                  wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq]
              all_goals
                exact ⟨⟨fb ++ ob, by
                      simp only [HeaderEncoding, ElementHeaderEncoding, Source.bytes, List.map_append, List.map_cons, List.map_nil]
                      exact WebAssembly.Binary.ElementHeaderEncoding.activeExpressions ((Leb128.encoding_iff _ _).mp hf) ho, hfs.append hos⟩,
                  hi, (by
                    have hrval : r.val = (0#u32).val := by scalar_tac
                    simpa [tt_post, hrval] using ht), hv⟩
      · obtain ⟨r, helemRead, he⟩ := WP.spec_imp_exists (metadata.decode_elem_type.spec data first)
        simp only [helemRead, bind_ok]
        cases r with
        | Err e => simp [
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok pair =>
          obtain ⟨elem, elemNext⟩ := pair
          obtain ⟨eb, he, hes⟩ := he
          have heq : eb = [elemByte elem] := he
          subst eb
          simp only [bind_ok]
          exact ⟨⟨fb ++ [elemByte elem], by
                      simp only [HeaderEncoding, ElementHeaderEncoding, Source.bytes, List.map_append, List.map_cons, List.map_nil]
                      exact WebAssembly.Binary.ElementHeaderEncoding.passiveExpressions ((Leb128.encoding_iff _ _).mp hf), hfs.append hes⟩, trivial⟩
      · obtain ⟨r, hindex, hi⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data first)
        rw [hindex]
        cases r with
        | Err e => simp [
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          error.Error.Insts.CoreConvertFromOpError.from]
        | Ok pair =>
          obtain ⟨index, indexNext⟩ := pair
          obtain ⟨ib, hindexEnc, his⟩ := At.of_u32 hi
          simp only [bind_ok]
          step
          split
          · simp
          · obtain ⟨r, hconst, hc⟩ := WP.spec_imp_exists
              (metadata.decode_const_expr.spec data indexNext env .I32)
            rw [hconst]
            cases r with
            | Err e => simp [
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok pair =>
              obtain ⟨offset, offsetNext⟩ := pair
              obtain ⟨⟨ob, ho, hos⟩, hv⟩ := hc
              simp only [bind_ok]
              let Target : WP.Post (core.result.Result (metadata.ElementMode × wasm_types.ElemType × Bool × Usize) error.Error) :=
                fun result => match result with
                  | .Ok (mode, elem, expressions, next) =>
                      At (fun value => HeaderEncoding value.1 value.2.1 value.2.2)
                        data pos (mode, elem, expressions) next ∧ HeaderValid env mode elem
                  | .Err _ => True
              change ((metadata.decode_elem_type data offsetNext >>= _) :
                Result (core.result.Result (metadata.ElementMode × wasm_types.ElemType × Bool × Usize) error.Error)) ⦃ Target ⦄
              obtain ⟨r, helemRead, he⟩ := WP.spec_imp_exists (metadata.decode_elem_type.spec data offsetNext)
              simp only [helemRead]
              cases r with
              | Err e => simp [Target,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
              | Ok pair =>
                obtain ⟨elem, elemNext⟩ := pair
                obtain ⟨eb, he, hes⟩ := he
                have heq : eb = [elemByte elem] := he
                subst eb
                try with_unfolding_all simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
                step
                split
                · simp [Target]
                · have hi : (index).val < env.tables.val.length := by scalar_tac
                  have hty : wasm_types.ElemType.value_type elem = .ok (Module.Constants.referenceValueType elem) := by
                    cases elem <;> rfl
                  rw [hty]
                  simp only [bind_ok]
                  step as ⟨tt, tt_post⟩
                  cases elem <;> cases ht : tt.ty.elem <;>
                    simp [Target, wasm_types.ElemType.value_type, Module.Constants.referenceValueType,
                      core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
                      wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq]
                  all_goals
                    exact ⟨⟨fb ++ ib ++ ob ++ [_], by
                      simp only [HeaderEncoding, ElementHeaderEncoding, Source.bytes, List.map_append, List.map_cons, List.map_nil]
                      exact WebAssembly.Binary.ElementHeaderEncoding.explicitExpressions ((Leb128.encoding_iff _ _).mp hf) ((Leb128.encoding_iff _ _).mp hindexEnc) ho, ((hfs.append his).append hos).append hes⟩,
                      hi, (by
                        have hentry : tt = env.tables.val[index.val] := by
                          rw [tt_post]
                          congr 1
                          scalar_tac
                        simpa [hentry] using ht), hv⟩
      · obtain ⟨r, helemRead, he⟩ := WP.spec_imp_exists (metadata.decode_elem_type.spec data first)
        simp only [helemRead, bind_ok]
        cases r with
        | Err e => simp [
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok pair =>
          obtain ⟨elem, elemNext⟩ := pair
          obtain ⟨eb, he, hes⟩ := he
          have heq : eb = [elemByte elem] := he
          subst eb
          simp only [bind_ok]
          exact ⟨⟨fb ++ [elemByte elem], by
                      simp only [HeaderEncoding, ElementHeaderEncoding, Source.bytes, List.map_append, List.map_cons, List.map_nil]
                      exact WebAssembly.Binary.ElementHeaderEncoding.declarativeExpressions ((Leb128.encoding_iff _ _).mp hf), hfs.append hes⟩, trivial⟩

end Itasca

open Aeneas Aeneas.Std

namespace Itasca
open Binary Module.Elements

/-- An accepted `metadata.decode_element` is an `ElementEncoding` span of a valid element. The
declared functions grow by its references, and the cursor advances. -/
@[step]
theorem metadata.decode_element.spec (data : Slice U8) (pos : Usize)
    (env : metadata.CodeMetadata)
    :
    metadata.decode_element data pos env ⦃ r => match r.1 with
      | .Ok (entry, next) =>
          At ElementEncoding data pos (Module.Environment.rawElement entry) next ∧
          Module.References.Added env r.2 (Module.References.element entry) ∧
          Module.Segments.elementValid env entry ∧
          pos.val < next.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (metadata.decode_element_header.spec data pos env)
  cases r with
  | Err e => simp [metadata.decode_element, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok tuple =>
    obtain ⟨mode, elem, expressions, middle⟩ := tuple
    obtain ⟨hheader, hvalid⟩ := hp
    have hspan := hheader.span
    obtain ⟨⟨r, result⟩, hinit, hp⟩ := WP.spec_imp_exists
      (metadata.decode_element_initializers.spec data middle env elem expressions)
    cases r with
    | Err e => simp [metadata.decode_element, hr, hinit, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      obtain ⟨init, next⟩ := pair
      obtain ⟨hib, hadded, hiv⟩ := hp
      simp [metadata.decode_element, hr, hinit, core.result.Result.Insts.CoreOpsTry.branch]
      obtain ⟨fb, hf, hfs⟩ := hheader
      have hty := HeaderEncoding.initializer_type hf
      have hprogress : middle.val < next.val := by
        obtain ⟨count, content, hn, hc, hi⟩ := hib.vector_split
        have := hc.span
        have := hi.span
        omega
      obtain ⟨ib, hi, his⟩ := hib
      cases init <;> refine ⟨⟨fb ++ ib, HeaderEncoding.append hf hi, hfs.append his⟩, ?_,
        ⟨hvalid, (by simpa only [hty, initValues, Module.Environment.rawElement] using hiv)⟩, by omega⟩
      all_goals simpa [initValues, Module.References.element, Module.References.initializer, List.flatMap_map] using hadded

end Itasca

end
