import Itasca.Module.Env.Basic
import Itasca.Module.Readers.Types
import Itasca.Module.Readers.Utf8
import Itasca.Module.Const.Parser
import Itasca.Module.Env.Externals
import Itasca.Module.Elab.SegmentTyping

/-!
Sections, each formerly its own module: Type, DataCount, ElementInit, ElementHeader.
-/

/-! ## Type -/

section

/-!
# Type section parser

Soundness of `metadata.decode_type_section` and its loop. `TypesAdded` says the environment gains
exactly the decoded signatures. The `profile_spec` forms give a `VecEncoding FuncTypeEncoding`
span whose signatures satisfy the completeness caps. Completeness is in `Module/Sections/TypeComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- A repetition span extends by one element at its end. -/
theorem At.snoc {α : Type} {R : α → List U8 → Prop} {data start pos next values value}
    (h : At (Rep R) data start values pos) (h' : At R data pos value next) :
    At (Rep R) data start (values ++ [value]) next := by
  obtain ⟨bytes, hr, hs⟩ := h
  obtain ⟨last, he, ht⟩ := h'
  exact ⟨bytes ++ last, hr.snoc he, hs.append ht⟩

/-- A decoded count, a repetition of that many elements and their span form a `VecEncoding`. -/
theorem At.vector {α : Type} {R : α → List U8 → Prop} {data start pos next count values}
    (hc : Leb128.Decoded data start count pos)
    (he : At (Rep R) data pos values next) (hlen : values.length = count.val) :
    At (VecEncoding R) data start values next := by
  obtain ⟨bytes, hr, hs⟩ := he
  obtain ⟨countBytes, hcs, hcl, hcb, hce⟩ := hc
  exact ⟨countBytes ++ bytes,
    ⟨countBytes, bytes, by simpa [hlen] using hce, hr, rfl⟩,
    (show Wasm1.BytesAt data start countBytes pos from ⟨hcs, hcl, hcb⟩).append hs⟩

/-- A function type encoding consumes at least one byte. -/
theorem At.funcType_progress {data start ty next} (h : At FuncTypeEncoding data start ty next) :
    start.val < next.val := by
  obtain ⟨bytes, ⟨params, results, _, _, rfl⟩, hs⟩ := h
  have := hs.length
  simp only [List.length_cons, List.length_append] at this
  omega

end Itasca.ModuleBinary

namespace Itasca.ModuleSections

/-- `result` is `env` with the signatures `added` appended to its type table and nothing else
changed. -/
def TypesAdded (env result : metadata.Env) (added : List wasm_types.FuncType) : Prop :=
  result = { env with types := result.types } ∧ result.types.val = env.types.val ++ added

end Itasca.ModuleSections

namespace Itasca

open ModuleBinary ModuleSections

/-- The type loop adds `count` signatures forming a `Rep FuncTypeEncoding` span. Each satisfies the
completeness caps. -/
@[step]
theorem metadata.decode_type_section_loop.profile_spec (data : Slice U8) (env : metadata.Env)
     (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hsize : env.types.val.length ≤ start.val) :
    metadata.decode_type_section_loop data env count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ added, added.length = count.val ∧ TypesAdded env r.2 added ∧
          At (Rep FuncTypeEncoding) data start added next ∧
          (∀ ft ∈ added, Profile.FuncTypeWithinLimits ft) ∧ r.2.types.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  unfold metadata.decode_type_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ added, added.length = s.2.2.val ∧
      TypesAdded env s.1 added ∧ At (Rep FuncTypeEncoding) data start added s.2.1 ∧
      (∀ ft ∈ added, Profile.FuncTypeWithinLimits ft) ∧ s.1.types.val.length ≤ s.2.1.val)
  · rintro ⟨current, pos, i⟩ ⟨hi, added, hlen, henv, hbytes, hvalid, hsize⟩
    dsimp only at hi hlen henv hbytes hvalid hsize
    unfold metadata.decode_type_section_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : i.val = count.val := by scalar_tac
      exact ⟨added, by omega, henv, hbytes, hvalid, hsize⟩
    · rename_i hmore
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (metadata.decode_func_type.profile_spec data pos)
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        obtain ⟨ft, next⟩ := pair
        obtain ⟨hb, ht⟩ := hp
        have hprogress := hb.funcType_progress
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
      ⟨[], .nil, Wasm1.BytesAt.nil data start hstart⟩, by simp, hsize⟩

/-- `metadata.decode_type_section` adds the signatures of a `VecEncoding FuncTypeEncoding` span, each
satisfying the completeness caps. -/
@[step]
theorem metadata.decode_type_section.profile_spec (data : Slice U8) (pos : Usize) (env : metadata.Env)
     (hsize : env.types.val.length ≤ pos.val) :
    metadata.decode_type_section data pos env ⦃ r => match r.1 with
      | .Ok next => ∃ added, TypesAdded env r.2 added ∧
          At (VecEncoding FuncTypeEncoding) data pos added next ∧
          (∀ ft ∈ added, Profile.FuncTypeWithinLimits ft) ∧ r.2.types.val.length ≤ next.val
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
      (metadata.decode_type_section_loop.profile_spec data env count start hs.2.2 (by omega))
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

`ModuleBinary.sectionRank` is the Wasm 2.0 section order, and `metadata.section_order` computes it
and rejects ids outside `1` to `12` (spec and `.complete`). `metadata.decode_data_count` reads the
data count section, which only Wasm 2.0 accepts, and records the count in the environment.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- The position of a section id in the Wasm 2.0 order, which places the data count section (`12`)
before code (`10`) and data (`11`). Custom sections have no rank. -/
def sectionRank (id : U8) : U8 :=
  match id.val with
  | 12 => 10#u8
  | 10 => 11#u8
  | 11 => 12#u8
  | _ => id

/-- Ranks `1` to `10` belong to the ids `1` to `9` and `12`. -/
theorem sectionRank_prefix {id : U8} (hlo : 1 ≤ (sectionRank id).val)
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

end Itasca.ModuleBinary

namespace Itasca

/-- `metadata.section_order` returns the rank of an id from `1` to `12` and rejects other ids. -/
@[step]
theorem metadata.section_order.spec (id : U8) :
    metadata.section_order id ⦃ result => match result with
      | .Ok rank => rank = ModuleBinary.sectionRank id ∧ 1 ≤ id.val ∧ id.val ≤ 12
      | .Err _ => id.val = 0 ∨ 12 < id.val ⦄ := by
  have h10 : (10#uscalar : U8).val = 10 := rfl
  have h11 : (11#uscalar : U8).val = 11 := rfl
  have h12 : (12#uscalar : U8).val = 12 := rfl
  unfold metadata.section_order
  repeat' first | split
  all_goals simp_all [ModuleBinary.sectionRank, global_simps]
  all_goals first | omega | (split <;> simp_all; omega)

/-- `metadata.section_order` accepts every id from `1` to `12`. -/
theorem metadata.section_order.complete (id : U8) (hlo : 1 ≤ id.val) (hhi : id.val ≤ 12) :
    metadata.section_order id = .ok (.Ok (ModuleBinary.sectionRank id)) := by
  obtain ⟨result, hr, hp⟩ := WP.spec_imp_exists (metadata.section_order.spec id)
  cases result with
  | Err e => rcases hp with hz | hh <;> omega
  | Ok rank => simpa only [hp.1] using hr

/-- An accepted `metadata.decode_data_count` reads a `u32` count, sets only `data_count`, and
happens under Wasm 2.0. -/
@[step]
theorem metadata.decode_data_count.spec (data : Slice U8) (pos : Usize) (env : metadata.Env) :
    metadata.decode_data_count data pos env ⦃ result => match result.1 with
      | .Ok next => ∃ count,
          ModuleBinary.At ModuleBinary.StartEncoding data pos (some count) next ∧
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
theorem metadata.decode_data_count.complete (data : Slice U8) (pos : Usize) (env : metadata.Env)
    (count : U32) (next : Usize)
    (hb : ModuleBinary.At ModuleBinary.StartEncoding data pos (some count) next) :
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
Accepted values are `ModuleConstants.Valid` at the segment's reference type, and the declared
function references grow by exactly those of the initializers (`ModuleReferences.Added`).
Completeness is in `Module/Sections/ElementInitComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleElements

/-- One initializer: either a function index standing for `ref.func`, or, when `expressions` is
set, a whole constant expression including its terminating `end`. -/
def InitializerEncoding (expressions : Bool) (value : wasm_types.ConstExpr) (bytes : List U8) : Prop :=
  if expressions then ModuleBinary.ConstEncoding value bytes
  else ∃ index, value = .RefFunc index ∧ ModuleBinary.IndexEncoding index bytes

/-- The value type of an initializer: the element type for expressions, and `funcref` for
function indices. -/
def initializerType (elem : wasm_types.ElemType) (expressions : Bool) : wasm_types.ValueType :=
  if expressions then ModuleConstants.referenceValueType elem else .FuncRef

/-- An initializer encoding consumes at least one byte. -/
theorem InitializerEncoding.nonempty {expressions value bytes}
    (h : InitializerEncoding expressions value bytes) : 0 < bytes.length := by
  cases expressions with
  | true => cases h <;> simp
  | false =>
    obtain ⟨_, _, _, _, rfl, _⟩ := h
    simp

end Itasca.ModuleElements

namespace Itasca.ModuleConstants

/-- Constant validity depends only on the function types, global types and imported global count. -/
theorem Valid.same_caches {env result value ty} (h : Valid env value ty)
    (hf : result.func_types = env.func_types)
    (hg : result.global_types = env.global_types)
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

end Itasca.ModuleConstants

namespace Itasca.ModuleReferences

/-- Validity after adding declared references implies validity before. -/
theorem Added.valid_before {before after refs value ty} (h : Added before after refs)
    (hv : ModuleConstants.Valid after value ty) : ModuleConstants.Valid before value ty := by
  apply hv.same_caches <;> rw [h.1]

/-- Reference additions compose. -/
theorem Added.trans {before middle after xs ys} (h : Added before middle xs)
    (h' : Added middle after ys) : Added before after (xs ++ ys) := by
  constructor
  · rw [h'.1, h.1]
  · rw [h'.2, h.2, List.append_assoc]

end Itasca.ModuleReferences

namespace Itasca

/-- An accepted `metadata.decode_element_initializer` is an `InitializerEncoding` span whose value is
`Valid` at `initializerType`. -/
@[step]
theorem metadata.decode_element_initializer.spec (data : Slice U8) (pos : Usize)
    (env : metadata.Env) (elem : wasm_types.ElemType) (expressions : Bool) :
    metadata.decode_element_initializer data pos env elem expressions ⦃ r => match r with
      | .Ok (value, next) =>
          ModuleBinary.At (ModuleElements.InitializerEncoding expressions) data pos value next ∧
          ModuleConstants.Valid env value (ModuleElements.initializerType elem expressions)
      | .Err _ => True ⦄ := by
  cases expressions with
  | true =>
    have ht : wasm_types.ElemType.value_type elem = .ok (ModuleConstants.referenceValueType elem) := by
      cases elem <;> rfl
    simp only [metadata.decode_element_initializer, ↓reduceIte, ht, bind_ok]
    apply WP.spec_mono (metadata.decode_const_expr.spec data pos env (ModuleConstants.referenceValueType elem))
    intro r hp
    cases r with
    | Err _ => trivial
    | Ok pair => exact hp

  | false =>
    obtain ⟨r, hr, hb⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
    cases r with
    | Err e => simp [metadata.decode_element_initializer, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from]
    | Ok pair =>
      obtain ⟨idx, next⟩ := pair
      simp [metadata.decode_element_initializer, hr, core.result.Result.Insts.CoreOpsTry.branch]
      step
      split
      · simp
      · have hi : idx.val < env.func_types.val.length := by scalar_tac
        obtain ⟨bytes, he, hs⟩ := ModuleBinary.At.of_u32 hb
        exact ⟨⟨bytes, ⟨idx, rfl, he⟩, hs⟩, .refFunc idx hi⟩

/-- The initializer loop returns `count` initializers forming a `Rep` span, all valid, and extends
only the declared functions, by their references. -/
theorem metadata.decode_element_initializers_loop.spec (data : Slice U8) (env : metadata.Env)
    (elem : wasm_types.ElemType) (expressions : Bool)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hrefs : env.declared_funcs.val.length ≤ start.val) :
    metadata.decode_element_initializers_loop data env elem expressions count start
      (alloc.vec.Vec.new _) 0#u32 ⦃ r => match r.1 with
      | .Ok (values, next) => values.val.length = count.val ∧
          ModuleReferences.Added env r.2 (values.val.flatMap ModuleReferences.initializer) ∧
          ModuleBinary.At (ModuleBinary.Rep (ModuleElements.InitializerEncoding expressions))
            data start values.val next ∧
          (∀ value ∈ values.val, ModuleConstants.Valid env value (ModuleElements.initializerType elem expressions)) ∧
          r.2.declared_funcs.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  unfold metadata.decode_element_initializers_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.2.val)
    (fun s => s.2.2.2.val ≤ count.val ∧ s.2.2.1.val.length = s.2.2.2.val ∧
      ModuleReferences.Added env s.1 (s.2.2.1.val.flatMap ModuleReferences.initializer) ∧
      ModuleBinary.At (ModuleBinary.Rep (ModuleElements.InitializerEncoding expressions))
        data start s.2.2.1.val s.2.1 ∧
      (∀ value ∈ s.2.2.1.val, ModuleConstants.Valid env value (ModuleElements.initializerType elem expressions)) ∧
      s.1.declared_funcs.val.length ≤ s.2.1.val)
  · rintro ⟨current, pos, values, i⟩ ⟨hi, hlen, henv, hbytes, hvalid, hbound⟩
    dsimp only at hi hlen henv hbytes hvalid hbound
    unfold metadata.decode_element_initializers_loop.body
    dsimp only
    split
    · have heq : i.val = count.val := by scalar_tac
      exact ⟨by omega, henv, hbytes, hvalid, hbound⟩
    · obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists
        (metadata.decode_element_initializer.spec data pos current elem expressions)
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        obtain ⟨value, next⟩ := pair
        obtain ⟨hb, hv⟩ := hp
        have hspan := hb.span
        have hprogress : pos.val < next.val := by
          obtain ⟨bytes, he, hs⟩ := hb
          have := he.nonempty
          have := hs.length
          omega
        have hcapacity : values.val.length < Usize.max := by scalar_tac
        have hrefcapacity : current.declared_funcs.val.length < Usize.max := by scalar_tac
        simp [core.result.Result.Insts.CoreOpsTry.branch]
        step as ⟨updated, hupdated⟩
        step
        step
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · scalar_tac
        · simp only [init1_post, List.length_append, List.length_singleton]
          scalar_tac
        · simpa only [init1_post, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
            List.append_nil] using henv.trans hupdated
        · obtain ⟨bytes, he, hs⟩ := hbytes
          obtain ⟨last, he', hs'⟩ := hb
          exact ⟨bytes ++ last, by simpa only [init1_post] using he.snoc he', hs.append hs'⟩
        · intro val hm
          rw [init1_post] at hm
          rcases List.mem_append.mp hm with hm | hm
          · exact hvalid val hm
          · obtain rfl := List.mem_singleton.mp hm
            exact henv.valid_before hv
        · have hn : (ModuleReferences.initializer value).length ≤ 1 := by
            cases value <;> simp [ModuleReferences.initializer]
          rw [hupdated.2, List.length_append]
          omega
        · scalar_tac
  · exact ⟨by simp, by simp, ⟨rfl, by simp⟩,
      ⟨[], .nil, Wasm1.BytesAt.nil data start hstart⟩, by simp, hrefs⟩

/-- `metadata.decode_element_initializers` returns the initializers of a `VecEncoding` span, all
valid, and extends only the declared functions, by their references. -/
theorem metadata.decode_element_initializers.spec (data : Slice U8) (pos : Usize)
    (env : metadata.Env) (elem : wasm_types.ElemType) (expressions : Bool)
    (hrefs : env.declared_funcs.val.length ≤ pos.val) :
    metadata.decode_element_initializers data pos env elem expressions ⦃ r => match r.1 with
      | .Ok (values, next) =>
          ModuleBinary.At (ModuleBinary.VecEncoding (ModuleElements.InitializerEncoding expressions))
            data pos values.val next ∧
          ModuleReferences.Added env r.2 (values.val.flatMap ModuleReferences.initializer) ∧
          (∀ value ∈ values.val, ModuleConstants.Valid env value (ModuleElements.initializerType elem expressions)) ∧
          r.2.declared_funcs.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e => simp [metadata.decode_element_initializers, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨count, start⟩ := pair
    have hs := hc.span
    obtain ⟨r, hloop, hp⟩ := WP.spec_imp_exists
      (metadata.decode_element_initializers_loop.spec data env elem expressions count start
        hs.2.2 (by omega))
    obtain ⟨res, result⟩ := r
    simp [metadata.decode_element_initializers, hr, hloop, core.result.Result.Insts.CoreOpsTry.branch]
    cases res with
    | Err e => trivial
    | Ok pair =>
      obtain ⟨values, next⟩ := pair
      obtain ⟨hlen, hadded, hbytes, hvalid, hbound⟩ := hp
      refine ⟨?_, hadded, hvalid, hbound⟩
      obtain ⟨bytes, he, hs⟩ := hbytes
      obtain ⟨cb, hcs, hcl, hcb, hce⟩ := hc
      exact ⟨cb ++ bytes, ⟨cb, bytes, by simpa [hlen] using hce, he, rfl⟩,
        (show Wasm1.BytesAt data pos cb start from ⟨hcs, hcl, hcb⟩).append hs⟩

end Itasca

end

/-! ## ElementHeader -/

section

/-!
# Element segment header and entry parser

`ModuleElements.HeaderEncoding` is the independent grammar of the flag word and prefix of an
element segment in one of the eight Wasm 2.0 forms.
`metadata.decode_element_header.spec` shows an accepted header is a `HeaderEncoding` span whose
table and offset are valid. `metadata.decode_element.spec` assembles a full entry: an
`ElementEncodingFor` span that is valid, extends the declared functions by its references and
consumes input. Completeness is in `Module/Sections/ElementHeaderComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleElements
open ModuleBinary

/-- The bytes of an element segment header for a mode, element type and initializer
form (`true` for expressions). The first argument of each constructor is the flag word. -/
inductive HeaderEncoding : metadata.ElementMode → wasm_types.ElemType → Bool → List U8 → Prop where
  | activeIndices {offset fb ob} : IndexEncoding 0#u32 fb → ConstEncoding offset ob →
      HeaderEncoding (.Active 0#u32 offset) .FuncRef false (fb ++ ob)
  | passiveIndices {fb} : IndexEncoding 1#u32 fb →
      HeaderEncoding .Passive .FuncRef false (fb ++ [0#u8])
  | explicitIndices {index offset fb ib ob} : IndexEncoding 2#u32 fb →
      IndexEncoding index ib → ConstEncoding offset ob →
      HeaderEncoding (.Active index offset) .FuncRef false (fb ++ ib ++ ob ++ [0#u8])
  | declarativeIndices {fb} : IndexEncoding 3#u32 fb →
      HeaderEncoding .Declarative .FuncRef false (fb ++ [0#u8])
  | activeExpressions {offset fb ob} : IndexEncoding 4#u32 fb → ConstEncoding offset ob →
      HeaderEncoding (.Active 0#u32 offset) .FuncRef true (fb ++ ob)
  | passiveExpressions {elem fb} : IndexEncoding 5#u32 fb →
      HeaderEncoding .Passive elem true (fb ++ [elemByte elem])
  | explicitExpressions {elem index offset fb ib ob} : IndexEncoding 6#u32 fb →
      IndexEncoding index ib → ConstEncoding offset ob →
      HeaderEncoding (.Active index offset) elem true (fb ++ ib ++ ob ++ [elemByte elem])
  | declarativeExpressions {elem fb} : IndexEncoding 7#u32 fb →
      HeaderEncoding .Declarative elem true (fb ++ [elemByte elem])

/-- An active segment names an in-range table of the segment's element type with a valid `i32`
offset. Passive and declarative segments have no condition. -/
def HeaderValid (env : metadata.Env) (mode : metadata.ElementMode) (elem : wasm_types.ElemType) : Prop :=
  match mode with
  | .Active index offset => ∃ hi : index.val < env.table_types.val.length,
      env.table_types.val[index.val].elem = elem ∧ ModuleConstants.Valid env offset .I32
  | .Passive | .Declarative => True

private theorem indices_rep {values bytes}
    (h : Rep (InitializerEncoding false) values bytes) :
    ∃ indices, values = indices.map wasm_types.ConstExpr.RefFunc ∧ Rep IndexEncoding indices bytes := by
  induction h with
  | nil => exact ⟨[], rfl, .nil⟩
  | cons hv hs ih =>
    obtain ⟨index, rfl, hi⟩ := hv
    obtain ⟨indices, rfl, hrep⟩ := ih
    exact ⟨index :: indices, rfl, .cons hi hrep⟩

/-- A vector of index initializers is a vector of function indices. -/
theorem indices_vector {values bytes}
    (h : VecEncoding (InitializerEncoding false) values bytes) :
    ∃ indices, values = indices.map wasm_types.ConstExpr.RefFunc ∧ VecEncoding IndexEncoding indices bytes := by
  obtain ⟨count, encoded, hc, hr, rfl⟩ := h
  obtain ⟨indices, rfl, hi⟩ := indices_rep hr
  exact ⟨indices, rfl, count, encoded, by simpa using hc, hi, rfl⟩

/-- A header followed by an initializer vector is an `ElementEncodingFor` entry. -/
theorem HeaderEncoding.append {mode elem expressions header init bytes}
    (h : HeaderEncoding mode elem expressions header)
    (hi : VecEncoding (InitializerEncoding expressions) init bytes) :
    ElementEncodingFor ⟨elem, mode, init⟩ (header ++ bytes) := by
  cases h with
  | activeIndices hf ho =>
    obtain ⟨indices, rfl, hindices⟩ := indices_vector hi
    exact .activeIndices hf ho hindices
  | passiveIndices hf =>
    obtain ⟨indices, rfl, hindices⟩ := indices_vector hi
    exact .passiveIndices hf hindices
  | explicitIndices hf ht ho =>
    obtain ⟨indices, rfl, hindices⟩ := indices_vector hi
    exact .explicitIndices hf ht ho hindices
  | declarativeIndices hf =>
    obtain ⟨indices, rfl, hindices⟩ := indices_vector hi
    exact .declarativeIndices hf hindices
  | activeExpressions hf ho => exact .activeExpressions hf ho hi
  | passiveExpressions hf => exact .passiveExpressions hf hi
  | explicitExpressions hf ht ho => exact .explicitExpressions hf ht ho hi
  | declarativeExpressions hf => exact .declarativeExpressions hf hi

/-- The initializer type of a header is the reference type of its element type. -/
theorem HeaderEncoding.initializer_type {mode elem expressions bytes}
    (h : HeaderEncoding mode elem expressions bytes) :
    initializerType elem expressions = ModuleConstants.referenceValueType elem := by
  cases h <;> rfl

/-- A vector of function indices is a vector of index initializers. -/
theorem indices_vector_intro {indices bytes} (h : VecEncoding IndexEncoding indices bytes) :
    VecEncoding (InitializerEncoding false) (indices.map wasm_types.ConstExpr.RefFunc) bytes := by
  obtain ⟨count, encoded, hc, hr, rfl⟩ := h
  refine ⟨count, encoded, by simpa using hc, ?_, rfl⟩
  clear hc
  induction hr with
  | nil => exact .nil
  | cons hv hs ih => exact .cons ⟨_, rfl, hv⟩ ih

/-- An `ElementEncodingFor` entry splits into a header and an initializer vector. -/
theorem header_parts {entry bytes} (h : ElementEncodingFor entry bytes) :
    ∃ expressions header encoded, HeaderEncoding entry.mode entry.elem expressions header ∧
      VecEncoding (InitializerEncoding expressions) entry.init encoded ∧ bytes = header ++ encoded := by
  cases h with
  | activeIndices hf ho hi => exact ⟨false, _, _, .activeIndices hf ho, indices_vector_intro hi, rfl⟩
  | passiveIndices hf hi => exact ⟨false, _, _, .passiveIndices hf, indices_vector_intro hi, rfl⟩
  | explicitIndices hf ht ho hi => exact ⟨false, _, _, .explicitIndices hf ht ho, indices_vector_intro hi, rfl⟩
  | declarativeIndices hf hi => exact ⟨false, _, _, .declarativeIndices hf, indices_vector_intro hi, rfl⟩
  | activeExpressions hf ho hi => exact ⟨true, _, _, .activeExpressions hf ho, hi, rfl⟩
  | passiveExpressions hf hi => exact ⟨true, _, _, .passiveExpressions hf, hi, rfl⟩
  | explicitExpressions hf ht ho hi => exact ⟨true, _, _, .explicitExpressions hf ht ho, hi, rfl⟩
  | declarativeExpressions hf hi => exact ⟨true, _, _, .declarativeExpressions hf, hi, rfl⟩

end Itasca.ModuleElements

namespace Itasca
open ModuleBinary ModuleElements

/-- An accepted `metadata.decode_element_header` is a `HeaderEncoding` span with a `HeaderValid`
mode and element type. -/
@[step]
theorem metadata.decode_element_header.spec (data : Slice U8) (pos : Usize)
    (env : metadata.Env) :
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
            · have hi : (0#u32).val < env.table_types.val.length := by scalar_tac
              simp only [wasm_types.ElemType.value_type, bind_ok]
              step
              cases ht : tt.elem <;>
                simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
                  wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq]
              all_goals
                exact ⟨⟨fb ++ ob, .activeIndices hf ho, hfs.append hos⟩,
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
            exact ⟨⟨fb ++ [0#u8], .passiveIndices hf, hfs.append hks⟩, trivial⟩
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
                  · have hi : (index).val < env.table_types.val.length := by scalar_tac
                    simp only [wasm_types.ElemType.value_type, bind_ok]
                    step
                    cases ht : tt.elem <;>
                      simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
                        wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq]
                    all_goals
                      exact ⟨⟨fb ++ ib ++ ob ++ [0#u8], .explicitIndices hf hindexEnc ho, ((hfs.append his).append hos).append hks⟩,
                        hi, (by
                          have hentry : tt = env.table_types.val[index.val] := by
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
            exact ⟨⟨fb ++ [0#u8], .declarativeIndices hf, hfs.append hks⟩, trivial⟩
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
            · have hi : (0#u32).val < env.table_types.val.length := by scalar_tac
              simp only [wasm_types.ElemType.value_type, bind_ok]
              step
              cases ht : tt.elem <;>
                simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
                  wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq]
              all_goals
                exact ⟨⟨fb ++ ob, .activeExpressions hf ho, hfs.append hos⟩,
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
          exact ⟨⟨fb ++ [elemByte elem], .passiveExpressions hf, hfs.append hes⟩, trivial⟩
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
                · have hi : (index).val < env.table_types.val.length := by scalar_tac
                  have hty : wasm_types.ElemType.value_type elem = .ok (ModuleConstants.referenceValueType elem) := by
                    cases elem <;> rfl
                  rw [hty]
                  simp only [bind_ok]
                  step
                  cases elem <;> cases ht : tt.elem <;>
                    simp [Target, wasm_types.ElemType.value_type, ModuleConstants.referenceValueType,
                      core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
                      wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq]
                  all_goals
                    exact ⟨⟨_, .explicitExpressions hf hindexEnc ho, ((hfs.append his).append hos).append hes⟩,
                      hi, (by
                        have hentry : tt = env.table_types.val[index.val] := by
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
          exact ⟨⟨fb ++ [elemByte elem], .declarativeExpressions hf, hfs.append hes⟩, trivial⟩

end Itasca

open Aeneas Aeneas.Std

namespace Itasca
open ModuleBinary ModuleElements

/-- An accepted `metadata.decode_element` is an `ElementEncodingFor` span of a valid element. The
declared functions grow by its references, and the cursor advances. -/
@[step]
theorem metadata.decode_element.spec (data : Slice U8) (pos : Usize)
    (env : metadata.Env)
    (hrefs : env.declared_funcs.val.length ≤ pos.val) :
    metadata.decode_element data pos env ⦃ r => match r.1 with
      | .Ok (entry, next) =>
          At (ElementEncodingFor) data pos ⟨entry.elem, entry.mode, entry.init.val⟩ next ∧
          ModuleReferences.Added env r.2 (ModuleReferences.element entry) ∧
          ModuleSegments.elementValid env entry ∧
          r.2.declared_funcs.val.length ≤ next.val ∧ pos.val < next.val
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
      (metadata.decode_element_initializers.spec data middle env elem expressions (by omega))
    cases r with
    | Err e => simp [metadata.decode_element, hr, hinit, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      obtain ⟨init, next⟩ := pair
      obtain ⟨hib, hadded, hiv, hbound⟩ := hp
      simp [metadata.decode_element, hr, hinit, core.result.Result.Insts.CoreOpsTry.branch]
      obtain ⟨fb, hf, hfs⟩ := hheader
      have hty := hf.initializer_type
      have hprogress : middle.val < next.val := by
        obtain ⟨count, content, hn, hc, hi⟩ := hib.vector_split
        have := hc.span
        have := hi.span
        omega
      obtain ⟨ib, hi, his⟩ := hib
      exact ⟨⟨fb ++ ib, hf.append hi, hfs.append his⟩, hadded,
        ⟨hvalid, (by simpa only [hty] using hiv)⟩, hbound, by omega⟩

end Itasca

end
