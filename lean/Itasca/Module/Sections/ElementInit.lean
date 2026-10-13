import Itasca.Module.Const.Parser
import Itasca.Module.Env.References
import Itasca.Module.Elab.SegmentSyntax

/-!
# Element initializer parsers

Soundness of `module.decode_element_initializer` and `module.decode_element_initializers`, which
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
def InitializerEncoding (expressions : Bool) (value : types.ConstExpr) (bytes : List U8) : Prop :=
  if expressions then ModuleBinary.ConstEncoding value bytes
  else ∃ index, value = .RefFunc index ∧ ModuleBinary.IndexEncoding index bytes

/-- The value type of an initializer: the element type for expressions, and `funcref` for
function indices. -/
def initializerType (elem : types.ElemType) (expressions : Bool) : types.ValueType :=
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

/-- An accepted `module.decode_element_initializer` is an `InitializerEncoding` span whose value is
`Valid` at `initializerType`. -/
@[step]
theorem module.decode_element_initializer.spec (data : Slice U8) (pos : Usize)
    (env : module.Env) (elem : types.ElemType) (expressions : Bool) (profile : ValidationProfile) :
    module.decode_element_initializer data pos env elem expressions profile ⦃ r => match r with
      | .Ok (value, next) =>
          ModuleBinary.At (ModuleElements.InitializerEncoding expressions) data pos value next ∧
          ModuleConstants.Valid env value (ModuleElements.initializerType elem expressions)
      | .Err _ => True ⦄ := by
  cases expressions with
  | true =>
    have ht : types.ElemType.value_type elem = .ok (ModuleConstants.referenceValueType elem) := by
      cases elem <;> rfl
    simp only [module.decode_element_initializer, ↓reduceIte, ht, bind_ok]
    apply WP.spec_mono (module.decode_const_expr.spec data pos env (ModuleConstants.referenceValueType elem) profile)
    intro r hp
    cases r with
    | Err _ => trivial
    | Ok pair => exact hp

  | false =>
    obtain ⟨r, hr, hb⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
    cases r with
    | Err e => simp [module.decode_element_initializer, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from]
    | Ok pair =>
      obtain ⟨idx, next⟩ := pair
      simp [module.decode_element_initializer, hr, core.result.Result.Insts.CoreOpsTry.branch]
      step
      split
      · simp
      · have hi : idx.val < env.func_types.val.length := by scalar_tac
        obtain ⟨bytes, he, hs⟩ := ModuleBinary.At.of_u32 hb
        exact ⟨⟨bytes, ⟨idx, rfl, he⟩, hs⟩, .refFunc idx hi⟩

/-- The initializer loop returns `count` initializers forming a `Rep` span, all valid, and extends
only the declared functions, by their references. -/
theorem module.decode_element_initializers_loop.spec (data : Slice U8) (env : module.Env)
    (elem : types.ElemType) (expressions : Bool) (profile : ValidationProfile)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hrefs : env.declared_funcs.val.length ≤ start.val) :
    module.decode_element_initializers_loop data env elem expressions profile count start
      (alloc.vec.Vec.new _) 0#u32 ⦃ r => match r.1 with
      | .Ok (values, next) => values.val.length = count.val ∧
          ModuleReferences.Added env r.2 (values.val.flatMap ModuleReferences.initializer) ∧
          ModuleBinary.At (ModuleBinary.Rep (ModuleElements.InitializerEncoding expressions))
            data start values.val next ∧
          (∀ value ∈ values.val, ModuleConstants.Valid env value (ModuleElements.initializerType elem expressions)) ∧
          r.2.declared_funcs.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  unfold module.decode_element_initializers_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.2.val)
    (fun s => s.2.2.2.val ≤ count.val ∧ s.2.2.1.val.length = s.2.2.2.val ∧
      ModuleReferences.Added env s.1 (s.2.2.1.val.flatMap ModuleReferences.initializer) ∧
      ModuleBinary.At (ModuleBinary.Rep (ModuleElements.InitializerEncoding expressions))
        data start s.2.2.1.val s.2.1 ∧
      (∀ value ∈ s.2.2.1.val, ModuleConstants.Valid env value (ModuleElements.initializerType elem expressions)) ∧
      s.1.declared_funcs.val.length ≤ s.2.1.val)
  · rintro ⟨current, pos, values, i⟩ ⟨hi, hlen, henv, hbytes, hvalid, hbound⟩
    dsimp only at hi hlen henv hbytes hvalid hbound
    unfold module.decode_element_initializers_loop.body
    dsimp only
    split
    · have heq : i.val = count.val := by scalar_tac
      exact ⟨by omega, henv, hbytes, hvalid, hbound⟩
    · obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists
        (module.decode_element_initializer.spec data pos current elem expressions profile)
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

/-- `module.decode_element_initializers` returns the initializers of a `VecEncoding` span, all
valid, and extends only the declared functions, by their references. -/
theorem module.decode_element_initializers.spec (data : Slice U8) (pos : Usize)
    (env : module.Env) (elem : types.ElemType) (expressions : Bool) (profile : ValidationProfile)
    (hrefs : env.declared_funcs.val.length ≤ pos.val) :
    module.decode_element_initializers data pos env elem expressions profile ⦃ r => match r.1 with
      | .Ok (values, next) =>
          ModuleBinary.At (ModuleBinary.VecEncoding (ModuleElements.InitializerEncoding expressions))
            data pos values.val next ∧
          ModuleReferences.Added env r.2 (values.val.flatMap ModuleReferences.initializer) ∧
          (∀ value ∈ values.val, ModuleConstants.Valid env value (ModuleElements.initializerType elem expressions)) ∧
          r.2.declared_funcs.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e => simp [module.decode_element_initializers, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨count, start⟩ := pair
    have hs := hc.span
    obtain ⟨r, hloop, hp⟩ := WP.spec_imp_exists
      (module.decode_element_initializers_loop.spec data env elem expressions profile count start
        hs.2.2 (by omega))
    obtain ⟨res, result⟩ := r
    simp [module.decode_element_initializers, hr, hloop, core.result.Result.Insts.CoreOpsTry.branch]
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
