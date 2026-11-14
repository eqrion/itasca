import Itasca.Module.Sections.ElementHeader
import Itasca.Module.Const.ParserComplete
import Itasca.Module.Env.Requirements
import Itasca.Module.Sections.Tail
import Itasca.Module.Readers.Utf8
import Itasca.Module.Sections.Data
import Itasca.Module.Readers.TypesComplete
import Mathlib.Data.List.Nodup

/-!
Sections, each formerly its own module: ElementInitComplete, ElementHeaderComplete, ElementComplete, ExportComplete, FunctionComplete, GlobalComplete.
-/

/-! ## ElementInitComplete -/

section

/-!
# Completeness of the element initializer parsers

`metadata.decode_element_initializer.complete` and `metadata.decode_element_initializers.complete`:
independently encoded initializers that are `ModuleConstants.Valid` at `initializerType` are accepted, and the declared functions gain their references.
Soundness is in `Module/Sections/ElementInit`.
-/

open Aeneas Aeneas.Std

namespace Itasca
open ModuleBinary ModuleElements

/-- `metadata.decode_element_initializer` accepts a valid `InitializerEncoding` span. -/
theorem metadata.decode_element_initializer.complete {data : Slice U8} {pos next : Usize}
    {env : metadata.Env} {elem : wasm_types.ElemType} {expressions : Bool}
    {value : wasm_types.ConstExpr}
    (hb : At (InitializerEncoding expressions) data pos value next)
    (hv : ModuleConstants.Valid env value (initializerType elem expressions)) :
    metadata.decode_element_initializer data pos env elem expressions = .ok (.Ok (value, next)) := by
  cases expressions with
  | true =>
    have hty : wasm_types.ElemType.value_type elem = .ok (ModuleConstants.referenceValueType elem) := by
      cases elem <;> rfl
    simp only [metadata.decode_element_initializer, ↓reduceIte, hty, bind_ok]
    exact metadata.decode_const_expr.complete hb hv
  | false =>
    obtain ⟨bytes, ⟨index, rfl, hi⟩, hs⟩ := hb
    have hread := hs.read_u32 index hi
    have hvalid : index.val < env.func_types.val.length := by cases hv; assumption
    have hx : metadata.decode_element_initializer data pos env elem false ⦃ r => r = .Ok (.RefFunc index, next) ⦄ := by
      simp [metadata.decode_element_initializer, hread, core.result.Result.Insts.CoreOpsTry.branch]
      step
      have hguard : ¬env.func_types.val.length ≤ i.val := by scalar_tac
      simp [hguard]
    obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hx
    exact hr

/-- The initializer loop accepts the remaining valid initializers of a repetition span and
appends them to `out`. -/
theorem metadata.decode_element_initializers_loop.complete
    (data : Slice U8) (env : metadata.Env) (elem : wasm_types.ElemType) (expressions : Bool)
     (count : U32) (pos : Usize) (out : alloc.vec.Vec wasm_types.ConstExpr) (i : U32)
    (values : List wasm_types.ConstExpr) (next : Usize)
    (hb : At (Rep (InitializerEncoding expressions)) data pos values next)
    (hc : i.val + values.length = count.val) (hlen : out.val.length ≤ i.val)
    (hrefs : env.declared_funcs.val.length ≤ pos.val)
    (hv : ∀ value ∈ values, ModuleConstants.Valid env value (initializerType elem expressions)) :
    ∃ result actual, metadata.decode_element_initializers_loop data env elem expressions count pos out i =
      .ok (.Ok (actual, next), result) ∧ actual.val = out.val ++ values ∧
      ModuleReferences.Added env result (values.flatMap ModuleReferences.initializer) := by
  induction values generalizing env pos out i with
  | nil =>
    have he := hb.rep_nil
    have hstop : i ≥ count := by simp only [List.length_nil, Nat.add_zero] at hc; scalar_tac
    refine ⟨env, out, ?_, by simp, ⟨rfl, by simp⟩⟩
    unfold metadata.decode_element_initializers_loop
    rw [loop]
    simp [metadata.decode_element_initializers_loop.body, hstop, he]
  | cons value values ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hb.rep_cons
    have hmore : ¬i ≥ count := by simp only [List.length_cons] at hc; scalar_tac
    have hread := metadata.decode_element_initializer.complete hfirst (hv value (by simp))
    have hprogress : pos.val < middle.val := by
      obtain ⟨bytes, he, hs⟩ := hfirst
      have := he.nonempty
      have := hs.length
      omega
    obtain ⟨updated, hdeclare, hadded⟩ := WP.spec_imp_exists
      (metadata.declare_initializer.spec env value (by scalar_tac))
    obtain ⟨newOut, hpush, hvalues⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec out value (by simp only [List.length_cons] at hc; scalar_tac))
    obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
      (U32.add_spec (x := i) (y := 1#u32) (by simp only [List.length_cons] at hc; scalar_tac))
    have hnewrefs : updated.declared_funcs.val.length ≤ middle.val := by
      have hlen : (ModuleReferences.initializer value).length ≤ 1 := by cases value <;> simp [ModuleReferences.initializer]
      rw [hadded.2, List.length_append]
      omega
    obtain ⟨result, actual, hloop, hactual, htail⟩ := ih updated middle newOut j hrest
      (by simp only [List.length_cons] at hc; scalar_tac)
      (by simp only [hvalues, List.length_append, List.length_singleton]; scalar_tac)
      hnewrefs
      (by intro v hm; apply (hv v (by simp [hm])).same_caches <;> rw [hadded.1])
    refine ⟨result, actual, ?_, ?_, ?_⟩
    · unfold metadata.decode_element_initializers_loop at hloop ⊢
      rw [loop]
      simpa [metadata.decode_element_initializers_loop.body, hmore, hread, hdeclare, hpush, hj,
        core.result.Result.Insts.CoreOpsTry.branch] using hloop
    · simpa [hvalues, List.append_assoc] using hactual
    · simpa only [List.flatMap_cons] using hadded.trans htail

/-- `metadata.decode_element_initializers` accepts a vector span of valid initializers. -/
theorem metadata.decode_element_initializers.complete
    (data : Slice U8) (env : metadata.Env) (elem : wasm_types.ElemType) (expressions : Bool)
     (pos next : Usize) (values : List wasm_types.ConstExpr)
    (hb : At (VecEncoding (InitializerEncoding expressions)) data pos values next)
    (hrefs : env.declared_funcs.val.length ≤ pos.val)
    (hv : ∀ value ∈ values, ModuleConstants.Valid env value (initializerType elem expressions)) :
    ∃ result actual, metadata.decode_element_initializers data pos env elem expressions =
      .ok (.Ok (actual, next), result) ∧ actual.val = values ∧
      ModuleReferences.Added env result (values.flatMap ModuleReferences.initializer) := by
  obtain ⟨count, middle, hn, hc, hentries⟩ := hb.vector_split
  have hs := hc.span
  obtain ⟨result, actual, hr, hactual, hadded⟩ := metadata.decode_element_initializers_loop.complete
    data env elem expressions count middle (alloc.vec.Vec.new _) 0#u32 values next hentries
    (by simpa using hn.symm) (by simp) (by omega) hv
  refine ⟨result, actual, ?_, by simpa using hactual, hadded⟩
  simp [metadata.decode_element_initializers, reader.read_u32_leb.complete data pos count middle hc,
    core.result.Result.Insts.CoreOpsTry.branch, hr]

end Itasca

end

/-! ## ElementHeaderComplete -/

section

/-!
# Completeness of the element header and entry parser

`metadata.decode_element_header.complete` and `metadata.decode_element.complete`: an independently
encoded element header or entry that is valid in the environment is accepted, and the declared
functions gain its references. Soundness is in `Module/Sections/ElementHeader`.
-/

open Aeneas Aeneas.Std

namespace Itasca
open ModuleBinary ModuleElements

/-- `metadata.decode_element_header` accepts a valid `HeaderEncoding` span. -/
theorem metadata.decode_element_header.complete {data : Slice U8} {pos next : Usize}
    {env : metadata.Env} {mode elem expressions}
    (hb : At (fun value => HeaderEncoding value.1 value.2.1 value.2.2)
      data pos (mode, elem, expressions) next)
    (hv : HeaderValid env mode elem) :
    metadata.decode_element_header data pos env = .ok (.Ok (mode, elem, expressions, next)) := by
  obtain ⟨bytes, he, hs⟩ := hb
  have hx : metadata.decode_element_header data pos env ⦃ r => r = .Ok (mode, elem, expressions, next) ⦄ := by
    cases he with
    | @activeIndices offset fb ob hf ho =>
      obtain ⟨hi, ht, hv⟩ := hv
      obtain ⟨middle, hflags, hoffset⟩ := hs.split
      have hrf := hflags.read_u32 0#u32 hf
      have hro := metadata.decode_const_expr.complete (env := env) ⟨ob, ho, hoffset⟩ hv
      simp [metadata.decode_element_header, hrf, hro, core.result.Result.Insts.CoreOpsTry.branch,
        show (0#u32 % 2#u32 : Result U32) = .ok 0#u32 from rfl]
      step as ⟨cast1, hcast1⟩
      have hg1 : ¬env.table_types.val.length ≤ cast1.val := by scalar_tac
      simp only [hg1, ↓reduceIte]
      step as ⟨cast2, hcast2⟩
      have hg2 : ¬env.table_types.val.length ≤ cast2.val := by scalar_tac
      simp only [hg2, ↓reduceIte]
      have htype : wasm_types.ElemType.value_type wasm_types.ElemType.FuncRef = .ok (ModuleConstants.referenceValueType wasm_types.ElemType.FuncRef) := by rfl
      rw [htype]
      simp only [bind_ok]
      step as ⟨table, htable⟩
      have hte : table.elem = wasm_types.ElemType.FuncRef := by
        have hval : cast2.val = (0#u32).val := by scalar_tac
        simpa only [htable, hval] using ht
      rw [hte]
      simp [ModuleConstants.referenceValueType, wasm_types.ElemType.value_type,
        core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
        wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq]
    | @activeExpressions offset fb ob hf ho =>
      obtain ⟨hi, ht, hv⟩ := hv
      obtain ⟨middle, hflags, hoffset⟩ := hs.split
      have hrf := hflags.read_u32 4#u32 hf
      have hro := metadata.decode_const_expr.complete (env := env) ⟨ob, ho, hoffset⟩ hv
      simp [metadata.decode_element_header, hrf, hro, core.result.Result.Insts.CoreOpsTry.branch,
        show (4#u32 % 2#u32 : Result U32) = .ok 0#u32 from rfl]
      step as ⟨cast1, hcast1⟩
      have hg1 : ¬env.table_types.val.length ≤ cast1.val := by scalar_tac
      simp only [hg1, ↓reduceIte]
      step as ⟨cast2, hcast2⟩
      have hg2 : ¬env.table_types.val.length ≤ cast2.val := by scalar_tac
      simp only [hg2, ↓reduceIte]
      have htype : wasm_types.ElemType.value_type wasm_types.ElemType.FuncRef = .ok (ModuleConstants.referenceValueType wasm_types.ElemType.FuncRef) := by rfl
      rw [htype]
      simp only [bind_ok]
      step as ⟨table, htable⟩
      have hte : table.elem = wasm_types.ElemType.FuncRef := by
        have hval : cast2.val = (0#u32).val := by scalar_tac
        simpa only [htable, hval] using ht
      rw [hte]
      simp [ModuleConstants.referenceValueType, wasm_types.ElemType.value_type,
        core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
        wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq]
    | @passiveIndices fb hf =>
      obtain ⟨middle, hflags, hkind⟩ := hs.split
      have hrf := hflags.read_u32 1#u32 hf
      simp [metadata.decode_element_header, hrf, hkind.read_byte,
        show (1#u32 % 2#u32 : Result U32) = .ok 1#u32 from rfl,
        core.result.Result.Insts.CoreOpsTry.branch]
    | @declarativeIndices fb hf =>
      obtain ⟨middle, hflags, hkind⟩ := hs.split
      have hrf := hflags.read_u32 3#u32 hf
      simp [metadata.decode_element_header, hrf, hkind.read_byte,
        show (3#u32 % 2#u32 : Result U32) = .ok 1#u32 from rfl,
        core.result.Result.Insts.CoreOpsTry.branch]
    | @explicitIndices index offset fb ib ob hf hindexEnc ho =>
      obtain ⟨hi, ht, hv⟩ := hv
      obtain ⟨kindPos, hprefix, hkind⟩ := hs.split
      obtain ⟨offsetPos, hprefix, hoffset⟩ := hprefix.split
      obtain ⟨indexPos, hflags, hindex⟩ := hprefix.split
      have hrf := hflags.read_u32 2#u32 hf
      have hri := hindex.read_u32 index hindexEnc
      have hro := metadata.decode_const_expr.complete (env := env) ⟨ob, ho, hoffset⟩ hv
      simp [metadata.decode_element_header, hrf, hri, hro, hkind.read_byte,
        show (2#u32 % 2#u32 : Result U32) = .ok 0#u32 from rfl,
        core.result.Result.Insts.CoreOpsTry.branch]
      step as ⟨cast1, hcast1⟩
      have hg1 : ¬env.table_types.val.length ≤ cast1.val := by scalar_tac
      simp only [hg1, ↓reduceIte]
      step as ⟨cast2, hcast2⟩
      have hg2 : ¬env.table_types.val.length ≤ cast2.val := by scalar_tac
      simp only [hg2, ↓reduceIte]
      have htype : wasm_types.ElemType.value_type wasm_types.ElemType.FuncRef = .ok (ModuleConstants.referenceValueType wasm_types.ElemType.FuncRef) := by rfl
      rw [htype]
      simp only [bind_ok]
      step as ⟨table, htable⟩
      have hte : table.elem = wasm_types.ElemType.FuncRef := by
        have hval : cast2.val = (index).val := by scalar_tac
        simpa only [htable, hval] using ht
      rw [hte]
      simp [ModuleConstants.referenceValueType, wasm_types.ElemType.value_type,
        core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
        wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq]
    | @passiveExpressions elem fb hf =>
      obtain ⟨middle, hflags, helem⟩ := hs.split
      have hrf := hflags.read_u32 5#u32 hf
      have hre := metadata.decode_elem_type.complete data middle elem next ⟨_, rfl, helem⟩
      simp [metadata.decode_element_header, hrf, hre,
        show (5#u32 % 2#u32 : Result U32) = .ok 1#u32 from rfl,
        core.result.Result.Insts.CoreOpsTry.branch]
    | @declarativeExpressions elem fb hf =>
      obtain ⟨middle, hflags, helem⟩ := hs.split
      have hrf := hflags.read_u32 7#u32 hf
      have hre := metadata.decode_elem_type.complete data middle elem next ⟨_, rfl, helem⟩
      simp [metadata.decode_element_header, hrf, hre,
        show (7#u32 % 2#u32 : Result U32) = .ok 1#u32 from rfl,
        core.result.Result.Insts.CoreOpsTry.branch]
    | @explicitExpressions elem index offset fb ib ob hf hindexEnc ho =>
      obtain ⟨hi, ht, hv⟩ := hv
      obtain ⟨elemPos, hprefix, helem⟩ := hs.split
      obtain ⟨offsetPos, hprefix, hoffset⟩ := hprefix.split
      obtain ⟨indexPos, hflags, hindex⟩ := hprefix.split
      have hrf := hflags.read_u32 6#u32 hf
      have hri := hindex.read_u32 index hindexEnc
      have hro := metadata.decode_const_expr.complete (env := env) ⟨ob, ho, hoffset⟩ hv
      have hre := metadata.decode_elem_type.complete data elemPos elem next ⟨_, rfl, helem⟩
      simp [metadata.decode_element_header, hrf, hri, hro, hre,
        show (6#u32 % 2#u32 : Result U32) = .ok 0#u32 from rfl,
        core.result.Result.Insts.CoreOpsTry.branch]
      step as ⟨cast1, hcast1⟩
      have hg1 : ¬env.table_types.val.length ≤ cast1.val := by scalar_tac
      simp only [hg1, ↓reduceIte]
      step as ⟨cast2, hcast2⟩
      have hg2 : ¬env.table_types.val.length ≤ cast2.val := by scalar_tac
      simp only [hg2, ↓reduceIte]
      have htype : wasm_types.ElemType.value_type elem = .ok (ModuleConstants.referenceValueType elem) := by cases elem <;> rfl
      rw [htype]
      simp only [bind_ok]
      step as ⟨table, htable⟩
      have hte : table.elem = elem := by
        have hval : cast2.val = (index).val := by scalar_tac
        simpa only [htable, hval] using ht
      rw [hte]
      cases elem <;> simp [ModuleConstants.referenceValueType, wasm_types.ElemType.value_type,
        core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
        wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq]
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hx
  exact hr

end Itasca

open Aeneas Aeneas.Std

namespace Itasca
open ModuleBinary ModuleElements ModuleSections

/-- `metadata.decode_element` accepts an `ElementEncodingFor` span of a raw element that is valid in
the environment. -/
theorem metadata.decode_element.complete (data : Slice U8) (env : metadata.Env)
     (pos next : Usize) (entry : ModuleBinary.Element)
    (hb : At (ElementEncodingFor) data pos entry next)
    (hv : ElementValidRaw env entry) (hrefs : env.declared_funcs.val.length ≤ pos.val) :
    ∃ result actual, metadata.decode_element data pos env = .ok (.Ok (actual, next), result) ∧
      ModuleEnv.rawElement actual = entry ∧ ModuleReferences.Added env result (ModuleReferences.element actual) := by
  obtain ⟨bytes, he, hs⟩ := hb
  obtain ⟨expressions, header, encoded, hhead, hvalues, rfl⟩ := header_parts he
  obtain ⟨middle, hheader, hentries⟩ := hs.split
  have hreadheader := metadata.decode_element_header.complete (env := env)
    ⟨header, hhead, hheader⟩ hv.1
  have hspan := hheader.length
  have hty := hhead.initializer_type
  obtain ⟨result, init, hreadinit, hinit, hadded⟩ := metadata.decode_element_initializers.complete
    data env entry.elem expressions middle next entry.init ⟨encoded, hvalues, hentries⟩
    (by omega) (by simpa only [hty] using hv.2)
  let actual : metadata.Element := ⟨entry.elem, entry.mode, init⟩
  refine ⟨result, actual, ?_, ?_, ?_⟩
  · simp [metadata.decode_element, hreadheader, hreadinit, actual,
      core.result.Result.Insts.CoreOpsTry.branch]
  · cases entry
    simp [ModuleEnv.rawElement, actual, hinit]
  · simpa only [ModuleReferences.element, actual, hinit] using hadded

end Itasca

end

/-! ## ElementComplete -/

section

/-!
# Completeness of the element section parser

`metadata.decode_element_section.profile_complete` (and the Wasm 1.0 `.complete`): an independently
encoded vector of elements that are `ElementValidRaw` in the environment is accepted, and the
environment gains them (`ElementsAdded`). `metadata.decode_func_indices.complete` covers the index
vectors. Soundness is in `Module/Sections/Element`.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary ModuleSections

private theorem element_raw_valid_caches {env result entry}
    (h : ElementValidRaw env entry)
    (hf : result.func_types = env.func_types) (hg : result.global_types = env.global_types)
    (hn : result.num_imported_globals = env.num_imported_globals)
    (ht : result.table_types = env.table_types) : ElementValidRaw result entry := by
  obtain ⟨hm, hi⟩ := h
  constructor
  · cases hmode : entry.mode with
    | Passive | Declarative => trivial
    | Active index offset =>
      rw [hmode] at hm
      obtain ⟨hb, he, hv⟩ := hm
      exact ⟨by simpa [ht] using hb, by simpa [ht] using he, hv.same_caches hf hg hn⟩
  · intro value hv
    exact (hi value hv).same_caches hf hg hn

/-- The element loop accepts the remaining valid elements of a repetition span and adds them. -/
theorem metadata.decode_element_section_loop.profile_complete
    (data : Slice U8) (env : metadata.Env) (count : U32) (pos : Usize) (i : U32)
    (entries : List ModuleBinary.Element) (next : Usize)
    (hb : At (Rep (ElementEncodingFor)) data pos entries next)
    (hc : i.val + entries.length = count.val)
    (hv : ∀ entry ∈ entries, ElementValidRaw env entry)
    (hsize : env.elements.val.length ≤ pos.val) (hrefs : env.declared_funcs.val.length ≤ pos.val) :
    ∃ result actual, metadata.decode_element_section_loop data env count pos i = .ok (.Ok next, result) ∧
      actual.map ModuleEnv.rawElement = entries ∧ ElementsAdded env result actual := by
  induction entries generalizing env pos i with
  | nil =>
    have he := hb.rep_nil
    have hstop : i ≥ count := by simp only [List.length_nil, Nat.add_zero] at hc; scalar_tac
    refine ⟨env, [], ?_, rfl, ⟨by cases env; rfl, by simp, by simp⟩⟩
    unfold metadata.decode_element_section_loop
    rw [loop]
    simp [metadata.decode_element_section_loop.body, hstop, he]
  | cons entry entries ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hb.rep_cons
    have hmore : ¬ i ≥ count := by simp only [List.length_cons] at hc; scalar_tac
    obtain ⟨updated, current, hread, hraw, hadded⟩ := metadata.decode_element.complete
      data env pos middle entry hfirst (hv entry (by simp)) hrefs
    have hpost := metadata.decode_element.spec data pos env hrefs
    rw [hread] at hpost
    simp only [WP.spec_ok] at hpost
    obtain ⟨_, _, _, hbound, hprogress⟩ := hpost
    have hunchanged : updated.elements = env.elements := by rw [hadded.1]
    obtain ⟨elements, hpush, helements⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec updated.elements current (by rw [hunchanged]; scalar_tac))
    obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
      (U32.add_spec (x := i) (y := 1#u32) (by simp only [List.length_cons] at hc; scalar_tac))
    let after := { updated with elements := elements }
    obtain ⟨result, actual, hloop, hraws, htail⟩ := ih after middle j hrest
      (by simp only [List.length_cons] at hc; scalar_tac)
      (by
        intro e he
        apply element_raw_valid_caches (hv e (by simp [he])) <;>
          dsimp only [after] <;> rw [hadded.1])
      (by simp only [after, helements, hunchanged, List.length_append, List.length_singleton]; omega)
      hbound
    refine ⟨result, current :: actual, ?_, ?_, ?_⟩
    · unfold metadata.decode_element_section_loop at hloop ⊢
      rw [loop]
      simpa [metadata.decode_element_section_loop.body, hmore, hread, hpush, hj, after,
        core.result.Result.Insts.CoreOpsTry.branch] using hloop
    · simp only [List.map_cons, hraw, hraws]
    · refine ⟨?_, ?_, ?_⟩
      · rw [htail.1]
        dsimp only [after]
        rw [hadded.1]
      · simpa only [after, helements, hunchanged, List.append_assoc, List.cons_append,
          List.nil_append] using htail.2.1
      · simpa only [after, hadded.2, List.flatMap_cons, List.append_assoc] using htail.2.2

/-- `metadata.decode_element_section` accepts a vector span of valid elements and adds them. -/
theorem metadata.decode_element_section.profile_complete (data : Slice U8) (pos : Usize)
    (env : metadata.Env) (entries : List ModuleBinary.Element) (next : Usize)
    (hb : At (VecEncoding (ElementEncodingFor)) data pos entries next)
    (hv : ∀ entry ∈ entries, ElementValidRaw env entry)
    (hsize : env.elements.val.length ≤ pos.val) (hrefs : env.declared_funcs.val.length ≤ pos.val) :
    ∃ result actual, metadata.decode_element_section data pos env = .ok (.Ok next, result) ∧
      actual.map ModuleEnv.rawElement = entries ∧ ElementsAdded env result actual := by
  obtain ⟨count, middle, hc, hcount, hentries⟩ := hb.vector_split
  obtain ⟨result, actual, hr, hp⟩ := metadata.decode_element_section_loop.profile_complete
    data env count middle 0#u32 entries next hentries (by simpa using hc.symm) hv
    (by have := hcount.span; omega) (by have := hcount.span; omega)
  refine ⟨result, actual, ?_, hp⟩
  simp [metadata.decode_element_section, reader.read_u32_leb.complete data pos count middle hcount,
    core.result.Result.Insts.CoreOpsTry.branch, hr]

end Itasca

end

/-! ## ExportComplete -/

section

/-!
# Completeness of the export and start section parsers

`metadata.decode_export_section.complete`: an independently encoded vector of exports with distinct
names and valid descriptors is accepted, and the environment gains those exports
(`ExportsAdded`). `metadata.decode_start_section.complete` accepts a start function without
parameters or results. Soundness is in `Module/Sections/Export`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleSections

/-- Export additions compose. -/
theorem ExportsAdded.append {env middle result first rest}
    (hfirst : ExportsAdded env first middle) (hrest : ExportsAdded middle rest result) :
    ExportsAdded env (first ++ rest) result := by
  induction hrest with
  | nil => simpa using hfirst
  | snoc _ ha ih => simpa only [List.append_assoc] using ExportsAdded.snoc ih ha

end Itasca.ModuleSections

namespace Itasca.ModuleBinary
open ModuleSections

/-- An export descriptor encoding splits into its kind byte and index. -/
theorem At.export_desc_split {data pos desc next}
    (h : At ExportDescEncoding data pos desc next) :
    ∃ middle, At ByteEncoding data pos (descByte desc) middle ∧
      At IndexEncoding data middle (descIndex desc) next := by
  obtain ⟨bytes, he, hs⟩ := h
  cases he <;> rename_i idx indexBytes hi
  all_goals
    obtain ⟨middle, htag, hindex⟩ :=
      (show Wasm1.BytesAt data pos ([_] ++ indexBytes) next from hs).split
    exact ⟨middle, ⟨_, rfl, htag⟩, ⟨indexBytes, hi, hindex⟩⟩

/-- An export encoding splits into its name, kind byte and index. -/
theorem At.export_split {data pos entry next}
    (h : At ExportEncoding data pos entry next) :
    ∃ first middle, At NameEncoding data pos entry.name first ∧
      At ByteEncoding data first (descByte entry.desc) middle ∧
      At IndexEncoding data middle (descIndex entry.desc) next := by
  obtain ⟨bytes, ⟨nameBytes, descBytes, hn, hd, rfl⟩, hs⟩ := h
  obtain ⟨first, hname, hdesc⟩ := hs.split
  obtain ⟨middle, htag, hindex⟩ :=
    (show At ExportDescEncoding data first entry.desc next from ⟨descBytes, hd, hdesc⟩).export_desc_split
  exact ⟨first, middle, ⟨nameBytes, hn, hname⟩, htag, hindex⟩

end Itasca.ModuleBinary

namespace Itasca
open ModuleBinary ModuleSections

/-- `metadata.export_name_taken` returns false for an unused name. -/
theorem metadata.export_name_taken.fresh (env : metadata.Env) (nm : Slice U8)
    (h : nm.val ∉ env.exports.val.map (fun e => e.name.val)) :
    metadata.export_name_taken env nm = .ok false := by
  obtain ⟨taken, hr, ht⟩ := WP.spec_imp_exists (metadata.export_name_taken.spec env nm)
  cases taken with
  | false => exact hr
  | true => exact False.elim (h (ht.mp rfl))

/-- `metadata.export_name_taken` returns true for an exported name. -/
theorem metadata.export_name_taken.duplicate (env : metadata.Env) (nm : Slice U8)
    (h : nm.val ∈ env.exports.val.map (fun e => e.name.val)) :
    metadata.export_name_taken env nm = .ok true := by
  obtain ⟨taken, hr, ht⟩ := WP.spec_imp_exists (metadata.export_name_taken.spec env nm)
  simpa [ht.mpr h] using hr

/-- `metadata.export_desc` accepts the kind byte and index of a valid descriptor. -/
theorem metadata.export_desc.complete (env : metadata.Env) (desc : metadata.ExportDesc)
    (h : ExportDescValid env desc) :
    metadata.export_desc env (descByte desc) (descIndex desc) = .ok (.Ok desc) := by
  have hs : metadata.export_desc env (descByte desc) (descIndex desc) ⦃ r => r = .Ok desc ⦄ := by
    cases desc <;> simp only [descByte, descIndex, ExportDescValid] at *
    all_goals unfold metadata.export_desc
    all_goals step
    all_goals simp
    all_goals step*
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hs
  exact hr

/-- `metadata.decode_start_section` accepts a `StartEncoding` span naming a function without
parameters or results. -/
theorem metadata.decode_start_section.complete (data : Slice U8) (pos : Usize)
    (env : metadata.Env) (idx : U32) (next : Usize)
    (h : At StartEncoding data pos (some idx) next)
    (hi : idx.val < env.func_types.val.length)
    (hparams : env.func_types.val[idx.val].params.val = [])
    (hresults : env.func_types.val[idx.val].results.val = []) :
    metadata.decode_start_section data pos env = .ok (.Ok next, { env with start := some idx }) := by
  obtain ⟨bytes, ⟨index, hindex, he⟩, hs⟩ := h
  have hei : index = idx := Option.some.inj hindex.symm
  subst index
  have hr := hs.read_u32 idx he
  have hp : metadata.decode_start_section data pos env ⦃ r =>
      r = (.Ok next, { env with start := some idx }) ⦄ := by
    simp [metadata.decode_start_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    step*
    simp_all [alloc.vec.Vec.is_empty]
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hp
  exact hr


/-- The export loop accepts the remaining exports of a repetition span, given distinct names across
the environment's exports and the remaining ones, and valid descriptors. -/
theorem metadata.decode_export_section_loop.complete
    (data : Slice U8) (env : metadata.Env) (count : U32) (pos : Usize) (i : U32)
    (raw : List ModuleBinary.Export) (next : Usize)
    (hb : At (Rep ExportEncoding) data pos raw next)
    (hc : i.val + raw.length = count.val)
    (hnames : (env.exports.val.map (fun e => e.name.val) ++ raw.map (fun e => e.name)).Nodup)
    (hvalid : ∀ entry ∈ raw, ExportDescValid env entry.desc)
    (hsize : env.exports.val.length ≤ pos.val)
    (hrefs : env.declared_funcs.val.length ≤ pos.val) :
    ∃ result entries, metadata.decode_export_section_loop data env count pos i = .ok (.Ok next, result) ∧
      ExportsAdded env entries result ∧ entries.map ModuleEnv.rawExport = raw := by
  induction raw generalizing env pos i with
  | nil =>
      have he := hb.rep_nil
      have hstop : i ≥ count := by simp only [List.length_nil, Nat.add_zero] at hc; scalar_tac
      refine ⟨env, [], ?_, .nil, rfl⟩
      unfold metadata.decode_export_section_loop
      rw [loop]
      simp [metadata.decode_export_section_loop.body, hstop, he]
  | cons entry raw ih =>
      obtain ⟨endEntry, hentry, hrest⟩ := hb.rep_cons
      obtain ⟨first, middle, hnameBytes, htag, hindex⟩ := hentry.export_split
      obtain ⟨nm, hname, hnm⟩ := metadata.decode_name.complete_raw data pos entry.name first hnameBytes
      have hfresh : entry.name ∉ env.exports.val.map (fun e => e.name.val) := by
        have hh := List.nodup_cons.mp (List.nodup_middle.mp
          (show (env.exports.val.map (fun e => e.name.val) ++ entry.name :: raw.map (fun e => e.name)).Nodup from
            by simpa using hnames))
        intro hm
        exact hh.1 (List.mem_append_left _ hm)
      have htaken := metadata.export_name_taken.fresh env (alloc.vec.Vec.deref nm)
        (by simpa [alloc.vec.Vec.deref, hnm] using hfresh)
      have hdesc := metadata.export_desc.complete env entry.desc (hvalid entry (by simp))
      have hmore : ¬i ≥ count := by simp only [List.length_cons] at hc; scalar_tac
      have hprogress : pos.val < endEntry.val := by
        have := hnameBytes.span
        have := htag.span
        have := hindex.index_decoded.span
        omega
      have hbound := hentry.span.2
      let actual : metadata.Export := ⟨nm, entry.desc⟩
      have hraw : ModuleEnv.rawExport actual = entry := by cases entry; simp_all [ModuleEnv.rawExport, actual]
      have hdeclares : (match entry.desc with
          | .Func index => do
              let v ← alloc.vec.Vec.push env.declared_funcs index
              Result.ok {env with declared_funcs := v}
          | .Table _ => Result.ok env
          | .Memory _ => Result.ok env
          | .Global _ => Result.ok env) ⦃ result =>
          ModuleReferences.Added env result (ModuleReferences.exportIndices actual) ⦄ := by
        cases hdescCase : entry.desc <;> simp only
        · step
          exact ⟨rfl, by simpa [ModuleReferences.exportIndices, actual, hdescCase] using v_post⟩
        all_goals exact ⟨by cases env; rfl, by simp [ModuleReferences.exportIndices, actual, hdescCase]⟩
      obtain ⟨declared, hdeclare, hdeclared⟩ := WP.spec_imp_exists hdeclares
      have hnewRefs : declared.declared_funcs.val.length ≤ endEntry.val := by
        rw [hdeclared.2, List.length_append]
        have : (ModuleReferences.exportIndices actual).length ≤ 1 := by
          cases h : entry.desc <;> simp [ModuleReferences.exportIndices, actual, h]
        omega
      obtain ⟨exports, hpush, hexports⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec env.exports actual (by scalar_tac))
      obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
        (U32.add_spec (x := i) (y := 1#u32) (by scalar_tac))
      let updated := {env with exports := exports, declared_funcs := declared.declared_funcs}
      have hadded : ExportAdded env updated actual :=
        ⟨rfl, hexports, by simpa only [actual, hnm] using hfresh,
          (hvalid entry (by simp)).resolves nm, hdeclared.2⟩
      obtain ⟨result, entries, hloop, hhistory, hentries⟩ := ih updated endEntry j hrest
        (by simp only [List.length_cons] at hc; scalar_tac)
        (by simpa [updated, hexports, actual, hnm, List.append_assoc] using hnames)
        (by intro e he; exact hvalid e (by simp [he]))
        (by simp only [updated, hexports, List.length_append, List.length_singleton]; omega)
        hnewRefs
      refine ⟨result, actual :: entries, ?_, ?_, by simp [hraw, hentries]⟩
      · unfold metadata.decode_export_section_loop
        rw [loop]
        simp [metadata.decode_export_section_loop.body, hmore,
          hname, htaken, htag.read_byte, hindex.read_index, hdesc,
          core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        cases hdescCase : entry.desc <;> simp only [hdescCase] at hdeclare ⊢
        all_goals
          rw [hdeclare]
          simp only [bind_ok]
          rw [hdeclared.1]
          have hpush' := hpush
          simp only [actual, hdescCase] at hpush'
          simpa [hpush', hj, metadata.decode_export_section_loop,
            metadata.decode_export_section_loop.body, actual, updated, hdescCase,
            core.result.Result.Insts.CoreOpsTry.branch] using hloop
      · simpa using (ExportsAdded.snoc ExportsAdded.nil hadded).append hhistory

/-- `metadata.decode_export_section` accepts a vector span of exports with distinct names and valid
descriptors, starting from an environment without exports. -/
theorem metadata.decode_export_section.complete (data : Slice U8) (pos : Usize)
    (env : metadata.Env) (raw : List ModuleBinary.Export) (next : Usize)
    (hb : At (VecEncoding ExportEncoding) data pos raw next)
    (hempty : env.exports.val = []) (hnames : (raw.map (fun e => e.name)).Nodup)
    (hvalid : ∀ entry ∈ raw, ExportDescValid env entry.desc)
    (hrefs : env.declared_funcs.val.length ≤ pos.val) :
    ∃ result entries, metadata.decode_export_section data pos env = .ok (.Ok next, result) ∧
      ExportsAdded env entries result ∧ entries.map ModuleEnv.rawExport = raw := by
  obtain ⟨count, middle, hc, hcount, hentries⟩ := hb.vector_split
  obtain ⟨result, entries, hr, hp, he⟩ := metadata.decode_export_section_loop.complete
    data env count middle 0#u32 raw next hentries (by simpa using hc.symm)
    (by simpa [hempty] using hnames) hvalid (by simp [hempty])
    (by have := hcount.span; omega)
  refine ⟨result, entries, ?_, hp, he⟩
  simp [metadata.decode_export_section, reader.read_u32_leb.complete data pos count middle hcount,
    core.result.Result.Insts.CoreOpsTry.branch, hr]

end Itasca

end

/-! ## FunctionComplete -/

section

/-!
# Completeness of the function section parser

`metadata.decode_function_section.complete`: an independently encoded vector of in-range type
indices is accepted and the environment gains those indices and their signatures
(`FunctionsAdded`). `metadata.lookup_type.complete` is the lookup step. Soundness is in
`Module/Sections/Function`.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary ModuleSections

/-- `metadata.lookup_type` returns the signature at an in-range index. -/
theorem metadata.lookup_type.complete (env : metadata.Env) (idx : U32)
    (hi : idx.val < env.types.val.length) :
    metadata.lookup_type env idx = .ok (.Ok env.types.val[idx.val]) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (metadata.lookup_type.spec env idx)
  cases r with
  | Err e => have := hp.2; omega
  | Ok ft => obtain ⟨_, rfl⟩ := hp; exact hr

/-- The function loop accepts the remaining in-range indices of a repetition span and appends each
index with its signature, in order. -/
theorem metadata.decode_function_section_loop.complete
    (data : Slice U8) (env : metadata.Env) (count : U32) (pos : Usize) (i : U32)
    (indices : List U32) (next : Usize)
    (hb : At (Rep IndexEncoding) data pos indices next)
    (hc : i.val + indices.length = count.val)
    (ht : ∀ idx ∈ indices, idx.val < env.types.val.length)
    (hf : env.func_types.val.length ≤ pos.val)
    (hi : env.func_type_indices.val.length ≤ pos.val) :
    ∃ result signatures,
      metadata.decode_function_section_loop data env count pos i = .ok (.Ok next, result) ∧
      FunctionsAdded env result indices signatures := by
  induction indices generalizing env pos i with
  | nil =>
    have he := hb.rep_nil
    have hstop : i ≥ count := by simp only [List.length_nil, Nat.add_zero] at hc; scalar_tac
    refine ⟨env, [], ?_, ?_⟩
    · unfold metadata.decode_function_section_loop
      rw [loop]
      simp [metadata.decode_function_section_loop.body, hstop, he]
    · exact ⟨by cases env; rfl, by simp, by simp, .nil⟩
  | cons idx indices ih =>
    obtain ⟨middle, hidx, hrest⟩ := hb.rep_cons
    have hspan := hidx.index_decoded.span
    have hmore : ¬ i ≥ count := by simp only [List.length_cons] at hc; scalar_tac
    have hidxvalid := ht idx (by simp)
    have hread := hidx.read_index
    have hlookup := metadata.lookup_type.complete env idx hidxvalid
    obtain ⟨funcs, hpush, hfuncs⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.func_types env.types.val[idx.val] (by scalar_tac))
    obtain ⟨ids, hpushids, hids⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.func_type_indices idx (by scalar_tac))
    obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
      (U32.add_spec (x := i) (y := 1#u32) (by scalar_tac))
    let updated := {env with func_types := funcs, func_type_indices := ids}
    obtain ⟨result, signatures, hloop, hadded⟩ := ih updated middle j hrest
      (by simp only [List.length_cons] at hc; scalar_tac)
      (by intro idx hx; exact ht idx (by simp [hx]))
      (by simp only [updated, hfuncs, List.length_append, List.length_singleton]; omega)
      (by simp only [updated, hids, List.length_append, List.length_singleton]; omega)
    refine ⟨result, env.types.val[idx.val] :: signatures, ?_, ?_⟩
    · unfold metadata.decode_function_section_loop
      rw [loop]
      simp [metadata.decode_function_section_loop.body, hmore, hread, hlookup,
        hpush, hpushids, hj, core.result.Result.Insts.CoreOpsTry.branch]
      exact hloop
    · refine ⟨?_, ?_, ?_, .cons ⟨hidxvalid, rfl⟩ hadded.2.2.2⟩
      · rw [hadded.1]
      · simpa [updated, hids, List.append_assoc] using hadded.2.1
      · simpa [updated, hfuncs, List.append_assoc] using hadded.2.2.1

/-- `metadata.decode_function_section` accepts a vector span of in-range type indices. -/
theorem metadata.decode_function_section.complete (data : Slice U8) (pos : Usize)
    (env : metadata.Env) (indices : List U32) (next : Usize)
    (hb : At (VecEncoding IndexEncoding) data pos indices next)
    (ht : ∀ idx ∈ indices, idx.val < env.types.val.length)
    (hf : env.func_types.val.length ≤ pos.val)
    (hi : env.func_type_indices.val.length ≤ pos.val) :
    ∃ result signatures,
      metadata.decode_function_section data pos env = .ok (.Ok next, result) ∧
      FunctionsAdded env result indices signatures := by
  obtain ⟨count, middle, hc, hcount, hentries⟩ := hb.vector_split
  obtain ⟨result, signatures, hr, hp⟩ := metadata.decode_function_section_loop.complete
    data env count middle 0#u32 indices next hentries (by simpa using hc.symm) ht
    (by have := hcount.span; omega) (by have := hcount.span; omega)
  refine ⟨result, signatures, ?_, hp⟩
  simp [metadata.decode_function_section, reader.read_u32_leb.complete data pos count middle hcount,
    core.result.Result.Insts.CoreOpsTry.branch, hr]

end Itasca

end

/-! ## GlobalComplete -/

section

/-!
# Completeness of the global section parser

`metadata.decode_global_section.complete`: an independently encoded vector of globals with valid
initializers is accepted, and the environment gains those globals
(`GlobalsAdded`). Soundness is in `Module/Sections/Global`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- A global encoding splits into its type and initializer spans. -/
theorem At.global_split {data pos entry next} (h : At GlobalEncoding data pos entry next) :
    ∃ middle, At GlobalTypeEncoding data pos entry.gtype middle ∧
      At ConstEncoding data middle entry.init next := by
  obtain ⟨bytes, ⟨gb, ib, hg, hi, rfl⟩, hs⟩ := h
  obtain ⟨middle, hfirst, hrest⟩ := hs.split
  exact ⟨middle, ⟨_, hg, hfirst⟩, ⟨_, hi, hrest⟩⟩

/-- A global type encoding consumes at least one byte. -/
theorem At.globalType_progress {data pos ty next} (h : At GlobalTypeEncoding data pos ty next) :
    pos.val < next.val := by
  obtain ⟨bytes, rfl, hs⟩ := h
  have := hs.length
  simp only [List.length_cons, List.length_nil] at this
  omega

end Itasca.ModuleBinary

namespace Itasca

open ModuleBinary ModuleSections

/-- The global loop accepts the remaining valid globals of a repetition span and adds them. -/
theorem metadata.decode_global_section_loop.complete
    (data : Slice U8) (env : metadata.Env) (count : U32) (pos : Usize) (i : U32)
    (added : List metadata.Global) (next : Usize)
    (hb : At (Rep GlobalEncoding) data pos added next)
    (hc : i.val + added.length = count.val)
    (hv : ∀ g ∈ added, ModuleConstants.Valid env g.init g.gtype.valtype)
    (hg : env.globals.val.length ≤ pos.val)
    (ht : env.global_types.val.length ≤ pos.val)
    (href : env.declared_funcs.val.length ≤ pos.val) :
    ∃ result, metadata.decode_global_section_loop data env count pos i = .ok (.Ok next, result) ∧
      GlobalsAdded env result added := by
  induction added generalizing env pos i with
  | nil =>
    have he := hb.rep_nil
    have hstop : i ≥ count := by simp only [List.length_nil, Nat.add_zero] at hc; scalar_tac
    refine ⟨env, ?_, by exact ⟨by cases env; rfl, by simp, by simp, by simp⟩⟩
    unfold metadata.decode_global_section_loop
    rw [loop]
    simp [metadata.decode_global_section_loop.body, hstop, he]
  | cons g added ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hb.rep_cons
    obtain ⟨initStart, htype, hexpr⟩ := hfirst.global_split
    have hprogress := htype.globalType_progress
    have hspan := hexpr.span
    have hmore : ¬ i ≥ count := by simp only [List.length_cons] at hc; scalar_tac
    have hreadtype := metadata.decode_global_type.complete data pos g.gtype initStart htype
    have hreadexpr := metadata.decode_const_expr.complete hexpr (hv g (by simp))
    obtain ⟨declared, hdeclare, hdeclared⟩ := WP.spec_imp_exists
      (metadata.declare_initializer.spec env g.init (by scalar_tac))
    have hrefsLength : declared.declared_funcs.val.length ≤ middle.val := by
      rw [hdeclared.2, List.length_append]
      have : (ModuleReferences.initializer g.init).length ≤ 1 := by
        cases g.init <;> simp [ModuleReferences.initializer]
      omega
    obtain ⟨types, hpush, htypes⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.global_types g.gtype (by scalar_tac))
    obtain ⟨globals, hpushglobals, hglobals⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.globals g (by scalar_tac))
    obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
      (U32.add_spec (x := i) (y := 1#u32) (by scalar_tac))
    let updated := {env with globals := globals, global_types := types, declared_funcs := declared.declared_funcs}
    obtain ⟨result, hloop, hadded⟩ := ih updated middle j hrest
      (by simp only [List.length_cons] at hc; scalar_tac)
      (by intro g' hx; exact (hv g' (by simp [hx])).append_globals [g.gtype] htypes rfl rfl)
      (by simp only [updated, hglobals, List.length_append, List.length_singleton]; omega)
      (by simp only [updated, htypes, List.length_append, List.length_singleton]; omega)
      hrefsLength
    refine ⟨result, ?_, ?_⟩
    · unfold metadata.decode_global_section_loop
      rw [loop]
      simp [metadata.decode_global_section_loop.body, hmore,
        hreadtype, hreadexpr, core.result.Result.Insts.CoreOpsTry.branch, hdeclare]
      rw [hdeclared.1]
      simpa [hpush, hpushglobals, hj, metadata.decode_global_section_loop,
        metadata.decode_global_section_loop.body, updated, core.result.Result.Insts.CoreOpsTry.branch] using hloop
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hadded.1]
      · simpa [updated, hglobals, List.append_assoc] using hadded.2.1
      · simpa [updated, htypes, List.append_assoc] using hadded.2.2.1
      · simpa [updated, hdeclared.2, ModuleReferences.global, List.append_assoc] using hadded.2.2.2

/-- `metadata.decode_global_section` accepts a vector span of valid globals and adds them. -/
theorem metadata.decode_global_section.complete (data : Slice U8) (pos : Usize)
    (env : metadata.Env) (added : List metadata.Global) (next : Usize)
    (hb : At (VecEncoding GlobalEncoding) data pos added next)
    (hv : ∀ g ∈ added, ModuleConstants.Valid env g.init g.gtype.valtype)
    (hg : env.globals.val.length ≤ pos.val)
    (ht : env.global_types.val.length ≤ pos.val)
    (href : env.declared_funcs.val.length ≤ pos.val) :
    ∃ result, metadata.decode_global_section data pos env = .ok (.Ok next, result) ∧
      GlobalsAdded env result added := by
  obtain ⟨count, middle, hc, hcount, hentries⟩ := hb.vector_split
  obtain ⟨result, hr, hp⟩ := metadata.decode_global_section_loop.complete
    data env count middle 0#u32 added next hentries (by simpa using hc.symm) hv
    (by have := hcount.span; omega) (by have := hcount.span; omega)
    (by have := hcount.span; omega)
  refine ⟨result, ?_, hp⟩
  simp [metadata.decode_global_section, reader.read_u32_leb.complete data pos count middle hcount,
    core.result.Result.Insts.CoreOpsTry.branch, hr]

end Itasca

end
