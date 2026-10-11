import Itasca.Module.ModuleElementReaders
import Itasca.Module.ModuleConstantsComplete

open Aeneas Aeneas.Std

namespace Itasca
open ModuleBinary ModuleElements

theorem module.decode_element_initializer.complete {data : Slice U8} {pos next : Usize}
    {env : module.Env} {elem : types.ElemType} {expressions : Bool} {profile : ValidationProfile}
    {value : types.ConstExpr}
    (hb : At (InitializerEncoding expressions) data pos value next)
    (hv : ModuleConstants.Valid env value (initializerType elem expressions))
    (ha : expressions = true → ConstAllowed profile value) :
    module.decode_element_initializer data pos env elem expressions profile = .ok (.Ok (value, next)) := by
  cases expressions with
  | true =>
    have hty : types.ElemType.value_type elem = .ok (ModuleConstants.referenceValueType elem) := by
      cases elem <;> rfl
    simp only [module.decode_element_initializer, ↓reduceIte, hty, bind_ok]
    exact module.decode_const_expr.complete hb hv profile (ha rfl)
  | false =>
    obtain ⟨bytes, ⟨index, rfl, hi⟩, hs⟩ := hb
    have hread := hs.read_u32 index hi
    have hvalid : index.val < env.func_types.val.length := by cases hv; assumption
    have hx : module.decode_element_initializer data pos env elem false profile ⦃ r => r = .Ok (.RefFunc index, next) ⦄ := by
      simp [module.decode_element_initializer, hread, core.result.Result.Insts.CoreOpsTry.branch]
      step
      have hguard : ¬env.func_types.val.length ≤ i.val := by scalar_tac
      simp [hguard]
    obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hx
    exact hr

theorem module.decode_element_initializers_loop.complete
    (data : Slice U8) (env : module.Env) (elem : types.ElemType) (expressions : Bool)
    (profile : ValidationProfile) (count : U32) (pos : Usize) (out : alloc.vec.Vec types.ConstExpr) (i : U32)
    (values : List types.ConstExpr) (next : Usize)
    (hb : At (Rep (InitializerEncoding expressions)) data pos values next)
    (hc : i.val + values.length = count.val) (hlen : out.val.length ≤ i.val)
    (hrefs : env.declared_funcs.val.length ≤ pos.val)
    (hv : ∀ value ∈ values, ModuleConstants.Valid env value (initializerType elem expressions))
    (ha : ∀ value ∈ values, expressions = true → ConstAllowed profile value) :
    ∃ result actual, module.decode_element_initializers_loop data env elem expressions profile count pos out i =
      .ok (.Ok (actual, next), result) ∧ actual.val = out.val ++ values ∧
      ModuleReferences.Added env result (values.flatMap ModuleReferences.initializer) := by
  induction values generalizing env pos out i with
  | nil =>
    have he := hb.rep_nil
    have hstop : i ≥ count := by simp only [List.length_nil, Nat.add_zero] at hc; scalar_tac
    refine ⟨env, out, ?_, by simp, ⟨rfl, by simp⟩⟩
    unfold module.decode_element_initializers_loop
    rw [loop]
    simp [module.decode_element_initializers_loop.body, hstop, he]
  | cons value values ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hb.rep_cons
    have hmore : ¬i ≥ count := by simp only [List.length_cons] at hc; scalar_tac
    have hread := module.decode_element_initializer.complete hfirst (hv value (by simp)) (ha value (by simp))
    have hprogress : pos.val < middle.val := by
      obtain ⟨bytes, he, hs⟩ := hfirst
      have := he.nonempty
      have := hs.length
      omega
    obtain ⟨updated, hdeclare, hadded⟩ := WP.spec_imp_exists
      (module.declare_initializer.spec env value (by scalar_tac))
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
      (by intro v hm; exact ha v (by simp [hm]))
    refine ⟨result, actual, ?_, ?_, ?_⟩
    · unfold module.decode_element_initializers_loop at hloop ⊢
      rw [loop]
      simpa [module.decode_element_initializers_loop.body, hmore, hread, hdeclare, hpush, hj,
        core.result.Result.Insts.CoreOpsTry.branch] using hloop
    · simpa [hvalues, List.append_assoc] using hactual
    · simpa only [List.flatMap_cons] using hadded.trans htail

theorem module.decode_element_initializers.complete
    (data : Slice U8) (env : module.Env) (elem : types.ElemType) (expressions : Bool)
    (profile : ValidationProfile) (pos next : Usize) (values : List types.ConstExpr)
    (hb : At (VecEncoding (InitializerEncoding expressions)) data pos values next)
    (hrefs : env.declared_funcs.val.length ≤ pos.val)
    (hv : ∀ value ∈ values, ModuleConstants.Valid env value (initializerType elem expressions))
    (ha : ∀ value ∈ values, expressions = true → ConstAllowed profile value) :
    ∃ result actual, module.decode_element_initializers data pos env elem expressions profile =
      .ok (.Ok (actual, next), result) ∧ actual.val = values ∧
      ModuleReferences.Added env result (values.flatMap ModuleReferences.initializer) := by
  obtain ⟨count, middle, hn, hc, hentries⟩ := hb.vector_split
  have hs := hc.span
  obtain ⟨result, actual, hr, hactual, hadded⟩ := module.decode_element_initializers_loop.complete
    data env elem expressions profile count middle (alloc.vec.Vec.new _) 0#u32 values next hentries
    (by simpa using hn.symm) (by simp) (by omega) hv ha
  refine ⟨result, actual, ?_, by simpa using hactual, hadded⟩
  simp [module.decode_element_initializers, reader.read_u32_leb.complete data pos count middle hc,
    core.result.Result.Insts.CoreOpsTry.branch, hr]

end Itasca
