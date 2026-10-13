import Itasca.Module.Sections.Type

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

theorem Rep.valueTypes_length {values bytes} (h : Rep ValueTypeEncoding values bytes) :
    bytes.length = values.length := by
  induction h with
  | nil => rfl
  | cons he _ ih => simp_all [ValueTypeEncoding]

theorem FuncTypeEncoding.params_bound {ty bytes} (h : FuncTypeEncoding ty bytes) :
    ty.params.val.length ≤ bytes.length := by
  obtain ⟨params, results, ⟨count, entries, _, hp, rfl⟩, _, rfl⟩ := h
  have he := hp.valueTypes_length
  simp only [List.length_cons, List.length_append]
  omega

theorem At.funcType_params_bound {data start ty next}
    (h : At FuncTypeEncoding data start ty next) : ty.params.val.length ≤ next.val := by
  obtain ⟨bytes, he, hs⟩ := h
  have := he.params_bound
  have := hs.length
  omega

theorem Rep.funcTypes_params_bound {types bytes} (h : Rep FuncTypeEncoding types bytes) :
    ∀ ty ∈ types, ty.params.val.length ≤ bytes.length := by
  induction h with
  | nil => simp
  | cons he _ ih =>
    intro ty hm
    rcases List.mem_cons.mp hm with rfl | hm
    · have := he.params_bound
      simp only [List.length_append]
      omega
    · have := ih ty hm
      simp only [List.length_append]
      omega

theorem At.funcTypes_params_bound {data start types next}
    (h : At (Rep FuncTypeEncoding) data start types next) :
    ∀ ty ∈ types, ty.params.val.length ≤ next.val := by
  obtain ⟨bytes, he, hs⟩ := h
  intro ty hm
  have := he.funcTypes_params_bound ty hm
  have := hs.length
  omega

theorem At.funcTypeVector_params_bound {data start types next}
    (h : At (VecEncoding FuncTypeEncoding) data start types next) :
    ∀ ty ∈ types, ty.params.val.length ≤ next.val := by
  obtain ⟨bytes, ⟨count, entries, _, he, rfl⟩, hs⟩ := h
  intro ty hm
  have := he.funcTypes_params_bound ty hm
  have := hs.length
  simp only [List.length_append] at this
  omega

end Itasca.ModuleBinary

namespace Itasca.ModuleEnv

/-- Inner signature vectors, unlike index-space caches, need their own size bound. -/
def SignatureBounded (env : module.Env) (limit : Nat) : Prop :=
  ∀ ft ∈ env.types.val, ft.params.val.length ≤ limit

theorem SignatureBounded.mono {env limit next} (h : SignatureBounded env limit) (hle : limit ≤ next) :
    SignatureBounded env next := by
  intro ft hf
  have := h ft hf
  omega

theorem SignatureBounded.of_types_added {env result added data start next}
    (h : SignatureBounded env start.val)
    (hadd : ModuleSections.TypesAdded env result added)
    (hbytes : ModuleBinary.At (ModuleBinary.VecEncoding ModuleBinary.FuncTypeEncoding)
      data start added next) : SignatureBounded result next.val := by
  intro ft hf
  rw [hadd.2] at hf
  rcases List.mem_append.mp hf with hf | hf
  · exact h.mono hbytes.span.1 ft hf
  · exact hbytes.funcTypeVector_params_bound ft hf

end Itasca.ModuleEnv
