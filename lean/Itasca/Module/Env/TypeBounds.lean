import Itasca.Module.Sections.Type

/-!
# Function type parameter bounds

A function type's parameter vector is bounded by the number of bytes that encode it. The
`funcTypeVector_params_bound` lemmas give this for decoded type vectors, and `SignatureBounded`
packages the bound for the types of an environment so that parameter counts stay within the
byte cursor.
-/

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

/-- Every function type in a decoded type vector has at most as many parameters as the end
position of the vector. -/
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

/-- Every function type in the environment has at most `limit` parameters. Parameter vectors are
nested inside the type list, so they need their own size bound unlike the index-space caches. -/
def SignatureBounded (env : module.Env) (limit : Nat) : Prop :=
  ∀ ft ∈ env.types.val, ft.params.val.length ≤ limit

theorem SignatureBounded.mono {env limit next} (h : SignatureBounded env limit) (hle : limit ≤ next) :
    SignatureBounded env next := by
  intro ft hf
  have := h ft hf
  omega

/-- Appending the types decoded by a type section keeps the signature bound at the cursor after
the section. -/
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
