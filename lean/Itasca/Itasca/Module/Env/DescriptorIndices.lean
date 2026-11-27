import Itasca.Module.Sections.EnvironmentAndTail

open Aeneas Aeneas.Std

namespace Itasca.Module.Environment

/-- Every retained function descriptor resolves in the type section. This
invariant justifies indexing the type vector when the start section is read. -/
def DescriptorIndices (env : metadata.CodeMetadata) : Prop :=
  ∀ d ∈ env.funcs.val, d.type_index.val < env.types.val.length

theorem DescriptorIndices.of_fields {a b : metadata.CodeMetadata}
    (valid : DescriptorIndices a) (types : a.types = b.types)
    (funcs : b.funcs.val.map metadata.FuncDesc.type_index = a.funcs.val.map metadata.FuncDesc.type_index) :
    DescriptorIndices b := by
  intro d hd
  have hm : d.type_index ∈ a.funcs.val.map metadata.FuncDesc.type_index :=
    funcs ▸ List.mem_map_of_mem hd
  obtain ⟨old, hm, he⟩ := List.mem_map.mp hm
  simpa [← types, ← he] using valid old hm

theorem DescriptorIndices.refs {a b} {xs} (valid : DescriptorIndices a)
    (h : Module.References.Added a b xs) : DescriptorIndices b := by
  apply valid.of_fields (by rw [h.fields])
  rw [h.funcs]
  apply List.ext_getElem <;> simp

theorem DescriptorIndices.marked {a b} {desc} (valid : DescriptorIndices a)
    (h : Module.Sections.Marked a b desc) : DescriptorIndices b := by
  cases desc <;> obtain ⟨d,hd,rfl⟩ := h
  all_goals try exact valid
  apply DescriptorIndices.of_fields valid
  · rfl
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    simp only [List.getElem_map, alloc.vec.Vec.set_val_eq, List.getElem_set]
    split <;> simp_all

theorem DescriptorIndices.exports {a b xs} (valid : DescriptorIndices a.code)
    (h : Module.Sections.ExportsAdded a xs b) : DescriptorIndices b.code := by
  induction h with
  | nil => exact valid
  | snoc _ ha ih => exact ih.marked ha.2.2.2

theorem DescriptorIndices.imports {a b xs} (valid : DescriptorIndices a.code)
    (h : Module.Sections.ImportsAdded a xs b) : DescriptorIndices b.code := by
  induction h with
  | nil => exact valid
  | @snoc _ before after entry _ ha ih =>
    obtain ⟨_, update⟩ := ha
    cases he : entry.desc <;> simp only [he] at update
    case Func idx =>
      obtain ⟨bound, state, funcs, _⟩ := update
      have ht : after.code.types = before.code.types := by rw [state]
      intro d hd
      rw [funcs] at hd
      rcases List.mem_append.mp hd with hm | hm
      · simpa only [ht] using ih d hm
      · obtain rfl := List.mem_singleton.mp hm
        simpa only [ht] using bound
    all_goals rw [update.1]; exact ih

end Itasca.Module.Environment
