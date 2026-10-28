import Itasca.Runtime.Spec.Wf

/-! The per-export source judgment scopes address membership under export
iteration. In particular it has no global nonempty-namespace requirement. -/
namespace Itasca.Runtime.Spec

/-- The source repair expresses exactly well-formed export membership. -/
theorem exportinst_in_iff (addresses : List externaddr) (entry : exportinst) :
    Exportinst_in addresses entry ↔ entry.ADDR ∈ addresses ∧ wf_exportinst entry := by
  constructor
  · intro member
    cases member with
    | mk_Exportinst_in _ contains wellFormed =>
      exact ⟨List.contains_iff_mem.mp contains, wellFormed⟩
  · rintro ⟨member, wellFormed⟩
    exact .mk_Exportinst_in addresses entry (List.length_pos_of_mem member)
      (List.contains_iff_mem.mpr member) wellFormed

/-- Empty exports satisfy the generated premise even for an empty namespace. -/
theorem empty_exports_in (addresses : List externaddr) :
    Forall (Exportinst_in addresses) [] := by
  simp [Forall]

end Itasca.Runtime.Spec
