import Exec.Spec.Choices.SimdListDeterminism
/-! Canonical integer operands and injective source lane-kind embeddings. -/

namespace Exec.Spec
open SpecExt

theorem source_integer_num_unique (type : Inn) {left right : num_}
    (first : wf_num_ (numtype_Inn type) left) (second : wf_num_ (numtype_Inn type) right)
    (same : (proj_num__0 left).get! =(proj_num__0 right).get!) : left=right := by
  cases type <;> cases first <;> cases second
  all_goals try casesm* Inn
  all_goals try casesm* Fnn
  all_goals simp_all [numtype_Inn,numtype_Fnn,proj_num__0]

theorem source_lane_kind_injective {left right : Jnn} (same : lanetype_Jnn left=lanetype_Jnn right) : left=right := by
  cases left <;> cases right <;> simp_all [lanetype_Jnn]

theorem source_pack_lane_kind_injective {left right : packtype}
    (same : lanetype_packtype left=lanetype_packtype right) : left=right := by
  cases left <;> cases right <;> simp_all [lanetype_packtype]

theorem source_num_lane_kind_injective {left right : numtype}
    (same : lanetype_numtype left=lanetype_numtype right) : left=right := by
  cases left <;> cases right <;> simp_all [lanetype_numtype]
end Exec.Spec
