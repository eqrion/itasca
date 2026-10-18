import Exec.Abs.Simd.Transition
import Exec.Abs.Stateful.OwnershipStore
import Exec.Abs.Bound

namespace Exec.Abs.Simd
open SpecExt Exec.Spec Ownership

theorem numeric_value_owned {value : val} {output : valtype}
    (numeric : output = .V128 ∨ ∃ ty : numtype, output = valtype_numtype ty)
    (typeEq : valueType value = output) (bounds : Bounds) : ValueOwned bounds value := by
  cases value with
  | CONST | VCONST | REF_NULL => trivial
  | REF_FUNC_ADDR address =>
    rcases numeric with numeric | ⟨nt,numeric⟩
    · simp_all [valueType]
    · cases nt <;> simp_all [valueType,valtype_numtype]
  | REF_HOST_ADDR address =>
    rcases numeric with numeric | ⟨nt,numeric⟩
    · simp_all [valueType]
    · cases nt <;> simp_all [valueType,valtype_numtype]

theorem transition_owned {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {after : List instr} {source inputs output} {next : AState} {bounds}
    (signature : PureSignature source inputs output)
    (owned : StatefulOwned bounds ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩)
    (step : Transition ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩
      {f with code := source :: after} rest after source inputs output next) : StatefulOwned bounds next := by
  cases step with
  | next front operands value values types effect =>
    have active := owned.values.2 _ (List.mem_cons_self ..)
    change FrameOwned bounds f at active
    change f.vals = front ++ operands at values
    refine ⟨⟨valuesOwned_nil _,?_⟩,owned.heap⟩
    intro item member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · refine ⟨active.1,valuesOwned_append.mpr ⟨?_,?_⟩⟩
      · have before := active.2
        rw [values] at before
        exact (valuesOwned_append.mp before).1
      · exact valuesOwned_cons.mpr ⟨numeric_value_owned signature.output_numeric effect.2 bounds,valuesOwned_nil _⟩
    · exact owned.values.2 item (List.mem_cons_of_mem _ member)

theorem transition_core_typed {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {after : List instr} {source inputs output} {next : AState}
    (signature : PureSignature source inputs output)
    (typed : CoreTyped ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩)
    (step : Transition ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩
      {f with code := source :: after} rest after source inputs output next) : CoreTyped next := by
  have preserved := transition_preservation signature typed.typed step
  cases step
  exact ⟨preserved,typed.contents⟩

theorem transition_bound {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {after : List instr} {source inputs output} {next : AState} {bound}
    (bounded : CodeBound bound ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩)
    (step : Transition ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩
      {f with code := source :: after} rest after source inputs output next) : CodeBound bound next := by
  cases step with
  | next front operands value values types effect =>
    apply bound_replace_frame bounded
    have active := bounded.frames _ (List.mem_cons_self ..)
    refine ⟨?_,active.2⟩
    have size : sizeOf after < sizeOf (source :: after) := by simp
    exact Nat.le_trans (Nat.le_of_lt size) active.1

end Exec.Abs.Simd
