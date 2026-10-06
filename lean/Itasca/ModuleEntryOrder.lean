import Itasca.ModuleDeferred

open Aeneas Aeneas.Std

namespace Itasca.ModuleCodeVisitor

/-- Framing dispatches the remaining defined functions once each, in increasing
function-section order, independently of whether the callbacks validate them. -/
theorem EntriesRun.indices {V : Type} {visitor : module.CodeVisitor V}
    {data env v pos index v' finish entries}
    (h : EntriesRun visitor data env v pos index v' finish entries) :
    entries.map (fun entry => entry.1.val) =
      List.range' index.val (env.func_type_indices.val.length - index.val) := by
  induction h with
  | done _ _ index hs => simp [Nat.sub_eq_zero_of_le hs]
  | @more v v1 v2 v3 v' pos content last index j need finish entries hm hn hw hf hw2 he hj ht ih =>
    have hval := UScalar.add_spec (x := index) (y := 1#usize) (by scalar_tac)
    rw [hj, WP.spec_ok] at hval
    change j.val = index.val + 1 at hval
    have hn : env.func_type_indices.val.length - index.val =
        (env.func_type_indices.val.length - j.val) + 1 := by scalar_tac
    simp only [List.map_cons, ih, hn, List.range'_succ]
    simp only [hval]

/-- The accepted code-section handoffs cover exactly the declared function
count; imported functions are excluded from this defined-function index. -/
theorem SectionRun.indices {V : Type} {visitor : module.CodeVisitor V}
    {data pos env v v' finish entries}
    (h : SectionRun visitor data pos env v v' finish entries) :
    entries.map (fun entry => entry.1.val) = List.range env.func_type_indices.val.length := by
  cases h with
  | absent _ _ _ hc =>
    have hs := module.code_section.spec data pos env
    rw [hc, WP.spec_ok] at hs
    change env.func_type_indices.val = [] at hs
    simp [hs]
  | present _ _ _ _ he => simpa [List.range_eq_range'] using he.indices

theorem SectionRun.count {V : Type} {visitor : module.CodeVisitor V}
    {data pos env v v' finish entries}
    (h : SectionRun visitor data pos env v v' finish entries) :
    entries.length = env.func_type_indices.val.length := by
  simpa using congrArg List.length h.indices

end Itasca.ModuleCodeVisitor

namespace Itasca

/-- A recording consumer's successful code walk appends one obligation per
defined function, in exact index order, including the zero-function case. -/
theorem module.validate_code_with.recorded_order {V : Type}
    (visitor : module.CodeVisitor V) (observe : V → List ModuleCodeVisitor.Entry)
    (hr : ModuleCodeVisitor.Records visitor observe)
    (data : Slice U8) (pos : Usize) (env : module.Env) (v v' : V) (finish : Usize)
    (h : module.validate_code_with visitor data pos env v = .ok (.Ok finish, v')) :
    ∃ entries, observe v' = observe v ++ entries ∧
      entries.map (fun entry => entry.1.val) = List.range env.func_type_indices.val.length ∧
      entries.length = env.func_type_indices.val.length := by
  obtain ⟨entries, he⟩ := ModuleCodeVisitor.SectionRun.of_accepted visitor data pos env v v' finish h
  exact ⟨entries, he.records hr, he.indices, he.count⟩

end Itasca
