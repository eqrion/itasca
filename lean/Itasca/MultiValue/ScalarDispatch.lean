import Itasca.MultiValue.ScalarStep
import Itasca.MultiValue.Dispatch

open Aeneas Aeneas.Std

namespace Itasca.MultiValue

/-- All non-control opcodes use the capacity-guarded shared scalar arm. -/
theorem step.scalar_eq (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (opcode : U8) (hscalar : opcode.val ∉ controlOpcodes) :
    step st data env ctx index opcode =
      if alloc.vec.Vec.len st.core.vals = core.num.Usize.MAX then
        .ok (.Err .StackTooLarge, st)
      else (do
        let (r, s, _) ← code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
          st.core data env ctx opcode ()
        .ok (r, {st with core := s})) := by
  unfold step
  split <;> try rfl
  all_goals exact False.elim (hscalar (by decide))

/-- The multi-value dispatcher uses the selected type index for returns;
the shared context contributes only locals for every opcode. -/
theorem step_context (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (ctx ctx' : code.Context) (index : U32) (opcode : U8)
    (hlocals : ctx.locals = ctx'.locals) :
    step st data env ctx index opcode = step st data env ctx' index opcode := by
  by_cases hs : opcode.val ∉ controlOpcodes
  · rw [step.scalar_eq st data env ctx index opcode hs,
      step.scalar_eq st data env ctx' index opcode hs,
      scalar_context _ st.core data env ctx ctx' opcode () hs hlocals]
  · have hm := Classical.not_not.mp hs
    obtain ⟨⟨n, hn⟩⟩ := opcode
    change n ∈ controlOpcodes at hm
    simp only [controlOpcodes, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h | h | h | h | h <;>
      subst n <;> simp [step]

/-- Scalar preservation includes the extracted capacity guard. -/
theorem Pending.scalar_step {data env locals index st} (p : Pending data env locals index st)
    (ctx : code.Context) (hlocals : ctx.locals = locals)
    (opcode : U8) (hscalar : opcode.val ∉ controlOpcodes)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode) :
    step st data env ctx index opcode ⦃ r => r.1 = .Ok () → p.After r.2 ⦄ := by
  rw [step.scalar_eq st data env ctx index opcode hscalar]
  split
  · simp
  · rename_i hn
    have hsize : st.core.vals.val.length < Usize.max := by scalar_tac
    obtain ⟨⟨r, s, v⟩, hr, hout⟩ := WP.spec_imp_exists
      (p.scalar code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor () FullVisitor.empty_total ctx hlocals
        opcode hscalar hsize hbyte)
    rw [WP.spec_equiv_exists]
    exact ⟨(r, {st with core := s}), by simp [hr], hout⟩

end Itasca.MultiValue
