import Itasca.Wasm2.LoopDispatch
import Itasca.Wasm2.Step.Dispatch

/-!
# Result context independence of the body step

`Wasm2.step` dispatches the control opcodes itself and sends every other opcode to
`code.step_wasm2` behind a stack-capacity guard (`step.scalar_eq`). `step_context` shows that the
shared scalar context contributes only locals, so the semantic result context can be replaced by
the runtime's.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- All non-control opcodes use the capacity-guarded shared scalar arm. -/
theorem step.scalar_eq (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (opcode : U8) (hscalar : opcode.val ∉ controlOpcodes) :
    step st data env ctx index opcode =
      if alloc.vec.Vec.len st.core.vals = core.num.Usize.MAX then
        .ok (.Err .StackTooLarge, st)
      else (do
        let (r, s, _) ← code.step_wasm2 code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
          st.core data env ctx opcode ()
        .ok (r, {st with core := s})) := by
  unfold step
  split <;> try rfl
  all_goals exact False.elim (hscalar (by decide))

/-- The Wasm 2.0 body dispatcher uses the selected type index for returns;
the shared context contributes only locals for every opcode. -/
theorem step_context (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (ctx ctx' : code.Context) (index : U32) (opcode : U8)
    (hlocals : ctx.locals = ctx'.locals) :
    step st data env ctx index opcode = step st data env ctx' index opcode := by
  by_cases hs : opcode.val ∉ controlOpcodes
  · rw [step.scalar_eq st data env ctx index opcode hs,
      step.scalar_eq st data env ctx' index opcode hs,
      wasm2_context _ st.core data env ctx ctx' opcode () hs hlocals]
  · have hm := Classical.not_not.mp hs
    obtain ⟨⟨n, hn⟩⟩ := opcode
    change n ∈ controlOpcodes at hm
    simp only [controlOpcodes, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h | h | h | h | h <;>
      subst n <;> simp [step]

end Itasca.Wasm2
