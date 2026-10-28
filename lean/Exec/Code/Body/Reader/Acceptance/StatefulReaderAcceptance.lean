import Exec.Code.Body.Reader.Common.StatefulReaderPost
import Exec.Code.Local.Capacity.StatefulAvailability
import Exec.Code.Local.Capacity.DeadOpAvailability

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Independent Wasm 2 source-reader typing supplies the complete
stateful signature and live operands. Dead paths only observe the source stack.
This covers references, table operations, and memory/bulk metadata callbacks. -/
theorem StatefulReaderPost.available {data env locals index st} {p : Wasm2.Pending data env .Wasm2 locals index st}
    {out : code.OpIterState} {op : Abs.Stateful.Instruction} (post : StatefulReaderPost p out op)
    {A : Type} (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (demand : CallbackDemand compiler out bound)
    (C : context) (matched : EnvTranslation.Matches env ⟨locals,p.ft.results⟩ C)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (pairs : compiler.function.indirect.length ≤ compiler.function.code.length) (a b : U32) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler out (statefulOpcode op) a b 0#u128 ⦃ result =>
      result.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget result.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨_,_,typesPost⟩ := post
    obtain ⟨front,input,output,signature,beforeTypes,_⟩ := typesPost C matched (known live) (monomorphic live)
    have layout := wholeLayout live
    rw [beforeTypes] at layout
    have pc := demand.pc
    have capacity := demand.codeCapacity
    have reserve := demand.codeReserve
    simp only [alloc.vec.Vec.length] at pairs pc capacity reserve
    exact compiler_stateful_available ops bound available compiler out demand C front input output op signature a b
      (fun _ => layout)
      (fun _ => by change compiler.function.indirect.val.length ≤ U32.max; omega)
      (fun _ => by change compiler.function.indirect.val.length < Usize.max; omega)
      (fun _ => by change compiler.function.indirect.val.length+1 ≤ bound; omega)
  · apply WP.spec_mono (compiler_dead_op_available ops bound available compiler out (statefulOpcode op) a b
      0#u128 live demand.operands demand.slots)
    intro result held
    rw [held.2]
    exact ⟨held.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Itasca.Runtime.Code
