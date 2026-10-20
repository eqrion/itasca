import Exec.Code.Body.Reader.Memory.StatefulMemoryReaderWasm1
import Exec.Code.Body.Reader.Acceptance.StatefulReaderAcceptance
import Exec.Code.Local.Capacity.ReaderAcceptance

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Independently accepted Wasm 1 memory metadata readers establish their
source signatures and all live operands before actual callback lowering. -/
theorem reached_reader_stateful_memory_available_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (opcode : U8) (member : opcode.val ∈ [63,64])
    (demand : CallbackDemand compiler out bound) (C : context) (matched : EnvTranslation.Matches env ctx C)
    (known : compiler.reachable = true → ConcreteStack st.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.vals.val))
    (pairs : compiler.function.indirect.length ≤ compiler.function.code.length)
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (reference : code.step source st data env ctx opcode before = .ok (.Ok (),out,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx opcode compiler
      ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with member | member
  · have equal : opcode = code.OP_MEMORY_SIZE := by apply UScalar.eq_of_val_eq; simpa [global_simps] using member
    rw [equal] at byte reference ⊢
    rw [code.step_memory_size.dispatch] at reference ⊢
    refine CoreVisitor.run.accepted_lift_on (code.read_memory_size st data env)
      (fun v state (_ : Unit) => source.on_memory_size v state)
      (fun v state (_ : Unit) => (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_memory_size v state)
      before after compiler out (fun after => CompilationBudgetEffect compiler.budget after.budget
        (fun counter => if counter = .instructions then 1 else 0)) reference ?_
    intro value read _
    cases value
    have post := reader_memory_size_post_wasm1 p (by simpa only [global_simps] using byte)
      (by have room := p.val_capacity; omega) out read
    exact post.available ops bound allocation compiler demand C matched known monomorphic wholeLayout pairs 0#u32 0#u32
  · have equal : opcode = code.OP_MEMORY_GROW := by apply UScalar.eq_of_val_eq; simpa [global_simps] using member
    rw [equal] at byte reference ⊢
    rw [code.step_memory_grow.dispatch] at reference ⊢
    refine CoreVisitor.run.accepted_lift_on (code.read_memory_grow st data env)
      (fun v state (_ : Unit) => source.on_memory_grow v state)
      (fun v state (_ : Unit) => (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_memory_grow v state)
      before after compiler out (fun after => CompilationBudgetEffect compiler.budget after.budget
        (fun counter => if counter = .instructions then 1 else 0)) reference ?_
    intro value read _
    cases value
    have post := reader_memory_grow_post_wasm1 p (by simpa only [global_simps] using byte)
      (by have room := p.val_capacity; omega) out read
    exact post.available ops bound allocation compiler demand C matched known monomorphic wholeLayout pairs 0#u32 0#u32

end Exec.Code
