import Itasca.Runtime.Compiler.Body.Reader.Stateful.StatefulPost
import Itasca.Runtime.Compiler.Local.Capacity.StatefulAvailability
import Itasca.Runtime.Compiler.Local.Capacity.DeadOpAvailability
import Itasca.Runtime.Compiler.Local.Relations.Calls.StatefulCallbacks
import Itasca.Visitor.Events

/-!
Stateful reader acceptance and its callback-action lift. StatefulReaderPost.available connects the source postcondition to actual callback replay.
-/

/-! ## Stateful Reader Acceptance -/

section

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

end

/-! ## Stateful Callback Acceptance -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Named source event for each actual stateful visitor hook. -/
def statefulAction (op : Abs.Stateful.Instruction) (a b : U32) : Action :=
  match op with
  | .refNull .FUNCREF => .ref_null .FuncRef
  | .refNull .EXTERNREF => .ref_null .ExternRef
  | .refFunc _ => .ref_func a
  | .refIsNull => .ref_is_null
  | .tableGet _ => .table_get a
  | .tableSet _ => .table_set a
  | .tableSize _ => .table_size a
  | .tableGrow _ => .table_grow a
  | .tableFill _ => .table_fill a
  | .tableCopy .. => .table_copy a b
  | .tableInit .. => .table_init a b
  | .elemDrop _ => .elem_drop a
  | .memorySize => .memory_size
  | .memoryGrow => .memory_grow
  | .memoryFill => .memory_fill
  | .memoryCopy => .memory_copy
  | .memoryInit _ => .memory_init a
  | .dataDrop _ => .data_drop a

theorem stateful_callback_invoke {V : Type} (visitor : code.OpVisitor V) (before : V)
    (state : code.OpIterState) (op : Abs.Stateful.Instruction) (a b : U32) :
    statefulCallback visitor before state op a b = invoke visitor before (.op state (statefulAction op a b)) := by
  cases op <;> try rfl
  rename_i ty
  cases ty <;> rfl

/-- Source-reader typing and bounded lowering establish acceptance of the
actual stateful hook, with the checked compiler argument order. -/
theorem StatefulReaderPost.callback_available {data env locals index st} {p : Wasm2.Pending data env .Wasm2 locals index st}
    {out : code.OpIterState} {op : Abs.Stateful.Instruction} (post : StatefulReaderPost p out op)
    {A : Type} (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (demand : CallbackDemand compiler out bound)
    (C : context) (matched : EnvTranslation.Matches env ⟨locals,p.ft.results⟩ C)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (pairs : compiler.function.indirect.length ≤ compiler.function.code.length)
    (a b : U32) (arguments : StatefulArguments op a b) :
    statefulCallback (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler out op a b
      ⦃ result => result.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget result.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  rw [stateful_callback_lower ops compiler out op a b arguments]
  exact post.available ops bound allocation compiler demand C matched known monomorphic wholeLayout pairs a b

end Itasca.Runtime.Code

end
