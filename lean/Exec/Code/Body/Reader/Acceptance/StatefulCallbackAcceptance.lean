import Exec.Code.Body.Reader.Acceptance.StatefulReaderAcceptance
import Exec.Code.Local.Relations.Calls.StatefulCallbacks
import Itasca.Visitor.Events

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
