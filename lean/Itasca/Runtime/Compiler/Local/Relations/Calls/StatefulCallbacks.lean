import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulOpcode
import Itasca.Runtime.Equations
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

def statefulCallback {V : Type} (visitor : code.OpVisitor V) (before : V)
    (state : code.OpIterState) (op : SourceMachine.Stateful.Instruction) (a b : U32) :=
  match op with
  | .refNull .FUNCREF => visitor.on_ref_null before state .FuncRef
  | .refNull .EXTERNREF => visitor.on_ref_null before state .ExternRef
  | .refFunc _ => visitor.on_ref_func before state a
  | .refIsNull => visitor.on_ref_is_null before state
  | .tableGet _ => visitor.on_table_get before state a
  | .tableSet _ => visitor.on_table_set before state a
  | .tableSize _ => visitor.on_table_size before state a
  | .tableGrow _ => visitor.on_table_grow before state a
  | .tableFill _ => visitor.on_table_fill before state a
  | .tableCopy .. => visitor.on_table_copy before state a b
  | .tableInit .. => visitor.on_table_init before state a b
  | .elemDrop _ => visitor.on_elem_drop before state a
  | .memorySize => visitor.on_memory_size before state
  | .memoryGrow => visitor.on_memory_grow before state
  | .memoryFill => visitor.on_memory_fill before state
  | .memoryCopy => visitor.on_memory_copy before state
  | .memoryInit _ => visitor.on_memory_init before state a
  | .dataDrop _ => visitor.on_data_drop before state a

/-- The actual visitor forwards precisely the retained descriptor opcode and
immediates; paired table instructions keep their compiler argument order. -/
theorem stateful_callback_lower {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    (op : SourceMachine.Stateful.Instruction) (a b : U32) (arguments : StatefulArguments op a b) :
    statefulCallback (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before state op a b =
      runtime.compiler.lower.FunctionCompiler.op ops before state (statefulOpcode op) a b 0#u128 := by
  cases op <;> simp only [StatefulArguments,statefulArguments] at arguments
  all_goals try (rename_i ty; cases ty <;> simp only [statefulArguments] at arguments)
  all_goals obtain ⟨ha,hb⟩ := arguments
  all_goals try (have zero : b = 0#u32 := (UScalar.eq_equiv _ _).mpr hb; subst b)
  all_goals try (have zero : a = 0#u32 := (UScalar.eq_equiv _ _).mpr ha; subst a)
  all_goals try (have one : a = 1#u32 := (UScalar.eq_equiv _ _).mpr ha; subst a)
  all_goals try rfl
  all_goals simp only [statefulCallback,runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_ref_null,bind_ok,Bool.false_eq_true,↓reduceIte]
  all_goals rfl

end Itasca.Runtime.Compiler
