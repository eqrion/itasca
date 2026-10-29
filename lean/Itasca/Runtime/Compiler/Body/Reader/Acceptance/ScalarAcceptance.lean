import Itasca.Runtime.Compiler.Body.Reader.Acceptance.LiteralAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Acceptance.ReachedSimpleAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalAcceptance

/-!
The ordinary scalar readers whose source parsing and callback acceptance are independent of prefix decoding and structured-control dispatch.

Main declarations: `ScalarReaderKind` and `opcode`. A direct consumer is `Compiler.Body.Reader.Acceptance.SourceBoundScalarAcceptance`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- The ordinary scalar readers whose source parsing and callback acceptance
are independent of prefix decoding and structured-control dispatch. -/
inductive ScalarReaderKind where
  | nop
  | unreachable
  | drop
  | select
  | local_get
  | local_set
  | local_tee
  | global_get
  | global_set
  | i32_const
  | i64_const
  | f32_const
  | f64_const

namespace ScalarReaderKind

def opcode : ScalarReaderKind → U8
  | .nop => code.OP_NOP
  | .unreachable => code.OP_UNREACHABLE
  | .drop => code.OP_DROP
  | .select => code.OP_SELECT
  | .local_get => code.OP_LOCAL_GET
  | .local_set => code.OP_LOCAL_SET
  | .local_tee => code.OP_LOCAL_TEE
  | .global_get => code.OP_GLOBAL_GET
  | .global_set => code.OP_GLOBAL_SET
  | .i32_const => code.OP_I32_CONST
  | .i64_const => code.OP_I64_CONST
  | .f32_const => code.OP_F32_CONST
  | .f64_const => code.OP_F64_CONST

def Parameter : ScalarReaderKind → Type
  | .nop => Unit
  | .unreachable => Unit
  | .drop => code.StackType
  | .select => code.StackType
  | .local_get => U32
  | .local_set => U32
  | .local_tee => U32
  | .global_get => U32
  | .global_set => U32
  | .i32_const => I32
  | .i64_const => I64
  | .f32_const => U32
  | .f64_const => U64

def read (kind : ScalarReaderKind) (st : code.OpIterState) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) : Result (core.result.Result kind.Parameter error.OpError × code.OpIterState) :=
  match kind with
  | .nop => .ok (.Ok (),st)
  | .unreachable => code.read_unreachable st
  | .drop => code.read_drop st
  | .select => code.read_select st
  | .local_get => code.read_local_get st data ctx
  | .local_set => code.read_local_set st data ctx
  | .local_tee => code.read_local_tee st data ctx
  | .global_get => code.read_global_get st data env
  | .global_set => code.read_global_set st data env
  | .i32_const => code.read_i32_const st data
  | .i64_const => code.read_i64_const st data
  | .f32_const => code.read_f32_const st data
  | .f64_const => code.read_f64_const st data

def action : (kind : ScalarReaderKind) → kind.Parameter → Action
  | .nop => fun _ => .nop
  | .unreachable => fun _ => .unreachable
  | .drop => .drop
  | .select => .select
  | .local_get => .local_get
  | .local_set => .local_set
  | .local_tee => .local_tee
  | .global_get => .global_get
  | .global_set => .global_set
  | .i32_const => .i32_const
  | .i64_const => .i64_const
  | .f32_const => .f32_const
  | .f64_const => .f64_const

/-- Each inventory entry is checked against actual extracted source dispatch. -/
theorem dispatch {V : Type} (kind : ScalarReaderKind) (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (before : V) :
    code.step visitor st data env ctx kind.opcode before =
      CoreVisitor.run (kind.read st data env ctx)
        (fun log state value => invoke visitor log (.op state (kind.action value))) before := by
  cases kind
  · exact dispatch_nop visitor st data env ctx before
  · exact dispatch_unreachable visitor st data env ctx before
  · exact dispatch_drop visitor st data env ctx before
  · exact dispatch_select visitor st data env ctx before
  · exact dispatch_local_get visitor st data env ctx before
  · exact dispatch_local_set visitor st data env ctx before
  · exact dispatch_local_tee visitor st data env ctx before
  · exact dispatch_global_get visitor st data env ctx before
  · exact dispatch_global_set visitor st data env ctx before
  · exact dispatch_i32_const visitor st data env ctx before
  · exact dispatch_i64_const visitor st data env ctx before
  · exact dispatch_f32_const visitor st data env ctx before
  · exact dispatch_f64_const visitor st data env ctx before

theorem ordinary (kind : ScalarReaderKind) : kind.opcode.val ∉ Wasm2.controlOpcodes := by
  cases kind <;> simp only [opcode,global_simps,Wasm2.controlOpcodes] <;> decide

theorem plain (kind : ScalarReaderKind) : kind.opcode.val ∉ [28,37,38,208,209,210,252,253] := by
  cases kind <;> simp only [opcode,global_simps,Wasm2.controlOpcodes] <;> decide

theorem sign (kind : ScalarReaderKind) : Wasm2.NumericExtensions.signMeaning kind.opcode = none := by
  cases kind <;> simp only [opcode,global_simps,Wasm2.NumericExtensions.signMeaning] <;> decide

theorem misc (kind : ScalarReaderKind) : kind.opcode ≠ code.OP_MISC_PREFIX := by
  cases kind <;> simp only [opcode,global_simps,Wasm2.controlOpcodes] <;> decide

/-- Replay every inventory entry from the actual independent source reader.
The source stack and retained compiler layout determine operand shapes. -/
theorem available {A V : Type} (kind : ScalarReaderKind)
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler out bound) (localsMatch : compiler.function.locals = ctx.locals)
    (capacity : st.vals.val.length < Usize.max)
    (outer segment : List code.StackType) (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length)
    (monomorphic : compiler.reachable = true → Control.polymorphic st = false)
    (known : compiler.reachable = true → ConcreteStack st.vals.val)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.vals.val))
    (reference : code.step source st data env ctx kind.opcode before = .ok (.Ok (),out,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx kind.opcode compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  cases kind with
  | nop =>
      exact compiler_reader_nop_available ops bound allocation source before after compiler st out data env ctx
        demand reference
  | unreachable =>
      exact compiler_reader_unreachable_available ops bound allocation source before after compiler st out data env ctx
        demand reference
  | drop =>
      exact compiler_reader_drop_available ops bound allocation source before after compiler st out data env ctx
        demand reference
  | select =>
      exact reached_reader_select_available ops bound allocation source before after compiler st out data env ctx
        demand capacity outer segment values base monomorphic known wholeLayout reference
  | local_get =>
      exact compiler_reader_local_get_available ops bound allocation source before after compiler st out data env ctx
        demand localsMatch capacity wholeLayout reference
  | local_set =>
      exact compiler_reader_local_set_available ops bound allocation source before after compiler st out data env ctx
        demand localsMatch capacity outer segment values base monomorphic known wholeLayout reference
  | local_tee =>
      exact compiler_reader_local_tee_available ops bound allocation source before after compiler st out data env ctx
        demand localsMatch capacity outer segment values base monomorphic known wholeLayout reference
  | global_get =>
      exact compiler_reader_global_get_available ops bound allocation source before after compiler st out data env ctx
        demand reference
  | global_set =>
      exact reached_reader_global_set_available ops bound allocation source before after compiler st out data env ctx
        demand outer segment values base monomorphic known wholeLayout reference
  | i32_const =>
      exact compiler_reader_i32_const_available ops bound allocation source before after compiler st out data env ctx
        demand reference
  | i64_const =>
      exact compiler_reader_i64_const_available ops bound allocation source before after compiler st out data env ctx
        demand reference
  | f32_const =>
      exact compiler_reader_f32_const_available ops bound allocation source before after compiler st out data env ctx
        demand reference
  | f64_const =>
      exact compiler_reader_f64_const_available ops bound allocation source before after compiler st out data env ctx
        demand reference

end ScalarReaderKind
end Itasca.Runtime.Code
