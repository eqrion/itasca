import Exec.Code.Local.Relations.Common.SelectSafety
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

@[step] theorem compiler_i32_const_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bits : U128)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 65#u16 0#u32 0#u32 bits ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  by_cases live : compiler.reachable = true
  · have run : runtime.compiler.lower.FunctionCompiler.op ops compiler state 65#u16 0#u32 0#u32 bits =
        (do
          let word ← lift (UScalar.cast .U32 bits)
          runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state
            (.Const32 compiler.height word)) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos live]
      rfl
    rw [run]
    simp only [lift,bind_ok]
    exact finish_op_observed ops law compiler state _ codeFits sourceFits coordinateFits
  · unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_neg live]
    exact compiler_observe_stack ops law compiler state

@[step] theorem compiler_on_i32_const_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bits : I32)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_i32_const compiler state bits ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const,lift,bind_ok]
  exact compiler_i32_const_total ops law compiler state _ codeFits sourceFits coordinateFits

@[step] theorem compiler_i64_const_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bits : U128)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 66#u16 0#u32 0#u32 bits ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  by_cases live : compiler.reachable = true
  · have run : runtime.compiler.lower.FunctionCompiler.op ops compiler state 66#u16 0#u32 0#u32 bits =
        (do
          let word ← lift (UScalar.cast .U64 bits)
          runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state
            (.Const64 compiler.height word)) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos live]
      rfl
    rw [run]
    simp only [lift,bind_ok]
    exact finish_op_observed ops law compiler state _ codeFits sourceFits coordinateFits
  · unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_neg live]
    exact compiler_observe_stack ops law compiler state

@[step] theorem compiler_on_i64_const_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bits : I64)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_i64_const compiler state bits ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const,lift,bind_ok]
  exact compiler_i64_const_total ops law compiler state _ codeFits sourceFits coordinateFits

@[step] theorem compiler_f32_const_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bits : U128)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 67#u16 0#u32 0#u32 bits ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  by_cases live : compiler.reachable = true
  · have run : runtime.compiler.lower.FunctionCompiler.op ops compiler state 67#u16 0#u32 0#u32 bits =
        (do
          let word ← lift (UScalar.cast .U32 bits)
          runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state
            (.Const32 compiler.height word)) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos live]
      rfl
    rw [run]
    simp only [lift,bind_ok]
    exact finish_op_observed ops law compiler state _ codeFits sourceFits coordinateFits
  · unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_neg live]
    exact compiler_observe_stack ops law compiler state

@[step] theorem compiler_on_f32_const_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bits : U32)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_f32_const compiler state bits ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f32_const,lift,bind_ok]
  exact compiler_f32_const_total ops law compiler state _ codeFits sourceFits coordinateFits

@[step] theorem compiler_f64_const_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bits : U128)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 68#u16 0#u32 0#u32 bits ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  by_cases live : compiler.reachable = true
  · have run : runtime.compiler.lower.FunctionCompiler.op ops compiler state 68#u16 0#u32 0#u32 bits =
        (do
          let word ← lift (UScalar.cast .U64 bits)
          runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state
            (.Const64 compiler.height word)) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos live]
      rfl
    rw [run]
    simp only [lift,bind_ok]
    exact finish_op_observed ops law compiler state _ codeFits sourceFits coordinateFits
  · unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_neg live]
    exact compiler_observe_stack ops law compiler state

@[step] theorem compiler_on_f64_const_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bits : U64)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_f64_const compiler state bits ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f64_const,lift,bind_ok]
  exact compiler_f64_const_total ops law compiler state _ codeFits sourceFits coordinateFits

@[step] theorem compiler_on_nop_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_nop compiler state ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  have run : (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_nop compiler state =
      runtime.compiler.FunctionCompiler.observe ops compiler state := by
    change runtime.compiler.lower.FunctionCompiler.op ops compiler state 1#u16 0#u32 0#u32 0#u128 = _
    unfold runtime.compiler.lower.FunctionCompiler.op
    split <;> rfl
  rw [run]
  exact compiler_observe_stack ops law compiler state

@[step] theorem compiler_on_drop_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (type : Itasca.code.StackType) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_drop compiler state type ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  have run : (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_drop compiler state type =
      runtime.compiler.FunctionCompiler.observe ops compiler state := by
    change runtime.compiler.lower.FunctionCompiler.op ops compiler state 26#u16 0#u32 0#u32 0#u128 = _
    unfold runtime.compiler.lower.FunctionCompiler.op
    split <;> rfl
  rw [run]
  exact compiler_observe_stack ops law compiler state

end Itasca.Runtime.Code
