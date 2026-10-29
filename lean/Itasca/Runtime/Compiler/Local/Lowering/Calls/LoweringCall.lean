import Itasca.Runtime.Compiler.Local.Lowering.Emission.Lowering
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
/-! Actual direct-call lowering constructs a retained structured certificate
from source signature and compiler slot metadata. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

set_option maxRecDepth 4096 in
@[step] theorem lower_call {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (before : List valtype) (index paramSlots base : U32)
    (layout : CompilerLayout compiler before) (reachable : compiler.reachable = true)
    (signature : compiler.func_param_slots.val[index.val]? = some paramSlots)
    (arguments : compiler.height.val = base.val + paramSlots.val)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 16#u16 index 0#u32 0#u128 ⦃ out =>
      out.1 = .Ok () → Lowered compiler out.2 (.Call index base) (types.map Itasca.Translate.valueType) ⦄ := by
  have run : runtime.compiler.lower.FunctionCompiler.op ops compiler state 16#u16 index 0#u32 0#u128 = (do
      let i ← lift (UScalar.cast .Usize index)
      let slots ← Slice.index_usize compiler.func_param_slots i
      let o ← lift (U32.checked_sub compiler.height slots)
      let r ← core.option.Option.ok_or o Itasca.error.VisitError.OutOfMemory
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state (.Call index val)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame Itasca.error.VisitError) residual
        Result.ok (r1, compiler)) := by
    unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_pos reachable]
    rfl
  rw [run]
  step as ⟨i, hi⟩
  have bound : i.val < compiler.func_param_slots.length := by
    have found := (List.getElem?_eq_some_iff.mp signature).1
    scalar_tac
  step as ⟨slots, hslots⟩
  have same : slots = paramSlots := by
    have atIndex : i.val = index.val := by scalar_tac
    simp only [atIndex] at hslots
    exact hslots.trans ((List.getElem?_eq_some_iff.mp signature).2)
  rw [same]
  step as ⟨o, ho⟩
  cases o with
  | none => simp only at ho; omega
  | some word =>
    have same : word = base := by
      apply UScalar.eq_of_val_eq
      simp only at ho
      omega
    subst word
    simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    exact finish_op ops law compiler state types _ before layout concrete codeFits sourceFits coordinateFits

end Itasca.Runtime.Compiler
