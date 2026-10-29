import Itasca.Runtime.Compiler.Local.Lowering.Emission.Lowering

/-!
NOP and DROP update the validator-derived stack layout without emitting code.

Main declarations: `LoweredEmpty`. A direct consumer is `Compiler.Body.Source.TypedLowering`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- NOP and DROP update the validator-derived stack layout without emitting code. -/
def LoweredEmpty {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (stack : List valtype) : Prop :=
  after.function.code = before.function.code ∧
  CompilerLayout after stack ∧ compilerLocals after = compilerLocals before ∧
  after.reachable = before.reachable ∧
  before.function.slot_count.val ≤ after.function.slot_count.val

@[step] theorem compiler_observe_empty {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (before : List valtype) (layout : CompilerLayout compiler before)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val) :
    runtime.compiler.FunctionCompiler.observe ops compiler state ⦃ out => out.1 = .Ok () →
      LoweredEmpty compiler out.2 (types.map Itasca.Translate.valueType) ⦄ := by
  obtain ⟨out, called, info⟩ := WP.spec_imp_exists (compiler_observe ops law compiler state)
  rw [called, WP.spec_ok]
  intro accepted
  obtain ⟨_, _, locals, _, _, reachable, code, _, _, _, capacity, _, _⟩ := info accepted
  have newLayout := compiler_observe_layout ops law compiler state types concrete layout.localSlots layout.localOffsets
  rw [called, WP.spec_ok] at newLayout
  exact ⟨code, newLayout accepted, by simp [compilerLocals, locals], reachable, capacity⟩

theorem lower_empty_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (drop : Bool) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (if drop then 26#u16 else 1#u16) 0#u32 0#u32 0#u128 =
      runtime.compiler.FunctionCompiler.observe ops compiler state := by
  cases drop <;> unfold runtime.compiler.lower.FunctionCompiler.op <;> split <;> rfl

end Itasca.Runtime.Compiler
