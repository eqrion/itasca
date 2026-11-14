import Itasca.Runtime.Compiler.Local.Lowering.Emission.Pair
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Initializer.InitializerElementAppend
import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Frame
import Itasca.Runtime.Compiler.Local.Relations.Select.SelectOperands
import Itasca.Runtime.Compiler.Local.Relations.Global.GlobalOperands
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission

/-!
Sections, each formerly its own module: PairSuccess, DeadCode, CoreBasicEmissions.
-/

/-! ## PairSuccess -/

section

/-!
Successful pair allocation retains the whole compiler frame and appends exactly the two supplied source indices at the returned entry.

Main declarations: `compiler_pair_success`. A direct consumer is `Compiler.Local.Relations.Calls.IndirectCallLowering`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Successful pair allocation retains the whole compiler frame and appends
exactly the two supplied source indices at the returned entry. -/
theorem compiler_pair_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (a b entry : U32)
    (accepted : runtime.compiler.FunctionCompiler.pair ops before a b = .ok (.Ok entry, after)) :
    ∃ budget pairs,
      after = { before with budget, function := {before.function with indirect := pairs} } ∧
      pairs.val = before.function.indirect.val ++ [(a,b)] ∧
      entry.val = before.function.indirect.val.length := by
  obtain ⟨pairs, same, appended, indexEq⟩ :=
    ((runtime.compiler.FunctionCompiler.pair.inv ops before after a b (.Ok entry) accepted).2 law).2 entry rfl
  exact ⟨before.budget, pairs, same, appended, indexEq⟩


end Itasca.Runtime.Compiler

end

/-! ## DeadCode -/

section

/-!
Code and reachability effects of observation and unreachable callbacks.

Main declarations: `ObserveFrame.code` and `callback_unreachable_dead`. A direct consumer is `Compiler.Module.CompileSlice`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

theorem ObserveFrame.code {A : Type} {a b : runtime.compiler.FunctionCompiler A}
    (frame : ObserveFrame a b) : b.function.code = a.function.code := by rw [frame]

theorem ObserveFrame.reachable {A : Type} {a b : runtime.compiler.FunctionCompiler A}
    (frame : ObserveFrame a b) : b.reachable = a.reachable := by rw [frame]

set_option maxRecDepth 4096 in
/-- Every scalar opcode callback in a dead source region only observes the
validator state, preserving code, labels, immutable metadata and deadness. -/
@[step] theorem compiler_op_dead {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (dead : compiler.reachable = false) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state opcode a b bits ⦃ out =>
      ObserveFrame compiler out.2 ⦄ := by
  rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (dead)]
  exact compiler_observe_frame ops law compiler state

@[step] theorem callback_return_dead {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (dead : compiler.reachable = false) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return ops compiler state ⦃ out =>
      ObserveFrame compiler out.2 ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return
  simp only [dead, Bool.false_eq_true, ite_false]
  exact compiler_observe_frame ops law compiler state

@[step] theorem callback_unreachable_dead {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (dead : compiler.reachable = false) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable ops compiler state ⦃ out =>
      ObserveFrame compiler out.2 ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable
  simp only [dead, Bool.false_eq_true, ite_false]
  exact compiler_observe_frame ops law compiler state
end Itasca.Runtime.Compiler

end

/-! ## CoreBasicEmissions -/

section

/-!
Emission certificates for select and global operations.

Main declarations: `compiler_select_emission` and `compiler_global_set_emission`. A direct consumer is `Compiler.Body.Reader.Global.GlobalEmissions`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

@[step] theorem compiler_select_emission {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.wasm_types.ValueType)
    (C : context) (front : List valtype) (ty : valtype)
    (locals : compilerLocals compiler = C.LOCALS)
    (layout : CompilerLayout compiler (front ++ [ty, ty, .I32]))
    (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front ++ [ty])
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 27#u16 0#u32 0#u32 0#u128
      ⦃ out => out.1 = .Ok () → ∃ emitted,
        Lowered compiler out.2 emitted (front ++ [ty]) ∧
        ScalarEmission C (front ++ [ty, ty, .I32]) (.SELECT none) [emitted] (front ++ [ty]) ⦄ := by
  apply WP.spec_mono (compiler_select_lowered ops law compiler state types front ty layout reachable concrete typed
    codeFits sourceFits coordinateFits)
  intro out result success
  obtain ⟨left,right,condition,lp,rp,cp,lowered⟩ := result success
  exact ⟨_, lowered, .select front ty left right condition (by simpa only [locals] using lp) rp cp⟩

@[step] theorem compiler_global_get_emission {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (front : List Itasca.wasm_types.ValueType)
    (ty : Itasca.wasm_types.ValueType) (index : U32) (C : context) (mutability : «mut»)
    (locals : compilerLocals compiler = C.LOCALS)
    (globalType : C.GLOBALS[index.val]? = some (.mk_globaltype mutability (Itasca.Translate.valueType ty)))
    (layout : CompilerLayout compiler (front.map Itasca.Translate.valueType))
    (reachable : compiler.reachable = true)
    (concrete : state.vals.val = (front ++ [ty]).map Itasca.code.StackType.Val)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 35#u16 index 0#u32 0#u128
      ⦃ out => out.1 = .Ok () → ∃ emitted,
        Lowered compiler out.2 emitted ((front ++ [ty]).map Itasca.Translate.valueType) ∧
        ScalarEmission C (front.map Itasca.Translate.valueType) (.GLOBAL_GET (.mk_uN index.val)) [emitted]
          ((front ++ [ty]).map Itasca.Translate.valueType) ⦄ := by
  apply WP.spec_mono (compiler_global_get_lowered ops law compiler state front ty index layout reachable concrete
    codeFits sourceFits coordinateFits)
  intro out result success
  refine ⟨_, result success, ?_⟩
  simpa only [List.map_append, List.map_cons, List.map_nil] using
    ScalarEmission.globalGet (C := C) (front.map Itasca.Translate.valueType) mutability
      (Itasca.Translate.valueType ty) index compiler.height globalType (by simpa only [locals] using layout.height)

@[step] theorem compiler_global_set_emission {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.wasm_types.ValueType)
    (front : List valtype) (ty : valtype) (index : U32) (C : context)
    (locals : compilerLocals compiler = C.LOCALS)
    (globalType : C.GLOBALS[index.val]? = some (.mk_globaltype (some .MUT) ty))
    (layout : CompilerLayout compiler (front ++ [ty]))
    (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 36#u16 index 0#u32 0#u128
      ⦃ out => out.1 = .Ok () → ∃ emitted,
        Lowered compiler out.2 emitted front ∧
        ScalarEmission C (front ++ [ty]) (.GLOBAL_SET (.mk_uN index.val)) [emitted] front ⦄ := by
  apply WP.spec_mono (compiler_global_set_lowered ops law compiler state types front ty index layout reachable concrete typed
    codeFits sourceFits coordinateFits)
  intro out result success
  obtain ⟨source, position, lowered⟩ := result success
  exact ⟨_, lowered, .globalSet front ty index source globalType (by simpa only [locals] using position)⟩
end Itasca.Runtime.Compiler

end
