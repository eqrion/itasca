import Exec.Code.Body.Reader.Table.TableReaderCompilerPoint
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerRoot
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem TypedRunWasm2.fold_tables {A : Type}
    (ops : runtime.platform.Alloc A)
    (emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop)
    (initial : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (ft : Itasca.types.FuncType) (source : List instr)
    (progress : ∀ (st : code.BodyState) (before middle final : runtime.compiler.FunctionCompiler A)
      (next : Usize) (out : code.BodyState),
      TableReaderCompilerPointWasm2 emit initial before types functions returns locals data env ctx.locals index ft st →
      next.val = st.core.pos.val + 1 →
      (inbounds : st.core.pos.val < data.length) →
      code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        {core := {st.core with pos := next}} data env ctx index .Wasm2
        data.val[st.core.pos.val] before = .ok (.Ok (), out, middle) →
      TypedRunWasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx index out middle final →
      StructuredCompiledBody (emit (CompilerTables.ofFunction final.function)) initial final types functions returns locals source ∨
      TableReaderCompilerPointWasm2 emit initial middle types functions returns locals data env ctx.locals index ft out)
    {st before final}
    (run : TypedRunWasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx index st before final)
    (point : TableReaderCompilerPointWasm2 emit initial before types functions returns locals data env ctx.locals index ft st) :
    StructuredCompiledBody (emit (CompilerTables.ofFunction final.function)) initial final types functions returns locals source := by
  induction run with
  | done typed closed finished =>
    obtain ⟨parents, current, savedParents, savedCurrent, state⟩ := point CompilerTables.empty
    obtain ⟨_, _, _, _, _, _, _, blocks, _⟩ := state.boundary.opened
    rw [closed] at blocks
    simp at blocks
  | @step st before next out middle final typed pending start advance called rest ih =>
    have inbounds : st.core.pos.val < data.length := by simpa only [start] using pending.inbounds
    have called' : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        {core := {st.core with pos := next}} data env ctx index .Wasm2
        data.val[st.core.pos.val] before = .ok (.Ok (), out, middle) := by
      simpa only [start] using called
    rcases progress st before middle final next out point advance inbounds called' rest with done | nextPoint
    · exact done
    · exact ih nextPoint


end Exec.Code
