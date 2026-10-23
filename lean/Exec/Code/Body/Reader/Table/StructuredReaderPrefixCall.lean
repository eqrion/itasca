import Exec.Code.Body.Control.Table.StructuredCompilerPrefixAdvance
import Exec.Code.Body.Reader.Calls.ReaderCallLowering
import Exec.Code.Body.Reader.Common.ReaderSpan
import Exec.Code.Body.Control.Table.StructuredLinearEmbedding
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_call_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    {emit types returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types (env.func_types.val.map EnvTranslation.funcType) returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (metadata : FunctionParameterSlots initial env)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_CALL)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_CALL before = .ok (.Ok (), out, after)) :
    ∃ (callee : U32) (ft : Itasca.types.FuncType) (values : List code.StackType),
      env.func_types.val[callee.val]? = some ft ∧
      ReaderPostWasm2 p out.core (.CALL (.mk_uN callee.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types (env.func_types.val.map EnvTranslation.funcType) returns locals parents (current.advance (.CALL (.mk_uN callee.val)))
        out.core.vals.val out.core.pos.val := by
  have metadataBefore : FunctionParameterSlots before env := by
    simpa only [FunctionParameterSlots, invariant.metadata.fields.2.1] using metadata
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
  obtain ⟨codeFits, sourceFits, _, _⟩ := invariant.capacities bound
  have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    have position := p.inbounds
    omega
  obtain ⟨ordinary, sources, cursor, callee, ft, values, front, base, found, inputTypes, post, arguments, lower⟩ :=
    reader_emit_call_wasm2 p ops law before after out ctx (invariant.known reachable) monomorphic metadataBefore retained.layout reachable
      codeFits sourceFits coordinateFits (by simpa only [global_simps] using byte)
      (by simpa only [global_simps] using accepted)
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨callee, ft, values, found, post, invariant.call reachable ordinary lower inputTypes ?_ ?_ sources consumed ?_⟩
  · simp only [List.getElem?_map, found, Option.map_some, EnvTranslation.funcType]
  · simpa only [retained.localsEq] using arguments
  · rw [cursor]

end Exec.Code
