import Exec.Code.Body.Control.Table.StructuredCompilerPrefixRootWithTables
import Exec.Code.Local.Control.Table.StructuredFunctionBodyCloseWithTables
import Exec.Code.Local.Callbacks.Common.CompilerCloseMetadata
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- The actual final END resolves the retained root certificate and emits its
literal epilogue. Source-byte accounting supplies the final fetch bound. -/
theorem StructuredCompilerPrefixWithTables.finish_body {jumpTables : List Aeneas.Std.U32} {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals current raw position}
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial before types functions returns locals [] current raw position)
    (entered : current.entered = true)
    (stack : before.reachable = true → Sequence.stackTypes raw = returns)
    (form : current.form = .body) (front : current.front = []) (params : current.params = [])
    (results : current.results = returns)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType)
    (coordinate : before.function.body_start.val + state.pos.val ≤ Usize.max)
    (consumed : position < state.pos.val) (sourceBound : state.pos.val ≤ limits.MAX_MODULE_BYTES.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    ∃ target : U32, CompilerStable initial after ∧ after.frames.val = [] ∧
      StructuredCodeWithTables emit types functions returns locals after.function.code.val jumpTables
        [functionRootLabel returns after.function target] [] current.source 0 target.val returns ∧
      (∃ src count, src.val = slots locals ∧ after.function.code.val[target.val]? = some (.Return src count)) ∧
      after.function.code.val.length = target.val + 1 ∧
      after.function.code.val.length ≤ U32.max := by
  have beforeBound := (Nat.le_of_lt consumed).trans sourceBound
  have fetchBound := invariant.codeBudget.fetch_bound beforeBound
  let target : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
  have positionEq : target.val = before.function.code.val.length := by simp [target]
  obtain ⟨frame, frames, bodyKind, noGuard, height, width, mapBound, branches, body⟩ :=
    invariant.root_relation entered stack target positionEq form front params results
  obtain ⟨codeFits, sourceFits, _, _⟩ := invariant.capacities beforeBound
  have emitCoordinate : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    omega
  have call : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state .Block .Empty = .ok (.Ok (), after) := accepted
  have effect := structured_close_function_body_with_tables ops law before state frame (alloc.vec.Vec.new _) target
    (by simpa using frames) bodyKind noGuard positionEq branches mapBound coordinate codeFits sourceFits emitCoordinate
    types functions returns locals current.source width body
  rw [call, WP.spec_ok] at effect
  have result := effect rfl
  dsimp only at result
  obtain ⟨popped, relation, returnedCode, endpoint⟩ := result
  obtain ⟨count, returned⟩ := returnedCode
  have stable := compiler_end_stable_result ops law before after state kind bt (.Ok ()) accepted
  have growth : after.function.code.val.length ≤ before.function.code.val.length + 3 := by omega
  have bound := (invariant.codeBudget.advance growth consumed).fetch_bound sourceBound
  exact ⟨target, invariant.metadata.trans stable, by simp [popped], relation,
    ⟨frame.height, count, height, returned⟩, endpoint, Nat.le_of_lt bound⟩
end Exec.Code
