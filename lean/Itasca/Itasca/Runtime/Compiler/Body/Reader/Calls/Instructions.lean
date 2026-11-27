import Itasca.Body.Trace.BytesDispatch
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalEffects
import Itasca.Body.Trace.ControlRecords
import Itasca.Body.Control.BranchComplete
import Itasca.Runtime.Compiler.Body.Reader.StackValues

open WebAssembly

/-!
Proofs for Runtime / Compiler / Body / Reader / Calls.

This module collects Instructions, CallEffects.
Each section documents its contracts and consumers.
-/

/-! ## Instructions -/

section

/-!
Accepted direct and indirect call reader steps and their decoded instruction facts, used by call safety, lowering and replay.
-/

/-! ## Reader Body Call -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body Itasca.Visitor.Trace

theorem reader_call {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x10#u8)
    (accepted : code.step_body visitor st data env ctx index 0x10#u8 before =
      .ok (.Ok (), out, after)) :
    ∃ idx values, visitor.on_call before out.core idx = .ok (.Ok (), after) ∧
      code.call_info st data env = .ok (.Ok idx, out) ∧
      Body.ReaderPost p out.core (.CALL (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values := by
  rw [CallbackTrace.dispatch_call] at accepted
  obtain ⟨idx, read, callback⟩ := Body.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  have erased : code.call st data env false = .ok (.Ok (), out) := by
    simp [code.call, read, core.result.Result.Insts.CoreOpsTry.branch]
  have effect := p.call_reader byte
  rw [erased, WP.spec_ok] at effect
  obtain ⟨sourceIndex, values, decoded, post⟩ := effect rfl
  have info := code.call_info.bytes st data env p.opened.shape.core
  rw [read, WP.spec_ok] at info
  obtain ⟨rfl, _⟩ := Binary.Leb128.Decoded.deterministic data st.core.pos idx sourceIndex
    out.core.pos out.core.pos (info idx rfl) decoded
  exact ⟨idx, values, callback, read, post⟩

end Itasca.Compiler

end

/-! ## Reader Indirect Call -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body Itasca.Visitor.Trace

/-- Accepted indirect calls retain both canonical source indices and advance
exactly the supplied source zipper, including polymorphic operand segments. -/
theorem reader_indirect_call {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x11#u8)
    (accepted : code.step_body visitor st data env ctx index 0x11#u8 before = .ok (.Ok (),out,after)) :
    ∃ idx table values, visitor.on_call_indirect before out.core idx table = .ok (.Ok (),after) ∧
      code.call_indirect_info st data env = .ok (.Ok (idx,table),out) ∧
      Body.ReaderPost p out.core (.CALL_INDIRECT (.mk_uN table.val) (.mk_uN idx.val))
        p.current.ctrl.polymorphic_base values := by
  rw [CallbackTrace.dispatch_call_indirect] at accepted
  obtain ⟨⟨idx, table⟩, read, callback⟩ := Body.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  have erased : code.call st data env true = .ok (.Ok (), out) := by
    simp [code.call, read, core.result.Result.Insts.CoreOpsTry.branch]
  have effect := p.call_indirect_reader byte
  rw [erased, WP.spec_ok] at effect
  obtain ⟨sourceIndex, sourceTable, middle, values, decoded, decodedTable, post⟩ := effect rfl
  have info := code.call_indirect_info.bytes st data env p.opened.shape.core
  rw [read, WP.spec_ok] at info
  obtain ⟨middle', indexBytes, tableBytes⟩ := info idx table rfl
  obtain ⟨rfl, rfl⟩ := Binary.Leb128.Decoded.deterministic data st.core.pos idx sourceIndex middle' middle indexBytes decoded
  obtain ⟨rfl, _⟩ := Binary.Leb128.Decoded.deterministic data middle' table sourceTable out.core.pos out.core.pos tableBytes decodedTable
  exact ⟨idx, table, values, callback, read, post⟩

end Itasca.Compiler

end

end

/-! ## CallEffects -/

section

/-!
Actual direct-call metadata lookup and parameter/result stack transfer.

Main declarations: `reader_call_info_effect` and `call_full_stack_types`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual direct-call metadata lookup and parameter/result stack transfer. -/
theorem reader_call_info_effect (st out : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (index : U32) (outer segment : List code.StackType)
    (values : st.core.vals.val = outer ++ segment) (base : (Body.Control.base st.core).val = outer.length)
    (accepted : code.call_info st data env = .ok (.Ok index, out)) :
    ∃ (ft : wasm_types.FuncType) (rest : List code.StackType),
      env.func_types.val[index.val]? = some ft ∧
      out.core.vals.val = outer ++ (rest ++ ft.results.val.map code.StackType.Val) ∧
      (∀ ts, Body.Stack.Realizes (Body.Control.polymorphic st.core) rest ts →
        Body.Stack.Realizes (Body.Control.polymorphic st.core) segment (ts ++ ft.params.val.map Translation.valueType)) := by
  obtain ⟨⟨result, state⟩, read, sameValues, controls, post⟩ := WP.spec_imp_exists (code.take_index.spec st.core data)
  dsimp only at sameValues controls post
  cases result with
  | Err error => simp [code.call_info, read, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok idx =>
    by_cases bound : idx.val < env.func_types.val.length
    · have indexBound : (UScalar.cast .Usize idx).val < env.func_types.val.length := by simpa using bound
      obtain ⟨ft, indexed, lookup⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.index_usize_spec env.func_types (UScalar.cast .Usize idx) indexBound)
      obtain ⟨⟨reply, after⟩, applied, effect⟩ := WP.spec_imp_exists
        (code.apply_func_type.realizes state ft outer segment (by simpa [sameValues] using values)
          (by simpa [Body.Control.base, controls] using base))
      cases reply with
      | Err error => simp [code.call_info, read, lift, Nat.not_le_of_gt bound, indexed, applied,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
      | Ok unit =>
        cases unit
        obtain ⟨_, _, _, _, rest, afterValues, _, transfer⟩ := effect rfl
        dsimp only at afterValues transfer
        simp [code.call_info, read, lift, Nat.not_le_of_gt bound, indexed, applied,
          core.result.Result.Insts.CoreOpsTry.branch] at accepted
        obtain ⟨rfl, rfl⟩ := accepted
        refine ⟨ft, rest, ?_, afterValues, ?_⟩
        · simpa [List.getElem?_eq_getElem bound] using congrArg some lookup.symm
        · simpa [Body.Control.polymorphic, controls] using transfer
    · simp [code.call_info, read, lift, Nat.le_of_not_gt bound,
        core.result.Result.Insts.CoreOpsTry.branch] at accepted

/-- Live calls determine complete concrete operand stacks from their exact
parameter/result transfer, without assuming a compiler stack effect. -/
theorem call_full_stack_types {before after outer segment rest : List code.StackType}
    (params results : List wasm_types.ValueType)
    (known : ConcreteStack before) (old : before = outer ++ segment)
    (new : after = outer ++ (rest ++ results.map code.StackType.Val))
    (transfer : ∀ ts, Body.Stack.Realizes false rest ts →
      Body.Stack.Realizes false segment (ts ++ params.map Translation.valueType)) :
    ∃ front : List wasm_types.ValueType,
      Body.Stack.stackTypes before = front.map Translation.valueType ++ params.map Translation.valueType ∧
      after = (front ++ results).map code.StackType.Val := by
  have both := concrete_stack_append.mp (old ▸ known)
  have restKnown := concrete_stack_transfer both.2 transfer
  obtain ⟨outerTypes, outerConcrete⟩ := (concrete_stack_iff outer).mp both.1
  obtain ⟨restTypes, restConcrete⟩ := (concrete_stack_iff rest).mp restKnown
  have segmentTypes := realized_concrete_types both.2 (transfer _ (Body.Stack.realizes_default false rest))
  refine ⟨outerTypes ++ restTypes, ?_, ?_⟩
  · have whole := congrArg (Body.Stack.stackTypes outer ++ ·) segmentTypes.symm
    simpa [old, outerConcrete, restConcrete, Body.Stack.stackTypes, List.map_map,
      Function.comp_def, List.append_assoc] using whole
  · simp [new, outerConcrete, restConcrete, List.append_assoc]

end Itasca.Compiler

end
