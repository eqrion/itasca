import Itasca.Runtime.Compiler.Body.Reader.Local.LocalEffects

/-!
Accepted load readers replace exactly the live i32 address with the specified numeric result type. Decoding the memory argument preserves operands.

Main declarations: `reader_memory_load_stack` and `reader_memory_store_stack`. A direct consumer is `Compiler.Body.Reader.Memory.Instructions`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Accepted load readers replace exactly the live i32 address with the
specified numeric result type. Decoding the memory argument preserves operands. -/
theorem reader_memory_load_stack (st out : code.OpIterState) (data : Slice U8) (env : module.Env)
    (ty : types.ValueType) (natural : U32) (arg : code.MemArg)
    (outer segment : List code.StackType)
    (values : st.vals.val = outer ++ segment) (base : (Control.base st).val = outer.length)
    (monomorphic : Control.polymorphic st = false) (known : ConcreteStack segment)
    (capacity : st.vals.val.length < Usize.max)
    (accepted : code.read_load st data env ty natural = .ok (.Ok arg,out)) :
    ∃ rest, segment = rest ++ [.Val .I32] ∧ out.vals.val = outer ++ rest ++ [.Val ty] ∧
      out.ctrls = st.ctrls ∧ code.check_memory_and_alignment env arg natural = .ok (.Ok ()) := by
  obtain ⟨⟨result,middle⟩,read,sameValues,controls,meaning⟩ := WP.spec_imp_exists (code.read_memarg.spec st data)
  dsimp only at sameValues controls meaning
  cases result with
  | Err error => simp [code.read_load,read,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok argument =>
    obtain ⟨checkResult,check,checked⟩ := WP.spec_imp_exists (code.check_memory_and_alignment.spec env argument natural)
    cases checkResult with
    | Err error => simp [code.read_load,read,check,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
    | Ok unit =>
      cases unit
      obtain ⟨⟨popResult,popped⟩,pop,popControls,_,rest,restValues,popEffect⟩ := WP.spec_imp_exists
        (code.pop_with_type.segment middle outer segment .I32 (by simpa [sameValues] using values)
          (by simpa [Control.base,controls] using base))
      dsimp only at popControls restValues popEffect
      cases popResult with
      | Err error => simp [code.read_load,read,check,pop,core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
      | Ok raw =>
        have poly : Control.polymorphic middle = false := by simpa [Control.polymorphic,controls] using monomorphic
        rw [poly] at popEffect
        have old := typed_pop_exact known popEffect
        have room : popped.vals.val.length < Usize.max := by
          simp only [values,old,List.length_append,List.length_singleton] at capacity
          simp only [restValues,List.length_append]
          omega
        obtain ⟨final,push,finalValues,finalControls,finalPos⟩ := WP.spec_imp_exists (code.push_val.spec popped (.Val ty) room)
        simp [code.read_load,read,check,pop,push,bind_ok,core.result.Result.Insts.CoreOpsTry.branch,
          Result.ok.injEq,Prod.mk.injEq,core.result.Result.Ok.injEq] at accepted
        obtain ⟨rfl,rfl⟩ := accepted
        exact ⟨rest,old,by simpa only [restValues] using finalValues,finalControls.trans (popControls.trans controls),check⟩

/-- Accepted stores remove the scalar value and i32 address without disturbing
the remaining current frame segment. -/
theorem reader_memory_store_stack (st out : code.OpIterState) (data : Slice U8) (env : module.Env)
    (ty : types.ValueType) (natural : U32) (arg : code.MemArg)
    (outer segment : List code.StackType)
    (values : st.vals.val = outer ++ segment) (base : (Control.base st).val = outer.length)
    (monomorphic : Control.polymorphic st = false) (known : ConcreteStack segment)
    (accepted : code.read_store st data env ty natural = .ok (.Ok arg,out)) :
    ∃ rest, segment = rest ++ [.Val .I32,.Val ty] ∧ out.vals.val = outer ++ rest ∧
      out.ctrls = st.ctrls ∧ code.check_memory_and_alignment env arg natural = .ok (.Ok ()) := by
  obtain ⟨⟨result,middle⟩,read,sameValues,controls,meaning⟩ := WP.spec_imp_exists (code.read_memarg.spec st data)
  dsimp only at sameValues controls meaning
  cases result with
  | Err error => simp [code.read_store,read,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok argument =>
    obtain ⟨checkResult,check,checked⟩ := WP.spec_imp_exists (code.check_memory_and_alignment.spec env argument natural)
    cases checkResult with
    | Err error => simp [code.read_store,read,check,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
    | Ok unit =>
      cases unit
      obtain ⟨⟨popResult,popped⟩,pop,popControls,_,remaining,remainingValues,popEffect⟩ := WP.spec_imp_exists
        (code.pop_with_type.segment middle outer segment ty (by simpa [sameValues] using values)
          (by simpa [Control.base,controls] using base))
      dsimp only at popControls remainingValues popEffect
      cases popResult with
      | Err error => simp [code.read_store,read,check,pop,core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
      | Ok raw =>
        have poly : Control.polymorphic middle = false := by simpa [Control.polymorphic,controls] using monomorphic
        rw [poly] at popEffect
        have old := typed_pop_exact known popEffect
        have remainingKnown : ConcreteStack remaining := (concrete_stack_append.mp (old ▸ known)).1
        obtain ⟨⟨addressResult,final⟩,addressPop,addressControls,_,rest,restValues,addressEffect⟩ := WP.spec_imp_exists
          (code.pop_with_type.segment popped outer remaining .I32 remainingValues
            (by simpa [Control.base,popControls,controls] using base))
        dsimp only at addressControls restValues addressEffect
        cases addressResult with
        | Err error => simp [code.read_store,read,check,pop,addressPop,core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
        | Ok address =>
          have addressPoly : Control.polymorphic popped = false := by simpa [Control.polymorphic,popControls] using poly
          rw [addressPoly] at addressEffect
          have remainingShape := typed_pop_exact remainingKnown addressEffect
          simp [code.read_store,read,check,pop,addressPop,bind_ok,core.result.Result.Insts.CoreOpsTry.branch,
            Result.ok.injEq,Prod.mk.injEq,core.result.Result.Ok.injEq] at accepted
          obtain ⟨rfl,rfl⟩ := accepted
          exact ⟨rest,by simpa only [remainingShape,List.append_assoc,List.cons_append,List.nil_append] using old,
            restValues,addressControls.trans (popControls.trans controls),check⟩
end Itasca.Runtime.Compiler
