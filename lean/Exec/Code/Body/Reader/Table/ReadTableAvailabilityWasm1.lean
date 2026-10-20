import Exec.Code.Body.Reader.Table.TableReaderTailWasm1
import Exec.Code.Body.Reader.Table.ExactLabelCollectionAvailabilityWasm1

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- The actual Wasm 1 collecting reader accepts every independently accepted
source read with bounded label allocations. Its pure fallback/operand tail is
reused exactly, and its target scratch buffer is the independent source list. -/
theorem compiler_read_br_table_available_wasm1 {A V : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (fallback : U32) (common : code.BlockType) (depths : List U32)
    (encoded : BrTable.Decoded data st.pos depths fallback out.pos)
    (empty : compiler.table_depths.val = [])
    (branches : compiler.budget.branches.val+depths.length ≤ compiler.budget.limits.max_branch_table_entries.val)
    (capacity : depths.length ≤ Usize.max) (reserve : depths.length ≤ bound)
    (reference : code.read_br_table source st data before = .ok (.Ok (fallback,common),out,after)) :
    code.read_br_table (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data compiler
      ⦃ result => result.1 = .Ok (fallback,common) ∧ result.2.1 = out ∧
        LabelCollectionPrefix compiler result.2.2 depths.length ∧ result.2.2.table_depths.val = depths ⦄ := by
  obtain ⟨count,first,last,countDecoded,length,labelsDecoded,defaultDecoded⟩ := encoded
  have readCount := reader.read_u32_leb.complete data st.pos count first countDecoded
  rw [table_reader_factored_wasm1] at reference ⊢
  unfold tableReaderFactoredWasm1 at reference ⊢
  rw [readCount] at reference ⊢
  simp only [bind_ok] at reference ⊢
  obtain ⟨⟨reply,labelState,middle⟩,labelsCalled,rest⟩ := ResultFacts.bind_ok_inv _ _ _ reference
  cases reply with
  | Err error => simp at rest
  | Ok expect =>
    simp only [Std.uncurry,bind_ok] at rest
    obtain ⟨⟨reply,final⟩,tailCalled,returned⟩ := ResultFacts.bind_ok_inv _ _ _ rest
    simp only [Std.uncurry,Result.ok.injEq,Prod.mk.injEq] at returned
    obtain ⟨accepted,same,visitor⟩ := returned
    subst reply final middle
    obtain ⟨⟨reply,final,targetCollected⟩,targetCalled,accepted,same,collected,exactBuffer⟩ := WP.spec_imp_exists
      (compiler_exact_table_labels_available_wasm1 ops law bound allocation source before after compiler
        {st with pos := first} labelState data count expect depths last empty length labelsDecoded
        (by simpa only [← length] using branches) (by omega) (by omega)
        (by simpa only [code.read_table_labels] using labelsCalled))
    dsimp only at accepted same collected exactBuffer
    subst reply final
    apply WP.exists_imp_spec
    refine ⟨(.Ok (fallback,common),out,targetCollected),?_,rfl,rfl,?_,exactBuffer⟩
    · simp only [code.read_table_labels,targetCalled,tailCalled,bind_ok,Std.uncurry]
    · simpa only [← length] using collected

end Exec.Code
