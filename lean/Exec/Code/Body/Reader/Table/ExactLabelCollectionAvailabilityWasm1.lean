import Exec.Code.Body.Reader.Table.LabelCollectionAvailability
import Exec.Code.Body.Reader.Table.TableDecodePrefix

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- All actual Wasm 1 vector labels accept and collect exactly their
independently decoded values, with source-count branch and reserve bounds. -/
theorem compiler_exact_table_labels_available_wasm1 {A V : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (count : U32) (common : Option code.BlockType) (depths : List U32) (finish : Usize)
    (empty : compiler.table_depths.val = []) (length : depths.length = count.val)
    (decoded : BrTable.LabelsDecoded data st.pos depths finish)
    (branches : compiler.budget.branches.val+count.val ≤ compiler.budget.limits.max_branch_table_entries.val)
    (capacity : count.val ≤ Usize.max) (reserve : count.val ≤ bound)
    (reference : code.read_table_labels_loop source st data count before none 0#u32 = .ok (.Ok common,out,after)) :
    code.read_table_labels_loop (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data count compiler none 0#u32 ⦃ result => result.1 = .Ok common ∧ result.2.1 = out ∧
        LabelCollectionPrefix compiler result.2.2 count.val ∧ result.2.2.table_depths.val = depths ⦄ := by
  let related := fun index state (_ : V) current =>
    LabelCollectionPrefix compiler current index ∧ TableDecodePrefix data depths finish index state current.table_depths.val
  have replay := code.read_table_labels_loop.accepted_replay_on source
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data count related
    (by
      intro state sourceBefore current index depth label next middle remaining held read _
      have actual := code.read_label.spec state data
      rw [read,WP.spec_ok] at actual
      have bytes := actual.2.2.1
      have readPrefix := held.2.read_decoded (by omega) bytes
      obtain ⟨⟨reply,targetAfter⟩,called,accepted,collected⟩ := WP.spec_imp_exists
        (held.1.collect_available ops law bound allocation compiler current next depth index count.val remaining
          (by simpa [empty] using branches) (by simpa [empty] using capacity) (by simpa [empty] using reserve))
      dsimp only at accepted collected
      subst reply
      obtain ⟨budget,buffer,frame,appended⟩ := compiler_table_label_success ops law current targetAfter next depth called
      apply WP.exists_imp_spec
      refine ⟨(.Ok (),targetAfter),called,rfl,collected,?_⟩
      simpa only [frame,appended] using readPrefix.collect)
    st out before after compiler none common 0#u32 (by simp)
    ⟨LabelCollectionPrefix.initial compiler,by simpa [empty] using TableDecodePrefix.initial st decoded⟩ reference
  apply WP.spec_mono replay
  intro result held
  exact ⟨held.1,held.2.1,held.2.2.1,(held.2.2.2.complete length).1⟩

end Exec.Code
