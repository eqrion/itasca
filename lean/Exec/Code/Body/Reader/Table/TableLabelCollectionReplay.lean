import Exec.Code.Body.Reader.Table.TableReaderReplay
import Exec.Code.Body.Reader.Table.TableDecodePrefix
import Exec.Code.Body.Reader.Table.LabelCollectionAvailability

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Replay all actual Wasm 2 vector labels with independent scratch and branch
bounds. The remaining final-callback obligation receives the exact decoded
source list, not an arbitrary scratch buffer or an assumed target success. -/
theorem compiler_table_loop_collect_available {A V : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st : code.OpIterState) (out : code.BodyState)
    (data : Slice U8) (env : module.Env) (count : U32) (all : List U32)
    (empty : compiler.table_depths.val = []) (length : all.length = count.val+1)
    (decoded : BrTable.LabelsDecoded data st.pos all out.core.pos)
    (branches : compiler.budget.branches.val+count.val ≤ compiler.budget.limits.max_branch_table_entries.val)
    (capacity : count.val ≤ Usize.max) (reserve : count.val ≤ bound)
    (post : code.BodyState → V → runtime.compiler.FunctionCompiler A → Prop)
    (finish : ∀ (state : code.BodyState) current marked depth ts sourceBefore sourceAfter,
      LabelCollectionPrefix compiler current count.val →
      TableDecodeRead data all out.core.pos count.val state.core current.table_depths.val depth →
      state.core.vals = st.vals → state.core.ctrls = st.ctrls →
      code.mark_unreachable state.core = .ok marked →
      source.on_br_table sourceBefore marked depth ts = .ok (.Ok (),sourceAfter) →
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_br_table current marked depth ts
        ⦃ result => result.1 = .Ok () ∧ post {state with core := marked} sourceAfter result.2 ⦄)
    (reference : code.branch_table_with_loop source st data env before count none 0#u32 =
      .ok (.Ok (),out,after)) :
    code.branch_table_with_loop (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env compiler count none 0#u32 ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        post out after result.2.2 ⦄ := by
  let related := fun index state (_ : V) current =>
    LabelCollectionPrefix compiler current index ∧
      TableDecodePrefix data all out.core.pos index state current.table_depths.val ∧
      state.vals = st.vals ∧ state.ctrls = st.ctrls
  let readRelated := fun index state depth (_ : signature.ResultType) (_ : V) current =>
    LabelCollectionPrefix compiler current index ∧
      TableDecodeRead data all out.core.pos index state current.table_depths.val depth ∧
      state.vals = st.vals ∧ state.ctrls = st.ctrls
  have readMoves : ∀ (index : U32) (state : code.BodyState) sourceBefore current depth ts next,
      index.val ≤ count.val → related index.val state.core sourceBefore current →
      code.read_label_info state data = .ok (.Ok (depth,ts),next) →
      readRelated index.val next.core depth ts sourceBefore current := by
    intro index state sourceBefore current depth ts next bounded held read
    have actual := reader_table_label_wasm2 state data (by simp)
    rw [read,WP.spec_ok] at actual
    obtain ⟨values,controls,_,_⟩ := actual depth ts rfl
    exact ⟨held.1,held.2.1.read (by omega) read,values.trans held.2.2.1,controls.trans held.2.2.2⟩
  have label : ∀ (index : U32) state sourceBefore current depth ts sourceAfter,
      index.val < count.val → readRelated index.val state depth ts sourceBefore current →
      source.on_br_table_label sourceBefore state depth = .ok (.Ok (),sourceAfter) →
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_br_table_label current state depth
        ⦃ result => result.1 = .Ok () ∧ related (index.val+1) state sourceAfter result.2 ⦄ := by
    intro index state sourceBefore current depth ts sourceAfter remaining held _
    obtain ⟨⟨reply,targetAfter⟩,called,accepted,collected⟩ := WP.spec_imp_exists
      (held.1.collect_available ops law bound allocation compiler current state depth index.val count.val
        remaining (by simpa [empty] using branches) (by simpa [empty] using capacity) (by simpa [empty] using reserve))
    dsimp only at accepted collected
    subst reply
    obtain ⟨budget,depths,frame,appended⟩ := compiler_table_label_success ops law current targetAfter state depth called
    have decodedPrefix := held.2.1.collect
    apply WP.exists_imp_spec
    refine ⟨(.Ok (),targetAfter),called,rfl,collected,?_,held.2.2⟩
    simpa only [frame,appended] using decodedPrefix
  obtain ⟨targetAfter,called,retained⟩ := table_loop_reader_accepted_replay source
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) related readRelated post data env count
    readMoves label (fun state sourceBefore current marked depth ts sourceAfter held mark call =>
      finish state current marked depth ts sourceBefore sourceAfter held.1 held.2.1 held.2.2.1 held.2.2.2 mark call)
    0#u32 (by simp) none st out before after compiler
    ⟨LabelCollectionPrefix.initial compiler,by simpa [empty] using TableDecodePrefix.initial st decoded,rfl,rfl⟩ reference
  apply WP.exists_imp_spec
  exact ⟨(.Ok (),out,targetAfter),called,rfl,rfl,retained⟩

end Exec.Code
