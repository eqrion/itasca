import Itasca.Runtime.Compiler.Body.Reader.Control.BranchTableSource
import Itasca.Wasm2.Control.BrTableSound
import Itasca.Visitor.Accepts

/-!
Canonical accepted target checks retain a suffix obligation for every label, independently of the compiler visitor's implementation.

Main declarations: `reader_table_targets_wasm2`. A direct consumer is `Compiler.Body.Reader.Control.BranchTableInputsWasm2`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- Canonical accepted target checks retain a suffix obligation for every
label, independently of the compiler visitor's implementation. -/
theorem reader_table_targets_wasm2 {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (st final : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (cs : List code.Ctrl) (c : code.Ctrl)
    (controls : st.core.ctrls.val=cs++[c]) (shape : Control.Shape st.core)
    (accepted : code.branch_table_with visitor st data env .Wasm2 before=.ok (.Ok (),final,after)) :
    ∃ (count : U32) (first : Usize) (selector : code.StackType) (popped : code.OpIterState)
      (all : List U32) (arity : Usize),
      Leb128.Decoded data st.core.pos count first ∧
      code.pop_with_type {st.core with pos := first} .I32=.ok (.Ok selector,popped) ∧
      popped.ctrls=st.core.ctrls ∧ popped.pos=first ∧
      all.length=count.val+1 ∧ BrTable.LabelsDecoded data first all final.core.pos ∧
      Wasm2.TableTargets env ⟨popped⟩ all (some arity) := by
  obtain ⟨unit,erased⟩ := code.branch_table_with.accepted_transfer visitor
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_accepts st data env before () final after _ accepted
  cases unit
  unfold code.branch_table_with at erased
  obtain ⟨read,readCall,readSpec⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  rw [readCall] at erased
  cases read with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at erased
  | Ok pair =>
    obtain ⟨count,first⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,uncurry_apply_pair] at erased
    obtain ⟨⟨reply,popped⟩,popCall,rest⟩ := bind_ok_inv _ _ _ erased
    have popSpec := code.pop_with_type.total {st.core with pos := first} .I32
      (show Control.Shape {st.core with pos := first} from ⟨shape.ordered,shape.bounded⟩)
    rw [popCall,WP.spec_ok] at popSpec
    dsimp only at popSpec
    cases reply with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok selector =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,uncurry_apply_pair] at rest
      have loopCall : Wasm2.branchTableLoop popped data env .Wasm2 count none .Empty 0#u32=.ok (.Ok (),final) := by
        simp only [Wasm2.branchTableLoop,rest,bind_ok,uncurry_apply_pair]
      have checked := Wasm2.branchTableLoop.spec ⟨popped⟩ data env .Wasm2 count cs c
        (by simpa only [popSpec.2.1] using controls) popSpec.1
      rw [loopCall,WP.spec_ok] at checked
      obtain ⟨all,arity,length,decoded,targets,_,_,_,_⟩ := checked rfl
      exact ⟨count,first,selector,popped,all,arity,readSpec,popCall,popSpec.2.1,popSpec.2.2.1,
        length,by simpa only [popSpec.2.2.1] using decoded,targets⟩
end Itasca.Runtime.Compiler
