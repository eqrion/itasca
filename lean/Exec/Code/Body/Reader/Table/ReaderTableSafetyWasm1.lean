import Exec.Code.Local.Relations.Table.BranchTableCallbackSafety
import Exec.Code.Local.Source.SourceBudget
import Itasca.Visitor.ReachedTableLabels
import Itasca.Wasm2.Control.Total
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

private def TableReaderInvariant {A} (base : runtime.compiler.FunctionCompiler A)
    (controls : alloc.vec.Vec code.Ctrl) (data : Slice U8) (_ : Nat)
    (state : code.OpIterState) (current : runtime.compiler.FunctionCompiler A) : Prop :=
  Control.Shape state ∧ state.ctrls = controls ∧ state.pos.val ≤ data.length ∧
  ∃ budget depths, current = {base with budget,table_depths := depths} ∧
    (∀ depth ∈ depths.val, depth.val < base.frames.val.length) ∧
    base.function.code.val.length + 2*depths.val.length + 3 ≤ 3*state.pos.val

private theorem table_reader_label_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (base : runtime.compiler.FunctionCompiler A)
    (controls : alloc.vec.Vec code.Ctrl) (data : Slice U8)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (frames : base.frames.val.length = controls.val.length)
    (state : code.OpIterState) (current : runtime.compiler.FunctionCompiler A) (index : Nat)
    (held : TableReaderInvariant base controls data index state current)
    (depth : U32) (target : code.Ctrl) (next : code.OpIterState)
    (read : code.read_label state data = .ok (.Ok (depth,target),next)) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_br_table_label
      current next depth ⦃ out => out.1 = .Ok () →
        TableReaderInvariant base controls data (index+1) next out.2 ⦄ := by
  obtain ⟨shape,ctrls,pos,budget,buffer,rfl,depths,room⟩ := held
  have effects := code.read_label.spec state data
  rw [read,WP.spec_ok] at effects
  obtain ⟨vals,ctrlsEq,decoded,depthBound,targetEq⟩ := effects
  have span := decoded.span
  dsimp only at span
  have shapeNext : Control.Shape next := by
    exact shape.replace_operands ctrlsEq (by rw [vals]; exact shape.base_le)
  have maximum : 3*limits.MAX_MODULE_BYTES.val < Usize.max := by
    simp only [limits.MAX_MODULE_BYTES]
    scalar_tac
  obtain ⟨⟨status,after⟩,called,_⟩ := WP.spec_imp_exists
    (compiler_table_label_total ops law {base with budget,table_depths := buffer} next depth (by dsimp only; omega))
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor]
  rw [called,WP.spec_ok]
  intro success
  change status = .Ok () at success
  subst status
  obtain ⟨freshBudget,freshBuffer,rfl,appended⟩ := compiler_table_label_success ops law _ after next depth called
  refine ⟨shapeNext,ctrlsEq.trans ctrls,span.2.2,freshBudget,freshBuffer,rfl,?_,?_⟩
  · intro d member
    rw [appended] at member
    rcases List.mem_append.mp member with old | added
    · exact depths d old
    · simp only [List.mem_singleton] at added
      subst d
      simpa only [frames,←ctrls] using depthBound
  · simp only [appended,List.length_append,List.length_singleton]
    omega

private theorem table_reader_labels_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (base : runtime.compiler.FunctionCompiler A)
    (controls : alloc.vec.Vec code.Ctrl) (data : Slice U8)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (frames : base.frames.val.length = controls.val.length)
    (state : code.OpIterState) (current : runtime.compiler.FunctionCompiler A) (count : U32)
    (held : TableReaderInvariant base controls data 0 state current) :
    code.read_table_labels (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      state data count current ⦃ out => ∀ common, out.1 = .Ok common →
      TableReaderInvariant base controls data count.val out.2.1 out.2.2 ⦄ := by
  unfold code.read_table_labels
  apply code.read_table_labels_loop.total_on _ data count (TableReaderInvariant base controls data)
  · intro st v index depth target next inside held read
    exact table_reader_label_total ops law base controls data sourceBound frames st v index held depth target next read
  · scalar_tac
  · exact held

private theorem compiler_read_br_table_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : code.OpIterState) (data : Slice U8)
    (shape : Control.Shape state) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (frames : compiler.frames.val.length = state.ctrls.val.length)
    (empty : compiler.table_depths.val = [])
    (room : compiler.function.code.val.length+3 ≤ 3*state.pos.val) :
    code.read_br_table (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) state data compiler ⦃ out =>
      ∀ fallback bt, out.1 = .Ok (fallback,bt) →
      ∃ budget depths, out.2.2 = {compiler with budget,table_depths := depths} ∧
        (∀ d ∈ depths.val, d.val < compiler.frames.val.length) ∧
        fallback.val < compiler.frames.val.length ∧
        compiler.function.code.val.length+1+2*(depths.val.length+1) ≤ Usize.max ⦄ := by
  unfold code.read_br_table
  obtain ⟨result,read,decoded⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data state.pos)
  rw [read]
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨count,next⟩ := pair
    have span := decoded.span
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry]
    have held : TableReaderInvariant compiler state.ctrls data 0 {state with pos := next} compiler := by
      refine ⟨⟨shape.ordered,shape.bounded⟩,rfl,span.2.2,compiler.budget,compiler.table_depths,rfl,?_,?_⟩
      · simp [empty]
      · simp only [empty,List.length_nil]; omega
    obtain ⟨⟨status,collectedState,collected⟩,collect,post⟩ := WP.spec_imp_exists
      (table_reader_labels_total ops law compiler state.ctrls data sourceBound frames
        {state with pos := next} compiler count held)
    rw [collect]
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok expected =>
      obtain ⟨freshShape,controls,cursor,budget,buffer,rfl,valid,budgetBound⟩ := post expected rfl
      dsimp only at freshShape controls cursor valid budgetBound
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry]
      obtain ⟨⟨label,defaultState⟩,labelCall,vals,ctrls,labelPost⟩ := WP.spec_imp_exists (code.read_label.spec collectedState data)
      rw [labelCall]
      cases label with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        obtain ⟨fallback,target⟩ := pair
        obtain ⟨defaultDecoded,defaultBound,targetEq⟩ := labelPost
        have defaultShape : Control.Shape defaultState :=
          freshShape.replace_operands ctrls (by rw [vals]; exact freshShape.base_le)
        have bound : fallback.val < compiler.frames.val.length := by
          simpa only [frames,controls] using defaultBound
        have maximum : 3*limits.MAX_MODULE_BYTES.val < Usize.max := by
          simp only [limits.MAX_MODULE_BYTES]; scalar_tac
        have room : compiler.function.code.val.length+1+2*(buffer.val.length+1) ≤ Usize.max := by omega
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry]
        obtain ⟨bt,btCall,_⟩ := WP.spec_imp_exists (code.branch_target_bt.spec target)
        rw [btCall]
        simp only [bind_ok]
        obtain ⟨merged,mergeCall,_⟩ := WP.spec_imp_exists (code.merge_target.spec expected bt)
        rw [mergeCall]
        cases merged with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok resultType =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry]
          obtain ⟨⟨popResult,popped⟩,popCall,popShape,rest⟩ := WP.spec_imp_exists
            (code.pop_with_type.total defaultState .I32 defaultShape)
          rw [popCall]
          cases popResult with
          | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok value =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry]
            obtain ⟨types,typesCall,_⟩ := WP.spec_imp_exists (code.block_results.spec resultType)
            rw [typesCall]
            simp only [bind_ok]
            obtain ⟨⟨argsResult,argsState⟩,argsCall,argsShape,rest⟩ := WP.spec_imp_exists
              (code.pop_types.total popped (alloc.vec.Vec.deref types) popShape)
            rw [argsCall]
            cases argsResult with
            | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok unit =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry]
              obtain ⟨marked,markCall,_⟩ := WP.spec_imp_exists (code.mark_unreachable_total argsState argsShape)
              rw [markCall]
              simp only [bind_ok,WP.spec_ok,core.result.Result.Ok.injEq,Prod.mk.injEq]
              intro fallback' bt' equal
              obtain ⟨rfl,rfl⟩ := equal
              exact ⟨budget,buffer,rfl,valid,bound,room⟩

/-- The actual Wasm 1 branch-table reader and compiler callbacks return from
raw reached bounds, even when the table count or any subsequent byte is invalid. -/
theorem compiler_table_reader_wasm1_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (shape : Control.Shape state) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (frames : compiler.frames.val.length = state.ctrls.val.length)
    (empty : compiler.table_depths.val = [])
    (room : compiler.function.code.val.length+3 ≤ 3*state.pos.val)
    (aligned : SourceAligned compiler)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (tables : compiler.function.jump_tables.val.length ≤ compiler.function.code.val.length)
    (coordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      state data env ctx code.OP_BR_TABLE compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_br_table.dispatch]
  obtain ⟨⟨status,final,collected⟩,read,post⟩ := WP.spec_imp_exists
    (compiler_read_br_table_total ops law compiler state data shape sourceBound frames empty room)
  rw [read]
  simp only [bind_ok]
  try dsimp only
  cases status with
  | Err error => simp [CoreVisitor.run,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨fallback,bt⟩ := pair
    obtain ⟨budget,buffer,rfl,valid,bound,capacity⟩ := post fallback bt rfl
    have callback := compiler_br_table_total ops law {compiler with budget,table_depths := buffer}
      final fallback (Control.resultView bt) aligned valid bound fixups capacity tables coordinate
    obtain ⟨⟨reply,after⟩,called,effect⟩ := WP.spec_imp_exists callback
    cases reply with
    | Err error => simp [CoreVisitor.run,runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
        called,code.visit,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok value =>
      cases value
      simpa [CoreVisitor.run,runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
        called,code.visit,core.result.Result.Insts.CoreOpsTry.branch] using effect rfl
end Exec.Code
