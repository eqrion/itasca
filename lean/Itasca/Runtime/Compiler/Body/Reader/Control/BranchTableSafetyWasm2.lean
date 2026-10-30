import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableCallbackSafety
import Itasca.Wasm2.Visitor.ReachedTableLoop
import Itasca.Wasm2.Visitor.Total

/-!
Normal return while collecting and reading br_table labels.

Main declarations: `TableCollecting`. A direct consumer is `Compiler.Body.Reader.Control.BranchTableDecodePrefix`.
-/

attribute [local step] Itasca.code.check_suffix.spec
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2.Visitor
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem reader_table_label_wasm2 (st : code.BodyState) (data : Slice U8)
    (aligned : st.blocks.val.length = st.core.ctrls.val.length) :
    code.read_label_info st data ⦃ out => ∀ depth types, out.1 = .Ok (depth,types) →
      out.2.core.vals = st.core.vals ∧ out.2.core.ctrls = st.core.ctrls ∧
      Leb128.Decoded data st.core.pos depth out.2.core.pos ∧ depth.val < st.core.ctrls.val.length ⦄ := by
  unfold code.read_label_info
  step with reader.read_u32_leb.spec data st.core.pos as ⟨result,decoded⟩
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨depth,next⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry]
    step with code.label.spec {core := {st.core with pos := next}} depth aligned as ⟨result,looked⟩
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok types =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,WP.spec_ok]
      intro actual view equal
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (core.result.Result.Ok.inj equal)
      refine ⟨trivial,trivial,decoded,?_⟩
      by_contra outside
      simp [Wasm2.labelAt, show ¬depth.val < st.core.ctrls.val.length from outside] at looked

structure TableCollecting {A} (before current : runtime.compiler.FunctionCompiler A)
    (state : code.BodyState) : Prop where
  unchanged : ∃ budget buffer, current = {before with budget,table_depths := buffer}
  targets : ∀depth∈current.table_depths.val, depth.val < before.frames.val.length
  room : before.function.code.val.length + 2*current.table_depths.val.length + 3 ≤ 3*state.core.pos.val
  position : state.core.pos.val ≤ Itasca.limits.MAX_MODULE_BYTES.val
  frames : before.frames.val.length = state.core.ctrls.val.length
  shape : Control.Shape state.core

private theorem table_check_total (st : code.BodyState) (env : metadata.Env)
    (types : signature.ResultType) (arity : Option Usize) (shape : Control.Shape st.core) :
    tableCheck st env types arity ⦃ _ => True ⦄ := by
  unfold tableCheck
  step with signature.ResultType.len.spec types env
  split
  · simp
  · cases arity <;> step*

theorem TableCollecting.read {A} {before current : runtime.compiler.FunctionCompiler A}
    {state next : code.BodyState} {data : Slice U8} {depth : U32} {types}
    (held : TableCollecting before current state) (bounded : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (read : code.read_label_info state data = .ok (.Ok (depth,types),next)) :
    TableCollecting before current next ∧ depth.val < before.frames.val.length ∧
      before.function.code.val.length + 2*current.table_depths.val.length + 5 ≤ 3*next.core.pos.val := by
  have spec := reader_table_label_wasm2 state data (by simp)
  rw [read,WP.spec_ok] at spec
  obtain ⟨values,controls,decoded,depthBound⟩ := spec depth types rfl
  dsimp only at values controls decoded depthBound
  obtain ⟨progress,endBound⟩ := decoded.span
  have room := held.room
  refine ⟨⟨held.unchanged,held.targets,by omega,by omega,?_,?_⟩,?_,by omega⟩
  · simpa [controls] using held.frames
  · exact ⟨by simpa [controls] using held.shape.ordered,by simpa [controls,values] using held.shape.bounded⟩
  · simpa [held.frames] using depthBound

theorem TableCollecting.label {A} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {before current : runtime.compiler.FunctionCompiler A} {state : code.BodyState} {depth : U32}
    (held : TableCollecting before current state) (depthBound : depth.val < before.frames.val.length)
    (extra : before.function.code.val.length + 2*current.table_depths.val.length + 5 ≤ 3*state.core.pos.val) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label ops current state.core depth
      ⦃ out => out.1 = .Ok () → TableCollecting before out.2 state ⦄ := by
  have words : 2^32-1 ≤ Usize.max := by scalar_tac
  have position := held.position
  norm_num [limits.MAX_MODULE_BYTES] at position
  obtain ⟨⟨status,after⟩,called,_⟩ := WP.spec_imp_exists
    (compiler_table_label_total ops law current state.core depth (by omega))
  rw [called,WP.spec_ok]
  intro accepted
  dsimp only at accepted ⊢
  subst status
  obtain ⟨allocation,buffer,rfl,bufferEq⟩ := compiler_table_label_success ops law current after state.core depth called
  obtain ⟨oldBudget,oldBuffer,currentEq⟩ := held.unchanged
  refine ⟨?_,?_,?_,held.position,held.frames,held.shape⟩
  · exact ⟨allocation,buffer,by simp [currentEq]⟩
  · intro value member
    rw [bufferEq] at member
    rcases List.mem_append.mp member with member | member
    · exact held.targets value member
    · simpa using (List.mem_singleton.mp member ▸ depthBound)
  · simp only [bufferEq,List.length_append,List.length_singleton]
    omega

theorem compiler_table_rest_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current : runtime.compiler.FunctionCompiler A)
    (state : code.BodyState) (env : metadata.Env) (count index depth : U32)
    (types : signature.ResultType) (arity : Option Usize) (first : signature.ResultType)
    (held : TableCollecting before current state) (bound : index.val ≤ count.val)
    (depthBound : depth.val < before.frames.val.length)
    (aligned : SourceAligned before) (fixups : FixupBudget before.frames.val before.function.code.val.length)
    (tables : before.function.jump_tables.val.length ≤ before.function.code.val.length)
    (coordinate : before.function.body_start.val + before.next_source.val ≤ Usize.max) :
    tableRest (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) state env count index depth types arity
      first current ⦃ result => match result with
        | .done out => out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val
        | .cont next => next.2.2.2.2.val ≤ count.val ∧ index.val < next.2.2.2.2.val ∧
          TableCollecting before next.2.1 ⟨next.1⟩ ⦄ := by
  unfold tableRest
  step with table_check_total state env types arity held.shape as ⟨status,_⟩
  cases status with
  | Err error => simp
  | Ok nextArity =>
    simp only
    by_cases last : index = count
    · simp only [last,↓reduceIte]
      step with code.mark_unreachable_total state.core held.shape as ⟨marked,_⟩
      have room := held.room
      have position := held.position
      have words : 2^32-1 ≤ Usize.max := by scalar_tac
      norm_num [limits.MAX_MODULE_BYTES] at position
      obtain ⟨allocation,buffer,currentEq⟩ := held.unchanged
      step with compiler_br_table_total ops law current marked depth types
        (by simpa [SourceAligned,currentEq] using aligned) (by simpa [currentEq] using held.targets)
        (by simpa [currentEq] using depthBound) (by simpa [currentEq] using fixups)
        (by simp only [currentEq] at room ⊢; omega)
        (by simpa [currentEq] using tables) (by simpa [currentEq] using coordinate) as ⟨reply,after,observed⟩
      cases reply <;> simp_all [code.visit]
    · simp only [last,↓reduceIte]
      step with UScalar.add_spec (x := index) (y := 1#u32) (by
        have ne : index.val ≠ count.val := fun h => last (UScalar.eq_of_val_eq h)
        scalar_tac) as ⟨next,advance⟩
      refine ⟨by scalar_tac,by scalar_tac,held⟩

theorem compiler_table_body_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current : runtime.compiler.FunctionCompiler A)
    (state : code.BodyState) (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (count index : U32) (arity : Option Usize) (first : signature.ResultType)
    (held : TableCollecting before current state)
    (bound : index.val ≤ count.val) (bounded : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (aligned : SourceAligned before) (fixups : FixupBudget before.frames.val before.function.code.val.length)
    (tables : before.function.jump_tables.val.length ≤ before.function.code.val.length)
    (coordinate : before.function.body_start.val + before.next_source.val ≤ Usize.max) :
    tableBody (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env profile count state current
      arity first index ⦃ result => match result with
        | .done out => out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val
        | .cont next => next.2.2.2.2.val ≤ count.val ∧ index.val < next.2.2.2.2.val ∧
          TableCollecting before next.2.1 ⟨next.1⟩ ⦄ := by
  unfold tableBody
  obtain ⟨⟨status,next⟩,read,_⟩ := WP.spec_imp_exists (reader_table_label_wasm2 state data (by simp))
  rw [read]
  cases status with
  | Err error => simp
  | Ok pair =>
    obtain ⟨depth,types⟩ := pair
    obtain ⟨fresh,target,extra⟩ := held.read bounded read
    simp only [bind_ok,Std.uncurry]
    obtain ⟨check,checked,_⟩ := WP.spec_imp_exists (code.check_table_target.spec profile env
      (if index = 0#u32 then types else first) types)
    rw [checked]
    cases check with
    | Err error => simp
    | Ok _ =>
    simp only [bind_ok]
    by_cases last : index = count
    · simp only [bne_iff_ne,last,ne_eq,not_true_eq_false,Bool.false_eq_true,↓reduceIte]
      simpa only [last] using compiler_table_rest_total ops law before current next env count index depth types arity _
        fresh bound target aligned fixups tables coordinate
    · simp only [bne_iff_ne,last,ne_eq,not_false_eq_true,↓reduceIte]
      obtain ⟨⟨reply,after⟩,called,kept⟩ := WP.spec_imp_exists (fresh.label ops law target extra)
      rw [called]
      cases reply with
      | Err error => simp [code.visit]
      | Ok unitValue =>
        cases unitValue
        simp only [bind_ok,Std.uncurry,code.visit]
        exact compiler_table_rest_total ops law before after next env count index depth types arity _
          (kept rfl) bound target aligned fixups tables coordinate

theorem compiler_table_reader_loop_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current : runtime.compiler.FunctionCompiler A)
    (state : code.BodyState) (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (count index : U32) (arity : Option Usize) (first : signature.ResultType) (held : TableCollecting before current state)
    (bound : index.val ≤ count.val) (bounded : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (aligned : SourceAligned before) (fixups : FixupBudget before.frames.val before.function.code.val.length)
    (tables : before.function.jump_tables.val.length ≤ before.function.code.val.length)
    (coordinate : before.function.body_start.val + before.next_source.val ≤ Usize.max) :
    code.branch_table_with_loop (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      state.core data env profile current count arity first index ⦃ out =>
        out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val ⦄ := by
  exact code.branch_table_with_loop.total_on _ data env profile count
    (fun state current _ _ _ => TableCollecting before current state)
    (fun state current => ObservedStack current state.core.vals.val)
    (by intro state current arity first index bound held
        apply WP.spec_mono (compiler_table_body_total ops law before current state data env profile
          count index arity first held bound bounded aligned fixups tables coordinate)
        intro result ready
        cases result <;> exact ready)
    state current arity first index bound held

theorem compiler_table_reader_wasm2_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (shape : Control.Shape state.core) (bounded : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (frameCount : compiler.frames.val.length = state.core.ctrls.val.length)
    (empty : compiler.table_depths.val = [])
    (room : compiler.function.code.val.length+3 ≤ 3*state.core.pos.val)
    (aligned : SourceAligned compiler) (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (tables : compiler.function.jump_tables.val.length ≤ compiler.function.code.val.length)
    (coordinate : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    code.branch_table_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      state data env .Wasm2 compiler ⦃ out => out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val ⦄ := by
  unfold code.branch_table_with
  step with reader.read_u32_leb.spec data state.core.pos as ⟨status,decoded⟩
  cases status with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨count,next⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry]
    obtain ⟨progress,endBound⟩ := decoded.span
    step with code.pop_with_type.total {state.core with pos := next} .I32
      (show Control.Shape {state.core with pos := next} from ⟨shape.ordered,shape.bounded⟩)
      as ⟨status,popped,shape',controls,position,_,_⟩
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok selector =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry]
      apply compiler_table_reader_loop_total ops law compiler compiler ⟨popped⟩ data env .Wasm2 count 0#u32 none
        .Empty _ (by simp) bounded aligned fixups tables coordinate
      refine ⟨⟨compiler.budget,compiler.table_depths,rfl⟩,by simp [empty],?_,?_,?_,shape'⟩
      · simp only [empty,List.length_nil,Nat.mul_zero,Nat.add_zero,position]
        omega
      · simp only [position]
        omega
      · simpa [controls] using frameCount

end Itasca.Runtime.Compiler
