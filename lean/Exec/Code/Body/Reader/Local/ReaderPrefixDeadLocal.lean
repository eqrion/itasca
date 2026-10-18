import Exec.Code.Body.Reader.Common.ReaderDead
import Exec.Code.Body.Relations.Local.KnownLocalStack
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_prefix_dead_local_get_wasm2 {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {types functions returns locals parents current}
    (invariant : CompilerPrefix initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_LOCAL_GET)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_LOCAL_GET before = .ok (.Ok (), out, after)) :
    ∃ (idx : U32) (values : List code.StackType),
      ReaderPostWasm2 p out.core (.LOCAL_GET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ∧
      CompilerPrefix initial after types functions returns locals parents (current.advance (.LOCAL_GET (.mk_uN idx.val)))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_LOCAL_GET before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨idx, values, callback, read, post⟩ := reader_local_get_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity (by simpa only [global_simps] using byte) run
  obtain ⟨ty, _, vals⟩ := reader_local_get_effect st.core out.core data ⟨sourceLocals, p.ft.results⟩ idx capacity read
  have known : ConcreteStack out.core.vals.val := by
    rw [vals]
    exact concreteStack_append.mpr ⟨invariant.known, by simp [ConcreteStack]⟩
  refine ⟨idx, values, post, ?_⟩
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 32#u16 idx 0#u32 0#u128 = _ at callback
  exact post.dead_op ops law invariant dead known 32#u16 idx 0#u32 0#u128 callback

theorem reader_prefix_dead_local_set_wasm2 {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {types functions returns locals parents current}
    (invariant : CompilerPrefix initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_LOCAL_SET)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_LOCAL_SET before = .ok (.Ok (), out, after)) :
    ∃ (idx : U32) (values : List code.StackType),
      ReaderPostWasm2 p out.core (.LOCAL_SET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ∧
      CompilerPrefix initial after types functions returns locals parents (current.advance (.LOCAL_SET (.mk_uN idx.val)))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_LOCAL_SET before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨idx, values, callback, read, post⟩ := reader_local_set_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core (by simpa only [global_simps] using byte) run
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  have known := reader_local_set_known st.core out.core data ⟨sourceLocals, p.ft.results⟩ idx 
    outer p.current.vals vals (by simpa [Control.base, controls] using base) invariant.known read
  refine ⟨idx, values, post, ?_⟩
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 33#u16 idx 0#u32 0#u128 = _ at callback
  exact post.dead_op ops law invariant dead known 33#u16 idx 0#u32 0#u128 callback

theorem reader_prefix_dead_local_tee_wasm2 {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {types functions returns locals parents current}
    (invariant : CompilerPrefix initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_LOCAL_TEE)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_LOCAL_TEE before = .ok (.Ok (), out, after)) :
    ∃ (idx : U32) (values : List code.StackType),
      ReaderPostWasm2 p out.core (.LOCAL_TEE (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ∧
      CompilerPrefix initial after types functions returns locals parents (current.advance (.LOCAL_TEE (.mk_uN idx.val)))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_LOCAL_TEE before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨idx, values, callback, read, post⟩ := reader_local_tee_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity (by simpa only [global_simps] using byte) run
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  have known := reader_local_tee_known st.core out.core data ⟨sourceLocals, p.ft.results⟩ idx capacity 
    outer p.current.vals vals (by simpa [Control.base, controls] using base) invariant.known read
  refine ⟨idx, values, post, ?_⟩
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 34#u16 idx 0#u32 0#u128 = _ at callback
  exact post.dead_op ops law invariant dead known 34#u16 idx 0#u32 0#u128 callback

theorem reader_prefix_dead_local_get_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    {types functions returns locals parents current}
    (invariant : CompilerPrefix initial before types functions returns locals parents current st.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_LOCAL_GET)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_LOCAL_GET before = .ok (.Ok (), out, after)) :
    ∃ (idx : U32) (values : List code.StackType),
      ReaderPostWasm1 p out (.LOCAL_GET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ∧
      CompilerPrefix initial after types functions returns locals parents (current.advance (.LOCAL_GET (.mk_uN idx.val)))
        out.vals.val out.pos.val ∧ after.reachable = false := by
  have capacity : st.vals.val.length < Usize.max := by have bound := p.val_capacity; omega
  obtain ⟨idx, values, callback, read, post⟩ := reader_local_get_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out capacity (by simpa only [global_simps] using byte) accepted
  obtain ⟨ty, _, vals⟩ := reader_local_get_effect st out data ctx idx capacity read
  have known : ConcreteStack out.vals.val := by
    rw [vals]
    exact concreteStack_append.mpr ⟨invariant.known, by simp [ConcreteStack]⟩
  refine ⟨idx, values, post, ?_⟩
  change runtime.compiler.lower.FunctionCompiler.op ops before out 32#u16 idx 0#u32 0#u128 = _ at callback
  exact post.dead_op ops law invariant dead known 32#u16 idx 0#u32 0#u128 callback

theorem reader_prefix_dead_local_set_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    {types functions returns locals parents current}
    (invariant : CompilerPrefix initial before types functions returns locals parents current st.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_LOCAL_SET)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_LOCAL_SET before = .ok (.Ok (), out, after)) :
    ∃ (idx : U32) (values : List code.StackType),
      ReaderPostWasm1 p out (.LOCAL_SET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ∧
      CompilerPrefix initial after types functions returns locals parents (current.advance (.LOCAL_SET (.mk_uN idx.val)))
        out.vals.val out.pos.val ∧ after.reachable = false := by
  have capacity : st.vals.val.length < Usize.max := by have bound := p.val_capacity; omega
  obtain ⟨idx, values, callback, read, post⟩ := reader_local_set_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out (by simpa only [global_simps] using byte) accepted
  obtain ⟨_, outer, _, _, base, _, controls, vals⟩ := p.opened
  have known := reader_local_set_known st out data ctx idx 
    outer p.current.vals vals (by simpa [Control.base, controls] using base) invariant.known read
  refine ⟨idx, values, post, ?_⟩
  change runtime.compiler.lower.FunctionCompiler.op ops before out 33#u16 idx 0#u32 0#u128 = _ at callback
  exact post.dead_op ops law invariant dead known 33#u16 idx 0#u32 0#u128 callback

theorem reader_prefix_dead_local_tee_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    {types functions returns locals parents current}
    (invariant : CompilerPrefix initial before types functions returns locals parents current st.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_LOCAL_TEE)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_LOCAL_TEE before = .ok (.Ok (), out, after)) :
    ∃ (idx : U32) (values : List code.StackType),
      ReaderPostWasm1 p out (.LOCAL_TEE (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ∧
      CompilerPrefix initial after types functions returns locals parents (current.advance (.LOCAL_TEE (.mk_uN idx.val)))
        out.vals.val out.pos.val ∧ after.reachable = false := by
  have capacity : st.vals.val.length < Usize.max := by have bound := p.val_capacity; omega
  obtain ⟨idx, values, callback, read, post⟩ := reader_local_tee_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out capacity (by simpa only [global_simps] using byte) accepted
  obtain ⟨_, outer, _, _, base, _, controls, vals⟩ := p.opened
  have known := reader_local_tee_known st out data ctx idx capacity 
    outer p.current.vals vals (by simpa [Control.base, controls] using base) invariant.known read
  refine ⟨idx, values, post, ?_⟩
  change runtime.compiler.lower.FunctionCompiler.op ops before out 34#u16 idx 0#u32 0#u128 = _ at callback
  exact post.dead_op ops law invariant dead known 34#u16 idx 0#u32 0#u128 callback

end Exec.Code
