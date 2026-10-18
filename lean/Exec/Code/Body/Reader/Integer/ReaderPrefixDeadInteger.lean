import Exec.Code.Body.Reader.Common.ReaderDead
import Exec.Code.Local.Relations.Common.KnownNumericStack
import Exec.Code.Body.Reader.Common.ReaderEqz
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_prefix_dead_integer_wasm2 {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {types functions returns locals parents current}
    (invariant : CompilerPrefix initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (ty : Inn) (op : IntegerBinary)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (binaryOpcode ty op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (binaryOpcode ty op)) before = .ok (.Ok (), out, after)) :
    ∃ values,
      ReaderPostWasm2 p out.core (op.source ty) p.current.ctrl.polymorphic_base values ∧
      CompilerPrefix initial after types functions returns locals parents (current.advance (op.source ty))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨operation, hook, meaning, handler, instruction, inputs, output,
    hookEq, ordinary, baseOpcode, sign, misc⟩ := binary_reader_facts ops before out.core ty op
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index _ before after ordinary baseOpcode sign misc contextLocals accepted
  obtain ⟨callback, read, _, _, values, effect, post⟩ := reader_numeric_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core _ operation hook
    capacity byte meaning handler run
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  have physicalBase : (Control.base st.core).val = outer.length := by
    simpa [Control.base, controls] using base
  have known := numeric_read_known operation st.core out.core outer p.current.vals vals physicalBase capacity invariant.known read
  rw [instruction] at post
  rw [hookEq, binaryCallback_eq] at callback
  exact ⟨values, post, post.dead_op ops law invariant dead known (binaryOpcode ty op) 0#u32 0#u32 0#u128 callback⟩

theorem reader_prefix_dead_eqz_wasm2 {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {types functions returns locals parents current}
    (invariant : CompilerPrefix initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (ty : Inn)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (eqzOpcode ty))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (eqzOpcode ty)) before = .ok (.Ok (), out, after)) :
    ∃ values,
      ReaderPostWasm2 p out.core (eqzSource ty) p.current.ctrl.polymorphic_base values ∧
      CompilerPrefix initial after types functions returns locals parents (current.advance (eqzSource ty))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨operation, hook, meaning, handler, instruction, inputs, output,
    hookEq, ordinary, baseOpcode, sign, misc⟩ := eqz_reader_facts ops before out.core ty
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index _ before after ordinary baseOpcode sign misc contextLocals accepted
  obtain ⟨callback, read, _, _, values, effect, post⟩ := reader_numeric_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core _ operation hook
    capacity byte meaning handler run
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  have physicalBase : (Control.base st.core).val = outer.length := by
    simpa [Control.base, controls] using base
  have known := numeric_read_known operation st.core out.core outer p.current.vals vals physicalBase capacity invariant.known read
  rw [instruction] at post
  rw [hookEq, eqzCallback_eq] at callback
  exact ⟨values, post, post.dead_op ops law invariant dead known (eqzOpcode ty) 0#u32 0#u32 0#u128 callback⟩

theorem reader_prefix_dead_integer_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    {types functions returns locals parents current}
    (invariant : CompilerPrefix initial before types functions returns locals parents current st.vals.val p.start.val)
    (dead : before.reachable = false)
    (ty : Inn) (op : IntegerBinary)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (binaryOpcode ty op))
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (binaryOpcode ty op)) before = .ok (.Ok (), out, after)) :
    ∃ values,
      ReaderPostWasm1 p out (op.source ty) p.current.ctrl.polymorphic_base values ∧
      CompilerPrefix initial after types functions returns locals parents (current.advance (op.source ty))
        out.vals.val out.pos.val ∧ after.reachable = false := by
  obtain ⟨operation, hook, meaning, handler, instruction, inputs, output,
    hookEq, ordinary, baseOpcode, sign, misc⟩ := binary_reader_facts ops before out ty op
  have capacity : st.vals.val.length < Usize.max := by have bound := p.val_capacity; omega
  obtain ⟨callback, read, _, _, values, effect, post⟩ := reader_numeric_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out _ operation hook
    capacity byte meaning handler accepted
  obtain ⟨_, outer, _, _, base, _, controls, vals⟩ := p.opened
  have physicalBase : (Control.base st).val = outer.length := by
    simpa [Control.base, controls] using base
  have known := numeric_read_known operation st out outer p.current.vals vals physicalBase capacity invariant.known read
  rw [instruction] at post
  rw [hookEq, binaryCallback_eq] at callback
  exact ⟨values, post, post.dead_op ops law invariant dead known (binaryOpcode ty op) 0#u32 0#u32 0#u128 callback⟩

theorem reader_prefix_dead_eqz_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    {types functions returns locals parents current}
    (invariant : CompilerPrefix initial before types functions returns locals parents current st.vals.val p.start.val)
    (dead : before.reachable = false)
    (ty : Inn)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (eqzOpcode ty))
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (eqzOpcode ty)) before = .ok (.Ok (), out, after)) :
    ∃ values,
      ReaderPostWasm1 p out (eqzSource ty) p.current.ctrl.polymorphic_base values ∧
      CompilerPrefix initial after types functions returns locals parents (current.advance (eqzSource ty))
        out.vals.val out.pos.val ∧ after.reachable = false := by
  obtain ⟨operation, hook, meaning, handler, instruction, inputs, output,
    hookEq, ordinary, baseOpcode, sign, misc⟩ := eqz_reader_facts ops before out ty
  have capacity : st.vals.val.length < Usize.max := by have bound := p.val_capacity; omega
  obtain ⟨callback, read, _, _, values, effect, post⟩ := reader_numeric_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out _ operation hook
    capacity byte meaning handler accepted
  obtain ⟨_, outer, _, _, base, _, controls, vals⟩ := p.opened
  have physicalBase : (Control.base st).val = outer.length := by
    simpa [Control.base, controls] using base
  have known := numeric_read_known operation st out outer p.current.vals vals physicalBase capacity invariant.known read
  rw [instruction] at post
  rw [hookEq, eqzCallback_eq] at callback
  exact ⟨values, post, post.dead_op ops law invariant dead known (eqzOpcode ty) 0#u32 0#u32 0#u128 callback⟩

end Exec.Code
