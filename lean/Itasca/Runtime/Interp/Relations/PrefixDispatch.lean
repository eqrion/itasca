import Itasca.Runtime.Interp.Relations.PrefixEffect
import Itasca.Runtime.Interp.Numeric.Integer.NumericDispatch
import Itasca.Runtime.Interp.Relations.Fetch
import Itasca.Runtime.Compiler.Local.Relations.Emission.Rel

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem execute_jump_prefix (exec : runtime.interp.Execution) (base index : Usize) (target : U32)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution)
    (returned : runtime.interp.execute_jump exec index target = .ok out) :
    SlotPrefix base.val exec.slots.val out.2.slots.val := by
  unfold runtime.interp.execute_jump at returned
  obtain ⟨frame, lookup, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  have same := Result.ok_injective returned
  rw [← same]
  exact .refl _ _

theorem execute_jump_if_zero_prefix (exec : runtime.interp.Execution) (base index : Usize) (cond target : U32)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution)
    (returned : runtime.interp.execute_jump_if_zero exec index base cond target = .ok out) :
    SlotPrefix base.val exec.slots.val out.2.slots.val := by
  unfold runtime.interp.execute_jump_if_zero at returned
  simp only [lift, bind_ok] at returned
  obtain ⟨position, address, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  obtain ⟨value, lookup, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  split at returned
  · obtain ⟨frame, lookup, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
    have same := Result.ok_injective returned
    rw [← same]
    exact .refl _ _
  · have same := Result.ok_injective returned
    rw [← same]
    exact .refl _ _

theorem execute_jump_if_non_zero_prefix (exec : runtime.interp.Execution) (base index : Usize) (cond target : U32)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution)
    (returned : runtime.interp.execute_jump_if_non_zero exec index base cond target = .ok out) :
    SlotPrefix base.val exec.slots.val out.2.slots.val := by
  unfold runtime.interp.execute_jump_if_non_zero at returned
  simp only [lift, bind_ok] at returned
  obtain ⟨position, address, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  obtain ⟨value, lookup, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  split at returned
  · obtain ⟨frame, lookup, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
    have same := Result.ok_injective returned
    rw [← same]
    exact .refl _ _
  · have same := Result.ok_injective returned
    rw [← same]
    exact .refl _ _

theorem dispatch_scalar_prefix (exec : runtime.interp.Execution) (base : Usize) (op : U16) (instruction : Compiler.Bytecode)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution)
    (returned : runtime.interp.dispatch_scalar floats exec base op instruction = .ok out) :
    SlotPrefix base.val exec.slots.val out.2.slots.val := by
  unfold runtime.interp.dispatch_scalar at returned
  obtain ⟨operands, lookup, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  exact execute_scalar_prefix floats exec base op operands.1 operands.2.1 operands.2.2 out returned

/-- Bytecode classes that never write below the current frame base. -/
inductive PrefixInstruction : Compiler.Bytecode → Prop where
  | numeric (op : SourceMachine.Numeric.Instruction) (dst a b : U32) : PrefixInstruction (Compiler.integerInstruction op dst a b)
  | integer (ty : Inn) (op : Compiler.IntegerBinary) (a b : U32) : PrefixInstruction (op.target ty a b)
  | eqz32 (dst a b : U32) : PrefixInstruction (.I32Eqz dst a b)
  | eqz64 (dst a b : U32) : PrefixInstruction (.I64Eqz dst a b)
  | const32 (dst value : U32) : PrefixInstruction (.Const32 dst value)
  | const64 (dst : U32) (value : U64) : PrefixInstruction (.Const64 dst value)
  | copy (dst src : U32) : PrefixInstruction (.Copy dst src)
  | copy2 (dst src : U32) : PrefixInstruction (.Copy2 dst src)
  | copyN (dst src count : U32) : PrefixInstruction (.CopyN dst src count)
  | jump (target : U32) : PrefixInstruction (.Jump target)
  | jumpZero (cond target : U32) : PrefixInstruction (.JumpIfZero cond target)
  | jumpNonzero (cond target : U32) : PrefixInstruction (.JumpIfNonZero cond target)
  | loopHead : PrefixInstruction .LoopHead
  | unreachable : PrefixInstruction .Unreachable

theorem pair_result_prefix (exec : runtime.interp.Execution) (base : Usize)
    (store : runtime.store.Store M) (platform : P)
    (handler : Result (core.result.Result Unit runtime.ExecError × runtime.interp.Execution))
    (preserves : ∀ out, handler = .ok out → SlotPrefix base.val exec.slots.val out.2.slots.val)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P)
    (returned : (do let (status, updated) ← handler; .ok (status, updated, store, platform)) = .ok out) :
    SlotPrefix base.val exec.slots.val out.2.1.slots.val := by
  obtain ⟨result, run, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  have same := Result.ok_injective returned
  rw [← same]
  exact preserves result run

theorem dispatch_prefix (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index inst function base : Usize) (instruction : Compiler.Bytecode)
    (allowed : PrefixInstruction instruction)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P)
    (returned : runtime.interp.dispatch memory hooks floats allocator exec store platform
      index inst function base instruction = .ok out) :
    SlotPrefix base.val exec.slots.val out.2.1.slots.val := by
  cases allowed with
  | numeric op dst a b =>
    rw [dispatch_integer_eq] at returned
    exact pair_result_prefix exec base store platform _
      (execute_scalar_prefix floats exec base (Compiler.integerOpcode op) dst a b) out returned
  | integer ty op a b =>
    cases ty <;> cases op <;>
      simp only [Compiler.IntegerBinary.target, runtime.interp.dispatch] at returned <;>
      exact pair_result_prefix exec base store platform _ (dispatch_scalar_prefix floats exec base _ _) out returned
  | eqz32 dst a b | eqz64 dst a b =>
    simp only [runtime.interp.dispatch] at returned
    exact pair_result_prefix exec base store platform _ (dispatch_scalar_prefix floats exec base _ _) out returned
  | const32 dst value =>
    simp only [runtime.interp.dispatch] at returned
    exact pair_result_prefix exec base store platform _
      (execute_const32_prefix exec base dst value) out returned
  | const64 dst value =>
    simp only [runtime.interp.dispatch] at returned
    exact pair_result_prefix exec base store platform _
      (execute_const64_prefix exec base dst value) out returned
  | copy dst src =>
    simp only [runtime.interp.dispatch] at returned
    exact pair_result_prefix exec base store platform _
      (execute_copy_prefix exec base dst src) out returned
  | copy2 dst src =>
    simp only [runtime.interp.dispatch] at returned
    exact pair_result_prefix exec base store platform _
      (execute_copy2_prefix exec base dst src) out returned
  | copyN dst src count =>
    simp only [runtime.interp.dispatch] at returned
    exact pair_result_prefix exec base store platform _
      (execute_copy_n_prefix exec base dst src count) out returned
  | jump target =>
    simp only [runtime.interp.dispatch] at returned
    exact pair_result_prefix exec base store platform _
      (execute_jump_prefix exec base index target) out returned
  | jumpZero cond target =>
    simp only [runtime.interp.dispatch] at returned
    exact pair_result_prefix exec base store platform _
      (execute_jump_if_zero_prefix exec base index cond target) out returned
  | jumpNonzero cond target =>
    simp only [runtime.interp.dispatch] at returned
    exact pair_result_prefix exec base store platform _
      (execute_jump_if_non_zero_prefix exec base index cond target) out returned
  | loopHead =>
    simp only [runtime.interp.dispatch] at returned
    obtain ⟨result, run, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
    have same := Result.ok_injective returned
    rw [← same]
    exact .refl _ _
  | unreachable =>
    simp only [runtime.interp.dispatch, runtime.interp.execute_unreachable] at returned
    obtain ⟨result, run, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
    have same := Result.ok_injective returned
    rw [← same]
    exact .refl _ _

theorem spec_value_eq {T : Type} (computation : Result T) (value : T)
    (specification : computation ⦃ out => out = value ⦄) : computation = .ok value := by
  obtain ⟨actual, returned, same⟩ := WP.spec_imp_exists specification
  simpa only [same] using returned

theorem step_prefix (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (instruction : Compiler.Bytecode)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (hop : compiled.code.val[raw.pc.val]? = some instruction)
    (allowed : PrefixInstruction instruction)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P)
    (returned : runtime.interp.step memory hooks floats allocator exec store platform = .ok out) :
    SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val := by
  have hiindex : (exec.frames.len - 1#usize : Result Usize) = .ok index := by
    apply spec_value_eq
    step as ⟨found, hf⟩
    scalar_tac
  have hframe := spec_value_eq _ _ (vec_index_given exec.frames index raw hf)
  have hinst := spec_value_eq _ _ (vec_index_given store.instances raw.instance inst hi)
  have hcompiled := spec_value_eq _ _ (vec_index_given inst.module.functions raw.function compiled hc)
  have hinstruction := spec_value_eq _ _ (vec_index_given compiled.code (UScalar.cast .Usize raw.pc) instruction
    (by simpa only [U32.cast_Usize_val_eq] using hop))
  change alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice runtime.interp.Frame) exec.frames index = .ok raw at hframe
  change alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice runtime.store.ModuleInst) store.instances raw.instance = .ok inst at hinst
  change alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice runtime.bytecode.CompiledFunction) inst.module.functions raw.function = .ok compiled at hcompiled
  change alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Compiler.Bytecode) compiled.code (UScalar.cast .Usize raw.pc) = .ok instruction at hinstruction
  unfold runtime.interp.step at returned
  simp only [lift, hiindex, hframe, hinst, hcompiled, hinstruction, bind_ok] at returned
  cases hnext : U32.checked_add raw.pc 1#u32 with
  | none =>
    simp only [hnext] at returned
    have same := Result.ok_injective returned
    rw [← same]
    exact .refl _ _
  | some next =>
    simp only [hnext] at returned
    obtain ⟨write, hwrite, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
    exact dispatch_prefix memory hooks floats allocator { exec with frames := write.2 { write.1 with pc := next } }
      store platform index raw.instance raw.function raw.base instruction allowed out returned

end Itasca.Runtime.Interp
