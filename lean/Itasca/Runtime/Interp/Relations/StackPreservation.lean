import Itasca.Runtime.Interp.Relations.Defaults
import Itasca.Support.Result
import Itasca.Runtime.Interp.Numeric.Integer.NumericFetch
import Itasca.Runtime.Compiler.Local.Relations.Emission.Rel
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.Interp.Relations.SuspendedPoint

/-!
Sections, each formerly its own module: PrefixEffect, PrefixDispatch, FrameStorePrefix, WordDecoding, StackPreservation.
-/

/-! ## PrefixEffect -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

structure SlotPrefix (base : Nat) (before after : List U64) : Prop where
  length : after.length = before.length
  words : ∀ index, index < base → after[index]? = before[index]?

theorem SlotPrefix.refl (base : Nat) (words : List U64) : SlotPrefix base words words :=
  ⟨rfl, by intros; rfl⟩

theorem SlotPrefix.trans {base before middle after}
    (first : SlotPrefix base before middle) (second : SlotPrefix base middle after) :
    SlotPrefix base before after :=
  ⟨second.length.trans first.length, fun i hi => (second.words i hi).trans (first.words i hi)⟩

theorem SlotPrefix.set (base : Nat) (words : List U64) (index : Nat) (word : U64)
    (above : base ≤ index) : SlotPrefix base words (words.set index word) := by
  refine ⟨List.length_set, ?_⟩
  intro j hj
  have ne : index ≠ j := by omega
  simp only [List.getElem?_set, ne, ite_false]

theorem SlotPrefix.copy (base : Nat) (words : List U64) (dst src count : Nat)
    (above : base ≤ dst) : SlotPrefix base words (copyWords words dst src count) := by
  induction count generalizing words dst src with
  | zero => exact .refl _ _
  | succ count ih =>
    exact (SlotPrefix.set base words dst words[src]! above).trans (ih _ _ _ (by omega))

theorem SlotPrefix.region {base before after} (preserved : SlotPrefix base before after)
    (position : Nat) (bits : List Nat) (represented : WordsAt before position bits)
    (below : position + bits.length ≤ base) : WordsAt after position bits := by
  apply represented.congr_region preserved.length
  intro index bound
  exact preserved.words _ (by omega)

theorem add_observed {ty : UScalarTy} (left right value : UScalar ty)
    (returned : (left + right : Result (UScalar ty)) = .ok value) : value.val = left.val + right.val := by
  have facts := UScalar.add_equiv left right
  rw [returned] at facts
  exact facts.2.1

theorem vec_index_mut_observed (words : alloc.vec.Vec U64) (index : Usize)
    (value : U64) (back : U64 → alloc.vec.Vec U64)
    (returned : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice U64) words index = .ok (value, back)) :
    ∀ replacement, (back replacement).val = words.val.set index.val replacement := by
  simp only [alloc.vec.Vec.index_mut,
    core.slice.index.Usize.index_mut, Slice.index_mut_usize] at returned
  obtain ⟨found, read, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  change Slice.index_mut_usize words.slice index = .ok found at read
  unfold Slice.index_mut_usize at read
  obtain ⟨item, indexed, read⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ read
  have foundEq := Result.ok_injective read
  rw [← foundEq] at returned
  have same := Result.ok_injective returned
  have backEq := congrArg Prod.snd same
  dsimp only at backEq
  rw [← backEq]
  intro replacement
  exact Slice.set_val_eq _ _ _

theorem execute_scalar_prefix {F : Type} (floats : runtime.platform.FloatOps F)
    (exec : runtime.interp.Execution) (base : Usize) (op : U16) (dst a b : U32)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution)
    (returned : runtime.interp.execute_scalar floats exec base op dst a b = .ok out) :
    SlotPrefix base.val exec.slots.val out.2.slots.val := by
  unfold runtime.interp.execute_scalar at returned
  simp only [lift, bind_ok] at returned
  obtain ⟨pa, hpa, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  obtain ⟨va, hva, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  obtain ⟨pb, hpb, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  obtain ⟨vb, hvb, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  obtain ⟨numeric, hn, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  cases numeric with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from] at returned
    simp [bind_ok] at returned
    rw [← returned]
    exact .refl _ _
  | Ok value =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at returned
    obtain ⟨pd, hpd, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
    obtain ⟨write, hwrite, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
    have same := Result.ok_injective returned
    rw [← same]
    rw [vec_index_mut_observed exec.slots pd write.1 write.2 hwrite]
    apply SlotPrefix.set
    have sum := add_observed base (UScalar.cast .Usize dst) pd hpd
    omega

theorem slice_update_observed (words : Slice U64) (index : Usize) (value : U64)
    (out : Slice U64) (returned : words.update index value = .ok out) :
    out.val = words.val.set index.val value := by
  unfold Slice.update at returned
  cases lookup : words.val[index.val]? with
  | none => simp [lookup] at returned
  | some old =>
    simp only [lookup] at returned
    have same := Result.ok_injective returned
    rw [← same]
    simp only [Slice.from_val]

theorem copy_loop_prefix (words : Slice U64) (dst src n i : Usize)
    (out : Slice U64) (returned : runtime.interp.copy_loop words dst src n i = .ok out) :
    SlotPrefix dst.val words.val out.val := by
  induction remaining : n.val - i.val using Nat.strong_induction_on generalizing words i out with
  | h remaining ih =>
    unfold runtime.interp.copy_loop at returned
    rw [loop.eq_def] at returned
    simp only [runtime.interp.copy_loop.body] at returned
    split at returned
    · rename_i more
      have less : i.val < n.val := by scalar_tac
      obtain ⟨flow, hflow, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
      obtain ⟨ps, hps, hflow⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ hflow
      obtain ⟨value, hvalue, hflow⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ hflow
      obtain ⟨pd, hpd, hflow⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ hflow
      obtain ⟨updated, hupdated, hflow⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ hflow
      obtain ⟨next, hnext, hflow⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ hflow
      have flowEq := Result.ok_injective hflow
      rw [← flowEq] at returned
      have nextVal := add_observed i 1#usize next hnext
      have dstVal := add_observed dst i pd hpd
      have updateVal := slice_update_observed words pd value updated hupdated
      have first : SlotPrefix dst.val words.val updated.val := by
        rw [updateVal]
        exact .set _ _ _ _ (by omega)
      have nextVal' : next.val = i.val + 1 := by simpa using nextVal
      exact first.trans (ih (n.val - next.val) (by omega)
        updated next out returned rfl)
    · simp only [bind_ok] at returned
      have same := Result.ok_injective returned
      rw [← same]
      exact .refl _ _

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem execute_const64_prefix (exec : runtime.interp.Execution) (base : Usize)
    (dst : U32) (value : U64)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution)
    (returned : runtime.interp.execute_const64 exec base dst value = .ok out) :
    SlotPrefix base.val exec.slots.val out.2.slots.val := by
  unfold runtime.interp.execute_const64 at returned
  simp only [lift, bind_ok] at returned
  obtain ⟨pd, hpd, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  obtain ⟨write, hwrite, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  have same := Result.ok_injective returned
  rw [← same]
  rw [vec_index_mut_observed exec.slots pd write.1 write.2 hwrite]
  apply SlotPrefix.set
  have sum := add_observed base (UScalar.cast .Usize dst) pd hpd
  omega

theorem execute_const32_prefix (exec : runtime.interp.Execution) (base : Usize)
    (dst : U32) (value : U32)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution)
    (returned : runtime.interp.execute_const32 exec base dst value = .ok out) :
    SlotPrefix base.val exec.slots.val out.2.slots.val := by
  unfold runtime.interp.execute_const32 at returned
  simp only [lift, bind_ok] at returned
  obtain ⟨pd, hpd, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  obtain ⟨write, hwrite, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  have same := Result.ok_injective returned
  rw [← same]
  rw [vec_index_mut_observed exec.slots pd write.1 write.2 hwrite]
  apply SlotPrefix.set
  have sum := add_observed base (UScalar.cast .Usize dst) pd hpd
  omega

theorem execute_copy_prefix (exec : runtime.interp.Execution) (base : Usize)
    (dst : U32) (value : U32)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution)
    (returned : runtime.interp.execute_copy exec base dst value = .ok out) :
    SlotPrefix base.val exec.slots.val out.2.slots.val := by
  unfold runtime.interp.execute_copy at returned
  simp only [lift, bind_ok] at returned
  obtain ⟨ps, hps, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  obtain ⟨source, hsource, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  obtain ⟨pd, hpd, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  obtain ⟨write, hwrite, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  have same := Result.ok_injective returned
  rw [← same]
  rw [vec_index_mut_observed exec.slots pd write.1 write.2 hwrite]
  apply SlotPrefix.set
  have sum := add_observed base (UScalar.cast .Usize dst) pd hpd
  omega

theorem execute_copy2_prefix (exec : runtime.interp.Execution) (base : Usize)
    (dst src : U32)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution)
    (returned : runtime.interp.execute_copy2 exec base dst src = .ok out) :
    SlotPrefix base.val exec.slots.val out.2.slots.val := by
  unfold runtime.interp.execute_copy2 at returned
  simp only [lift, bind_ok, alloc.vec.Vec.deref_mut] at returned
  obtain ⟨pd, hpd, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  obtain ⟨ps, hps, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  obtain ⟨updated, hupdated, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  have preserved := copy_loop_prefix exec.slots.slice pd ps _ 0#usize updated hupdated
  have same := Result.ok_injective returned
  rw [← same]
  refine ⟨preserved.length, ?_⟩
  intro position below
  apply preserved.words
  have sum := add_observed base (UScalar.cast .Usize dst) pd hpd
  omega

theorem execute_copy_n_prefix (exec : runtime.interp.Execution) (base : Usize)
    (dst src count : U32)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution)
    (returned : runtime.interp.execute_copy_n exec base dst src count = .ok out) :
    SlotPrefix base.val exec.slots.val out.2.slots.val := by
  unfold runtime.interp.execute_copy_n at returned
  simp only [lift, bind_ok, alloc.vec.Vec.deref_mut] at returned
  obtain ⟨pd, hpd, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  obtain ⟨ps, hps, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  obtain ⟨updated, hupdated, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  have preserved := copy_loop_prefix exec.slots.slice pd ps _ 0#usize updated hupdated
  have same := Result.ok_injective returned
  rw [← same]
  refine ⟨preserved.length, ?_⟩
  intro position below
  apply preserved.words
  have sum := add_observed base (UScalar.cast .Usize dst) pd hpd
  omega

end Itasca.Runtime.Interp

end

/-! ## PrefixDispatch -/

section

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

end

/-! ## FrameStorePrefix -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Existing frame metadata survives object creation when old entries retain
exact raw identities and indices. Payload mutation is unrestricted here. This
is a transport relation, not an assumed law of arbitrary host callbacks. -/
structure FrameStorePrefix {M : Type} (before after : runtime.store.Store M) : Prop where
  identity : after.id = before.id
  functions : after.funcs.val.take before.funcs.length = before.funcs.val
  types : after.types.val.take before.types.length = before.types.val
  instances : after.instances.val.take before.instances.length = before.instances.val

/-- Every retained module type index was already present before extension. -/
def FrameTypeBounds {M : Type} (store : runtime.store.Store M) : Prop :=
  ∀ inst ∈ store.instances.val, ∀ index ∈ inst.types.val, index.val < store.types.length

private theorem retained_lookup {T : Type} {before after : List T}
    (retained : after.take before.length = before) {index : Nat} {value : T}
    (found : before[index]? = some value) : after[index]? = some value := by
  have bound := (List.getElem?_eq_some_iff.mp found).1
  have same := congrArg (fun xs => xs[index]?) retained
  simpa only [List.getElem?_take,if_pos bound,found] using same

theorem FrameStorePrefix.refl {M : Type} (store : runtime.store.Store M) :
    FrameStorePrefix store store := by
  exact ⟨rfl,List.take_length,List.take_length,List.take_length⟩

private theorem retained_trans {T : Type} {a b c : List T}
    (first : b.take a.length = a) (second : c.take b.length = b) : c.take a.length = a := by
  have bound : a.length ≤ b.length := by
    have lengths := congrArg List.length first
    simp only [List.length_take] at lengths
    omega
  calc
    c.take a.length = (c.take b.length).take a.length := by simp only [List.take_take,Nat.min_eq_left bound]
    _ = b.take a.length := by rw [second]
    _ = a := first

theorem FrameStorePrefix.trans {M : Type} {a b c : runtime.store.Store M}
    (first : FrameStorePrefix a b) (second : FrameStorePrefix b c) : FrameStorePrefix a c :=
  ⟨second.identity.trans first.identity,retained_trans first.functions second.functions,
    retained_trans first.types second.types,retained_trans first.instances second.instances⟩

theorem FrameStoreMetadata.prefix {M : Type} {before after : runtime.store.Store M}
    (same : FrameStoreMetadata before after) : FrameStorePrefix before after := by
  exact ⟨same.identity,by simp [same.functions],by simp [same.types],by simp [same.instances]⟩

theorem FrameStorePrefix.function_lookup {M : Type} {before after : runtime.store.Store M}
    (retained : FrameStorePrefix before after) {index : Nat} {function : runtime.store.FuncInst}
    (found : before.funcs.val[index]? = some function) : after.funcs.val[index]? = some function :=
  retained_lookup retained.functions found

theorem FrameStorePrefix.type_lookup {M : Type} {before after : runtime.store.Store M}
    (retained : FrameStorePrefix before after) {index : Nat} {signature : Itasca.wasm_types.FuncType}
    (found : before.types.val[index]? = some signature) : after.types.val[index]? = some signature :=
  retained_lookup retained.types found

theorem FrameStorePrefix.instance_lookup {M : Type} {before after : runtime.store.Store M}
    (retained : FrameStorePrefix before after) {index : Nat} {inst : runtime.store.ModuleInst}
    (found : before.instances.val[index]? = some inst) : after.instances.val[index]? = some inst :=
  retained_lookup retained.instances found

theorem FrameStorePrefix.decode_instance {M : Type} {before after : runtime.store.Store M}
    (retained : FrameStorePrefix before after) (inst : runtime.store.ModuleInst)
    (typeBounds : ∀ index ∈ inst.types.val, index.val < before.types.length) :
    Store.decodeInstance after inst = Store.decodeInstance before inst := by
  unfold Store.decodeInstance
  congr 1
  apply List.map_congr_left
  intro index member
  have bound := typeBounds index member
  have found : before.types.val[index.val]? = some before.types.val[index.val] := List.getElem?_eq_getElem bound
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map,found,retained.type_lookup found]

theorem FunctionTable.store_prefix {M : Type} {before after : runtime.store.Store M}
    (retained : FrameStorePrefix before after) {inst functions}
    (table : FunctionTable before inst functions) : FunctionTable after inst functions := by
  apply table.imp
  intro address ty entry
  obtain ⟨owner,function,signature,found,typed,decoded⟩ := entry
  exact ⟨owner.trans retained.identity.symm,function,signature,retained.function_lookup found,retained.type_lookup typed,decoded⟩

theorem FrameBinding.store_prefix {M : Type} {before after : runtime.store.Store M}
    (retained : FrameStorePrefix before after) (bounds : FrameTypeBounds before)
    {exec raw source} (binding : FrameBinding before exec raw source) : FrameBinding after exec raw source := by
  obtain ⟨inst,fn,compiled,signature,owner,member,found,functionAt,wasm,code,typed,moduleEq,results,locals,capacity⟩ := binding
  exact ⟨inst,fn,compiled,signature,owner.trans retained.identity.symm,member,retained.instance_lookup found,
    retained.function_lookup functionAt,wasm,code,retained.type_lookup typed,
    moduleEq.trans (retained.decode_instance inst (bounds inst (List.mem_of_getElem? found))).symm,
    results,locals,capacity⟩

theorem FrameProgram.store_prefix {M : Type} {before after : runtime.store.Store M}
    (retained : FrameStorePrefix before after) {raw compiled locals results functions}
    (program : FrameProgram before raw compiled locals results functions) :
    FrameProgram after raw compiled locals results functions := by
  refine ⟨?_,program.checked,program.fetchBound,program.localSlots,program.epilogue⟩
  obtain ⟨inst,found,code,table⟩ := program.lookup
  exact ⟨inst,retained.instance_lookup found,code,table.store_prefix retained⟩

end Itasca.Runtime.Interp

end

/-! ## WordDecoding -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem decode_words_scalar (ty : Itasca.wasm_types.ValueType) (lo hi : U64)
    (scalar : ty ≠ .V128) : Store.decodeWords ty lo hi = Store.decodeWords ty lo 0#u64 := by
  cases ty <;> simp_all [Store.decodeWords]

/-- Recover a represented source value using the pure mathematical word
decoder. Reference addresses remain naturals here, so no usize cast is assumed. -/
theorem decode_words_represents (ty : Itasca.wasm_types.ValueType) (lo hi : U64)
    (value : val) (wellFormed : wf_val value) (typed : sourceType ty = Compiler.valueType value)
    (represented : pairWords ty (lo,hi) = Compiler.encodeValue value) :
    Store.decodeWords ty lo hi = value := by
  have floatBound : ty = .F32 → lo.val < 2^32 := by
    intro same
    subst ty
    have low := congrArg (fun words : List Nat => words[0]!) represented
    simp only [pairWords,sourceType,reduceCtorEq,ite_false,List.getElem!_cons_zero] at low
    rw [low]
    exact encode_value_f32_low value wellFormed typed.symm
  have source := Compiler.decode_encode value wellFormed []
  simp only [List.append_nil] at source
  rw [←typed,←represented,decode_words_code ty lo hi floatBound] at source
  exact congrArg Prod.fst (Option.some.inj source)

theorem WordsAt.decode_value {words : List U64} {position : Nat} (ty : Itasca.wasm_types.ValueType)
    (value : val) (wellFormed : wf_val value) (typed : sourceType ty = Compiler.valueType value)
    (represented : WordsAt words position (Compiler.encodeValue value)) :
    Store.decodeWords ty (Itasca.Runtime.Interp.readPair words position ty).1 (Itasca.Runtime.Interp.readPair words position ty).2 = value := by
  apply decode_words_represents ty _ _ value wellFormed typed
  exact represented.read_pair ty (by rw [Compiler.encode_value_length,←typed])

end Itasca.Runtime.Interp

end

/-! ## StackPreservation -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Unchanged store identity, retained membership, and nonshrinking storage
preserve all frame metadata and allocation facts. -/
theorem FrameBinding.retain {M : Type} {store : runtime.store.Store M}
    {before after : runtime.interp.Execution} {raw source}
    (binding : FrameBinding store before raw source)
    (identity : after.store = before.store)
    (member : raw ∈ after.frames.val)
    (capacity : before.slots.length ≤ after.slots.length) :
    FrameBinding store after raw source := by
  obtain ⟨inst, fn, compiled, signature, oldIdentity, _, hi, hf, hw, hc, hs, hm, hr, hl, bound⟩ := binding
  exact ⟨inst, fn, compiled, signature, identity.trans oldIdentity, member,
    hi, hf, hw, hc, hs, hm, hr, hl, bound.trans capacity⟩

end Itasca.Runtime.Interp

end
