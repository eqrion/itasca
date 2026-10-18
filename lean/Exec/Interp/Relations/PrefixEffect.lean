import Exec.Interp.Relations.CopyRel
import Itasca.Support.Result

namespace Exec.Interp
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

theorem admin_const64_prefix (exec : runtime.interp.Execution) (base : Usize)
    (dst : U32) (value : U64)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution)
    (returned : runtime.interp.admin_const64 memory hooks floats allocator exec base dst value = .ok out) :
    SlotPrefix base.val exec.slots.val out.2.slots.val := by
  unfold runtime.interp.admin_const64 at returned
  simp only [lift, bind_ok] at returned
  obtain ⟨pd, hpd, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  obtain ⟨write, hwrite, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  have same := Result.ok_injective returned
  rw [← same]
  rw [vec_index_mut_observed exec.slots pd write.1 write.2 hwrite]
  apply SlotPrefix.set
  have sum := add_observed base (UScalar.cast .Usize dst) pd hpd
  omega

theorem admin_const32_prefix (exec : runtime.interp.Execution) (base : Usize)
    (dst : U32) (value : U32)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution)
    (returned : runtime.interp.admin_const32 memory hooks floats allocator exec base dst value = .ok out) :
    SlotPrefix base.val exec.slots.val out.2.slots.val := by
  unfold runtime.interp.admin_const32 at returned
  simp only [lift, bind_ok] at returned
  obtain ⟨pd, hpd, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  obtain ⟨write, hwrite, returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ returned
  have same := Result.ok_injective returned
  rw [← same]
  rw [vec_index_mut_observed exec.slots pd write.1 write.2 hwrite]
  apply SlotPrefix.set
  have sum := add_observed base (UScalar.cast .Usize dst) pd hpd
  omega

theorem admin_copy_prefix (exec : runtime.interp.Execution) (base : Usize)
    (dst : U32) (value : U32)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution)
    (returned : runtime.interp.admin_copy memory hooks floats allocator exec base dst value = .ok out) :
    SlotPrefix base.val exec.slots.val out.2.slots.val := by
  unfold runtime.interp.admin_copy at returned
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

theorem admin_copy2_prefix (exec : runtime.interp.Execution) (base : Usize)
    (dst src : U32)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution)
    (returned : runtime.interp.admin_copy2 memory hooks floats allocator exec base dst src = .ok out) :
    SlotPrefix base.val exec.slots.val out.2.slots.val := by
  unfold runtime.interp.admin_copy2 at returned
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

theorem admin_copy_n_prefix (exec : runtime.interp.Execution) (base : Usize)
    (dst src count : U32)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution)
    (returned : runtime.interp.admin_copy_n memory hooks floats allocator exec base dst src count = .ok out) :
    SlotPrefix base.val exec.slots.val out.2.slots.val := by
  unfold runtime.interp.admin_copy_n at returned
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

end Exec.Interp
