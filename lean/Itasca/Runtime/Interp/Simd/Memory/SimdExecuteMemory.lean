import Itasca.Runtime.Interp.Simd.Common.SimdOperandsBounded
import Itasca.Runtime.Interp.Simd.Common.SimdExecutePure
import Itasca.Runtime.Platform.Memory
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

theorem execute_simd_pure_memory_bounded {M F : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instIndex function base : Usize) (op dst a entry : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (imm : runtime.bytecode.SimdImmediate) (wa wb wc wr : U32)
    (value : U128)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : inst.module.functions.val[function.val]? = some code)
    (immediate : code.simd.val[entry.val]? = some imm)
    (shape : runtime.bytecode.simd_shape op = .ok (some (wa,wb,wc,wr)))
    (ma : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (mapped : inst.memories.val[0]? = some ma)
    (issued : store.memories.val[ma.index.val]? = some object)
    (space : base.val + a.val + wa.val + wb.val ≤ Usize.max)
    (lastSpace : wc = 2#u32 → base.val + a.val + wa.val + wb.val < Usize.max)
    (capacity : base.val + dst.val + wr.val ≤ exec.slots.length)
    (numeric : runtime.interp.simd.simd floats op imm.offset imm.lane imm.bits
      (simdInput exec.slots.val (base.val+a.val) wa)
      (simdInput exec.slots.val (base.val+a.val+wa.val) wb)
      (simdInput exec.slots.val (base.val+a.val+wa.val+wb.val) wc) (some (view object.buf)) =
        .ok (.Ok value,some (view object.buf))) :
    runtime.interp.execute_simd memory floats exec store instIndex function base op dst a entry
      ⦃ out => out.1 = .Ok () ∧
        (∃ buffer, out.2.2 = {store with memories := store.memories.set ma.index {object with buf := buffer}} ∧
          view buffer = view object.buf) ∧ SlotsEffect exec out.2.1
        (simdResultSlots exec.slots.val (base.val+dst.val) wr value) ⦄ := by
  unfold runtime.interp.execute_simd
  step with vec_index_given store.instances instIndex inst found as ⟨actual,eq⟩
  subst actual
  step with vec_index_given inst.module.functions function code compiled as ⟨actual,eq⟩
  subst actual
  try simp only [lift,bind_ok]
  step with vec_index_given code.simd (UScalar.cast .Usize entry) imm (by simpa using immediate) as ⟨actual,eq⟩
  subst actual
  rw [shape,bind_ok]
  try simp only [lift,bind_ok]
  step as ⟨pos,hpos⟩
  step with simd_input_bounded as ⟨x,hx⟩
  try simp only [lift,bind_ok]
  step as ⟨ypos,hypos⟩
  step with simd_input_bounded as ⟨y,hy⟩
  try simp only [lift,bind_ok]
  step as ⟨zpos,hzpos⟩
  step with simd_input_bounded as ⟨z,hz⟩
  have hx' : x = simdInput exec.slots.val (base.val+a.val) wa := by simpa [alloc.vec.Vec.deref,hpos] using hx
  have hy' : y = simdInput exec.slots.val (base.val+a.val+wa.val) wb := by simpa [alloc.vec.Vec.deref,hypos,hpos] using hy
  have hz' : z = simdInput exec.slots.val (base.val+a.val+wa.val+wb.val) wc := by simpa [alloc.vec.Vec.deref,hzpos,hypos,hpos] using hz
  rw [hx',hy',hz']
  have hasMemory : alloc.vec.Vec.len inst.memories > 0#usize := by
    have bound := (List.getElem?_eq_some_iff.mp mapped).1
    scalar_tac
  rw [if_pos hasMemory]
  step with vec_index_given inst.memories 0#usize ma (by simpa using mapped) as ⟨actual,eq⟩
  subst actual
  have memoryBound : ma.index.val < store.memories.length := (List.getElem?_eq_some_iff.mp issued).1
  step as ⟨actual,restore,memRead,memBack⟩
  have actualEq : actual = object := by
    have found := List.getElem?_eq_some_iff.mp issued
    simpa [found.2] using memRead
  rw [actualEq]
  obtain ⟨writeBack,writeCall,writeLaw⟩ := laws.write object.buf
  rw [writeCall,bind_ok]
  have numericSpec : runtime.interp.simd.simd floats op imm.offset imm.lane imm.bits
      (simdInput exec.slots.val (base.val+a.val) wa)
      (simdInput exec.slots.val (base.val+a.val+wa.val) wb)
      (simdInput exec.slots.val (base.val+a.val+wa.val+wb.val) wc) (some (view object.buf)) ⦃ out => out = (.Ok value,some (view object.buf)) ⦄ := by
    rw [numeric]
    simp only [WP.spec_ok]
  step with numericSpec as ⟨status,bytes,statusEq,bytesEq⟩
  subst status bytes

  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  have bytesSame := writeLaw (view object.buf) rfl
  split
  · rename_i positive
    have posNat : 0 < wr.val := by scalar_tac
    try simp only [lift,bind_ok]
    step as ⟨destination,hdestination⟩
    step as ⟨pair,hold,hback⟩
    rcases pair with ⟨old,back⟩
    dsimp only at hold hback ⊢
    try simp only [lift,bind_ok]
    split
    · rename_i two
      step as ⟨shifted,hshifted,shiftBits⟩
      try simp only [lift,bind_ok]
      step as ⟨destination2,hdestination2⟩
      step as ⟨next,hnext⟩
      rw [hback]
      step as ⟨old2,back2,hold2,hback2⟩
      refine ⟨⟨writeBack (view object.buf),?_,bytesSame⟩,?_⟩
      · simp [memBack]
      simp [SlotsEffect,simdResultSlots,posNat,two,hback,hback2,hdestination,hdestination2,hnext]
      congr 1
      exact (UScalar.eq_equiv_bv_eq _ _).mpr (by simpa [UScalar.cast_bv_eq] using congrArg (BitVec.setWidth 64) shiftBits)
    · rename_i other
      with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) ⦃ _ ⦄
      rw [bind_ok]
      with_unfolding_all change Result.ok _ ⦃ _ ⦄
      rw [WP.spec_ok]
      refine ⟨rfl,⟨writeBack (view object.buf),?_,bytesSame⟩,?_⟩
      · simp [memBack]
      simp [SlotsEffect,simdResultSlots,posNat,other,hback,hdestination]
  · rename_i zero
    have zeroNat : ¬0 < wr.val := by scalar_tac
    have notTwo : wr ≠ 2#u32 := by scalar_tac
    simp only [if_neg notTwo,bind_ok,WP.spec_ok]
    refine ⟨rfl,⟨writeBack (view object.buf),?_,bytesSame⟩,?_⟩
    · simp [memBack]
    simp [SlotsEffect,simdResultSlots,zeroNat,notTwo]

end Itasca.Runtime.Interp
