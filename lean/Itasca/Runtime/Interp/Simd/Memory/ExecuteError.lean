import Itasca.Runtime.Interp.Simd.Execution.ExecutePure
import Itasca.Runtime.Platform.Memory
import Itasca.Runtime.Interp.Simd.Relations.OperandsBounded

/-!
Bounded SIMD execution when the memory operation returns an error.

Main declarations: `execute_simd_memory_error_bounded`. A direct consumer is `Interp.Simd.Memory.SourceExecute`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

theorem execute_simd_memory_error_bounded {M F : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instIndex function base : Usize) (op dst a entry : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (imm : runtime.bytecode.SimdImmediate) (wa wb wc wr : U32)
    (error : runtime.ExecError)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : inst.module.functions.val[function.val]? = some code)
    (immediate : code.simd.val[entry.val]? = some imm)
    (shape : runtime.bytecode.simd_shape op = .ok (some (wa,wb,wc,wr)))
    (ma : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (mapped : inst.memories.val[0]? = some ma)
    (issued : store.memories.val[ma.index.val]? = some object)
    (bytesAfter : Slice U8) (lengthEq : bytesAfter.length = (view object.buf).length)
    (space : base.val + a.val + wa.val + wb.val ≤ Usize.max)
    (lastSpace : wc = 2#u32 → base.val + a.val + wa.val + wb.val < Usize.max)
    (capacity : base.val + dst.val + wr.val ≤ exec.slots.length)
    (numeric : runtime.interp.simd.simd floats op imm.offset imm.lane imm.bits
      (simdInput exec.slots.val (base.val+a.val) wa)
      (simdInput exec.slots.val (base.val+a.val+wa.val) wb)
      (simdInput exec.slots.val (base.val+a.val+wa.val+wb.val) wc) (some (view object.buf)) =
        .ok (.Err error,some bytesAfter)) :
    runtime.interp.execute_simd memory floats exec store instIndex function base op dst a entry
      ⦃ out => out.1 = .Err error ∧ out.2.1 = exec ∧
        ∃ buffer, out.2.2 = {store with memories := store.memories.set ma.index {object with buf := buffer}} ∧
          view buffer = bytesAfter ⦄ := by
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
  step with simd_input_bounded _ pos wa (by intro two; scalar_tac) as ⟨x,hx⟩
  try simp only [lift,bind_ok]
  step as ⟨ypos,hypos⟩
  step with simd_input_bounded _ ypos wb (by intro two; scalar_tac) as ⟨y,hy⟩
  try simp only [lift,bind_ok]
  step as ⟨zpos,hzpos⟩
  step with simd_input_bounded _ zpos wc (by intro two; scalar_tac) as ⟨z,hz⟩
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
      (simdInput exec.slots.val (base.val+a.val+wa.val+wb.val) wc) (some (view object.buf)) ⦃ out => out = (.Err error,some bytesAfter) ⦄ := by
    rw [numeric]
    simp only [WP.spec_ok]
  step with numericSpec as ⟨status,bytes,statusEq,bytesEq⟩
  subst status bytes

  have bytesSame := writeLaw bytesAfter lengthEq
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame,core.convert.FromSame.from,WP.spec_ok]
  with_unfolding_all change (Aeneas.Std.bind (Aeneas.Std.bind (Result.ok _) _) _) ⦃ _ ⦄
  rw [bind_ok,bind_ok]
  with_unfolding_all change Result.ok _ ⦃ _ ⦄
  rw [WP.spec_ok]
  refine ⟨rfl,rfl,writeBack bytesAfter,?_,bytesSame⟩
  simp [memBack]

end Itasca.Runtime.Interp
