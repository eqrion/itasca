import Exec.Interp.Simd.Common.SimdMutation
import Exec.Interp.Simd.Memory.SimdExecuteMemory
import Exec.Interp.Memory.MemoryDecode
import Exec.Interp.Relations.FrameStoreMetadata
namespace Exec.Interp
open Aeneas Aeneas.Std

theorem execute_simd_source_mutation_bounded {M F : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (interpretation : Exec.Store.CodeInterpretation) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instIndex function base : Usize) (op dst a entry : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (imm : runtime.bytecode.SimdImmediate) (wa wb wc wr : U32)
    (source : U128 → Prop)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : inst.module.functions.val[function.val]? = some code)
    (immediate : code.simd.val[entry.val]? = some imm)
    (shape : runtime.bytecode.simd_shape op = .ok (some (wa,wb,wc,wr)))
    (memories : ∀ ma, inst.memories.val[0]? = some ma →
      ∃ object, store.memories.val[ma.index.val]? = some object)
    (space : base.val + a.val + wa.val + wb.val ≤ Usize.max)
    (lastSpace : wc = 2#u32 → base.val + a.val + wa.val + wb.val < Usize.max)
    (capacity : base.val + dst.val + wr.val ≤ exec.slots.length)
    (numeric : ∀ bytes, runtime.interp.simd.simd floats op imm.offset imm.lane imm.bits
      (simdInput exec.slots.val (base.val+a.val) wa)
      (simdInput exec.slots.val (base.val+a.val+wa.val) wb)
      (simdInput exec.slots.val (base.val+a.val+wa.val+wb.val) wc) bytes
      ⦃ result => ∃ value, result = (.Ok value,bytes) ∧ source value ⦄) :
    runtime.interp.execute_simd memory floats exec store instIndex function base op dst a entry
      ⦃ out => SimdStoreMutation view store out.2.2 ∧ ∃ value, source value ∧ out.1 = .Ok () ∧
        Exec.Store.decodeStore view interpretation out.2.2 = Exec.Store.decodeStore view interpretation store ∧
        FrameStoreMetadata store out.2.2 ∧ SlotsEffect exec out.2.1
        (simdResultSlots exec.slots.val (base.val+dst.val) wr value) ⦄ := by
  cases lookup : inst.memories.val[0]? with
  | none =>
    have empty : inst.memories.val = [] := by
      cases h : inst.memories.val with
      | nil => rfl
      | cons first rest => simp [h] at lookup
    obtain ⟨result,run,value,resultEq,allowed⟩ := WP.spec_imp_exists (numeric none)
    rw [resultEq] at run
    apply WP.spec_mono (execute_simd_no_memory_bounded memory floats exec store instIndex function base
      op dst a entry inst code imm wa wb wc wr value found compiled immediate shape empty space lastSpace capacity run)
    rintro out ⟨ok,unchanged,slots⟩
    rw [unchanged]
    exact ⟨Or.inl rfl,value,allowed,ok,rfl,⟨rfl,rfl,rfl,rfl⟩,slots⟩
  | some ma =>
    obtain ⟨object,issued⟩ := memories ma lookup
    obtain ⟨result,run,value,resultEq,allowed⟩ := WP.spec_imp_exists (numeric (some (view object.buf)))
    rw [resultEq] at run
    apply WP.spec_mono (execute_simd_pure_memory_bounded memory floats view laws exec store instIndex function base
      op dst a entry inst code imm wa wb wc wr value found compiled immediate shape ma object lookup issued space lastSpace capacity
      run)
    rintro out ⟨ok,⟨buffer,changed,bytes⟩,slots⟩
    have mutation : SimdStoreMutation view store out.2.2 :=
      Or.inr ⟨ma,object,issued,buffer,changed,by rw [bytes]⟩
    refine ⟨mutation,value,allowed,ok,?_,?_,slots⟩
    · rw [changed]
      exact memory_unchanged_decodes view interpretation store ma object buffer issued bytes
    · rw [changed]
      exact ⟨rfl,rfl,rfl,rfl⟩

end Exec.Interp
