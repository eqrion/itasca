import Exec.Interp.Relations.Const
namespace Exec.Interp.FloatConstant
open Aeneas Aeneas.Std SpecExt

theorem encode_float32 (bits : U32) :
    Code.encodeValue (.CONST .F32 (.mk_num__1 .F32 (Builtins.floatOfBits 32 bits.val))) = [bits.val] := by
  change [Builtins.floatBits 32 (Builtins.floatOfBits 32 bits.val)] = [bits.val]
  rw [Builtins.Float.float_bits_roundtrip_32 bits.val (by scalar_tac)]

theorem dispatch_float32_slots {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (dst : U32) (bits : U32)
    (f : Abs.AFrame) (after : List instr)
    (slots : FrameSlots exec raw f)
    (destination : dst.val = Code.slots ((f.locals ++ f.vals).map Code.valueType))
    (capacity : raw.base.val+dst.val < exec.slots.length) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex
      raw.instance raw.function raw.base (.Const32 dst bits) ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      FrameSlots out.2.1 raw {f with code := after,vals := f.vals ++ [.CONST .F32 (.mk_num__1 .F32 (Builtins.floatOfBits 32 bits.val))]} ∧
      SlotsEffect exec out.2.1 (exec.slots.val.set (raw.base.val+dst.val) (UScalar.cast .U64 bits)) ⦄ := by
  have length : (Code.encodeValues (f.locals ++ f.vals)).length = dst.val := by
    rw [Code.encodeValues_length,destination]
  have represented := WordsAt.set_append slots (UScalar.cast .U64 bits) (by simpa only [length] using capacity)
  rw [length] at represented
  simp only [runtime.interp.dispatch]
  obtain ⟨out,result,success,written,unchanged⟩ := WP.spec_imp_exists
    (const32_effect memory hooks floats allocator exec raw.base dst bits capacity)
  rw [result,bind_ok]
  rcases out with ⟨answer,next⟩
  with_unfolding_all apply WP.spec.ret
  refine ⟨success,rfl,rfl,?_,written,unchanged⟩
  simp only [FrameSlots,ValuesAt,written]
  simpa only [Code.encodeValues_append,Code.encodeValues,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,List.append_assoc,encode_float32, U32.cast_U64_val_eq] using represented

theorem encode_float64 (bits : U64) :
    Code.encodeValue (.CONST .F64 (.mk_num__1 .F64 (Builtins.floatOfBits 64 bits.val))) = [bits.val] := by
  change [Builtins.floatBits 64 (Builtins.floatOfBits 64 bits.val)] = [bits.val]
  rw [Builtins.Float.float_bits_roundtrip_64 bits.val (by scalar_tac)]

theorem dispatch_float64_slots {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (dst : U32) (bits : U64)
    (f : Abs.AFrame) (after : List instr)
    (slots : FrameSlots exec raw f)
    (destination : dst.val = Code.slots ((f.locals ++ f.vals).map Code.valueType))
    (capacity : raw.base.val+dst.val < exec.slots.length) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex
      raw.instance raw.function raw.base (.Const64 dst bits) ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      FrameSlots out.2.1 raw {f with code := after,vals := f.vals ++ [.CONST .F64 (.mk_num__1 .F64 (Builtins.floatOfBits 64 bits.val))]} ∧
      SlotsEffect exec out.2.1 (exec.slots.val.set (raw.base.val+dst.val) bits) ⦄ := by
  have length : (Code.encodeValues (f.locals ++ f.vals)).length = dst.val := by
    rw [Code.encodeValues_length,destination]
  have represented := WordsAt.set_append slots bits (by simpa only [length] using capacity)
  rw [length] at represented
  simp only [runtime.interp.dispatch]
  obtain ⟨out,result,success,written,unchanged⟩ := WP.spec_imp_exists
    (const64_effect memory hooks floats allocator exec raw.base dst bits capacity)
  rw [result,bind_ok]
  rcases out with ⟨answer,next⟩
  with_unfolding_all apply WP.spec.ret
  refine ⟨success,rfl,rfl,?_,written,unchanged⟩
  simp only [FrameSlots,ValuesAt,written]
  simpa only [Code.encodeValues_append,Code.encodeValues,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,List.append_assoc,encode_float64] using represented

end Exec.Interp.FloatConstant
