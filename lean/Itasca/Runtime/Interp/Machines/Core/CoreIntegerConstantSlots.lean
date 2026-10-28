import Itasca.Runtime.Interp.Relations.Execute
import Itasca.Runtime.Interp.Relations.Regions
import Itasca.Runtime.Abs.Sim.Instruction
namespace Itasca.Runtime.Interp.IntegerConstant
open Aeneas Aeneas.Std SpecExt

theorem encode_integer32 (bits : U32) :
    Code.encodeValue (.CONST .I32 (.mk_num__0 .I32 (.mk_uN bits.val))) = [bits.val] := by rfl

theorem dispatch_integer32_slots {M P F A : Type}
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
      FrameSlots out.2.1 raw {f with code := after,vals := f.vals ++ [.CONST .I32 (.mk_num__0 .I32 (.mk_uN bits.val))]} ∧
      SlotsEffect exec out.2.1 (exec.slots.val.set (raw.base.val+dst.val) (UScalar.cast .U64 bits)) ⦄ := by
  have length : (Code.encodeValues (f.locals ++ f.vals)).length = dst.val := by
    rw [Code.encodeValues_length,destination]
  have represented := WordsAt.set_append slots (UScalar.cast .U64 bits) (by simpa only [length] using capacity)
  rw [length] at represented
  simp only [runtime.interp.dispatch]
  obtain ⟨out,result,success,written,unchanged⟩ := WP.spec_imp_exists
    (const32_effect exec raw.base dst bits capacity)
  rw [result,bind_ok]
  rcases out with ⟨answer,next⟩
  with_unfolding_all apply WP.spec.ret
  refine ⟨success,rfl,rfl,?_,written,unchanged⟩
  simp only [FrameSlots,ValuesAt,written]
  simpa only [Code.encodeValues_append,Code.encodeValues,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,List.append_assoc,encode_integer32, U32.cast_U64_val_eq] using represented

theorem encode_integer64 (bits : U64) :
    Code.encodeValue (.CONST .I64 (.mk_num__0 .I64 (.mk_uN bits.val))) = [bits.val] := by rfl

theorem dispatch_integer64_slots {M P F A : Type}
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
      FrameSlots out.2.1 raw {f with code := after,vals := f.vals ++ [.CONST .I64 (.mk_num__0 .I64 (.mk_uN bits.val))]} ∧
      SlotsEffect exec out.2.1 (exec.slots.val.set (raw.base.val+dst.val) bits) ⦄ := by
  have length : (Code.encodeValues (f.locals ++ f.vals)).length = dst.val := by
    rw [Code.encodeValues_length,destination]
  have represented := WordsAt.set_append slots bits (by simpa only [length] using capacity)
  rw [length] at represented
  simp only [runtime.interp.dispatch]
  obtain ⟨out,result,success,written,unchanged⟩ := WP.spec_imp_exists
    (const64_effect exec raw.base dst bits capacity)
  rw [result,bind_ok]
  rcases out with ⟨answer,next⟩
  with_unfolding_all apply WP.spec.ret
  refine ⟨success,rfl,rfl,?_,written,unchanged⟩
  simp only [FrameSlots,ValuesAt,written]
  simpa only [Code.encodeValues_append,Code.encodeValues,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,List.append_assoc,encode_integer64] using represented

end Itasca.Runtime.Interp.IntegerConstant
