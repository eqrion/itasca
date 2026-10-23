import Exec.Interp.Relations.Execute
import Exec.Interp.Relations.Regions
import Exec.Abs.Sim.Instruction

namespace Exec.Interp
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

/-- Materializing an integer constant preserves decoded source configuration;
its administrative code-length measure strictly decreases. -/
theorem dispatch_const32_refines
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (dst : U32) (value : U32)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (destination : dst.val = Code.slots ((f.locals ++ f.vals).map Code.valueType))
    (capacity : raw.base.val + dst.val < exec.slots.length) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex
      raw.instance raw.function raw.base (.Const32 dst value) ⦃ out =>
      out.1 = .Ok () ∧
      FrameSlots out.2.1 raw { f with code := after, vals := f.vals ++ [Abs.integerVal .I32 value.val] } ∧
      { out.2.1 with slots := exec.slots } = exec ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      Abs.NextSim
        ⟨s, ambient, { f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after } :: rest, []⟩
        ⟨s, ambient, { f with code := after, vals := f.vals ++ [Abs.integerVal .I32 value.val] } :: rest, []⟩ ⦄ := by
  have length : (Code.encodeValues (f.locals ++ f.vals)).length = dst.val := by
    rw [Code.encodeValues_length, destination]
  have represented := WordsAt.set_append slots (UScalar.cast .U64 value)
    (by simpa only [length] using capacity)
  rw [length] at represented
  have bound : value.val < 4294967296 := by scalar_tac
  have step : Abs.astep
      ⟨s, ambient, { f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after } :: rest, []⟩ = .next
      ⟨s, ambient, { f with code := after, vals := f.vals ++ [Abs.integerVal .I32 value.val] } :: rest, []⟩ := by
    simp [Abs.astep, Abs.integer, numtype_Inn, bound, Abs.advance, Abs.integerVal]
  have simulation := Abs.instruction_simulation s ambient f rest
    (.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))) after _ (.const .I32 _) typed step
  simp only [runtime.interp.dispatch]
  obtain ⟨out, result, success, written, unchanged⟩ := WP.spec_imp_exists
    (const32_effect exec raw.base dst value capacity)
  rw [result, bind_ok]
  rcases out with ⟨answer, next⟩
  with_unfolding_all apply WP.spec.ret
  refine ⟨success, ?_, unchanged, rfl, rfl, simulation⟩
  simp only [FrameSlots, ValuesAt, written]
  simpa only [Code.encodeValues_append, Code.encodeValues, Abs.integerVal, Code.encodeValue,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc, numtype_Inn, U32.cast_U64_val_eq] using represented

/-- Materializing an integer constant preserves decoded source configuration;
its administrative code-length measure strictly decreases. -/
theorem dispatch_const64_refines
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (dst : U32) (value : U64)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (destination : dst.val = Code.slots ((f.locals ++ f.vals).map Code.valueType))
    (capacity : raw.base.val + dst.val < exec.slots.length) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex
      raw.instance raw.function raw.base (.Const64 dst value) ⦃ out =>
      out.1 = .Ok () ∧
      FrameSlots out.2.1 raw { f with code := after, vals := f.vals ++ [Abs.integerVal .I64 value.val] } ∧
      { out.2.1 with slots := exec.slots } = exec ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      Abs.NextSim
        ⟨s, ambient, { f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after } :: rest, []⟩
        ⟨s, ambient, { f with code := after, vals := f.vals ++ [Abs.integerVal .I64 value.val] } :: rest, []⟩ ⦄ := by
  have length : (Code.encodeValues (f.locals ++ f.vals)).length = dst.val := by
    rw [Code.encodeValues_length, destination]
  have represented := WordsAt.set_append slots value
    (by simpa only [length] using capacity)
  rw [length] at represented
  have bound : value.val < 18446744073709551616 := by scalar_tac
  have step : Abs.astep
      ⟨s, ambient, { f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after } :: rest, []⟩ = .next
      ⟨s, ambient, { f with code := after, vals := f.vals ++ [Abs.integerVal .I64 value.val] } :: rest, []⟩ := by
    simp [Abs.astep, Abs.integer, numtype_Inn, bound, Abs.advance, Abs.integerVal]
  have simulation := Abs.instruction_simulation s ambient f rest
    (.CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val))) after _ (.const .I64 _) typed step
  simp only [runtime.interp.dispatch]
  obtain ⟨out, result, success, written, unchanged⟩ := WP.spec_imp_exists
    (const64_effect exec raw.base dst value capacity)
  rw [result, bind_ok]
  rcases out with ⟨answer, next⟩
  with_unfolding_all apply WP.spec.ret
  refine ⟨success, ?_, unchanged, rfl, rfl, simulation⟩
  simp only [FrameSlots, ValuesAt, written]
  simpa only [Code.encodeValues_append, Code.encodeValues, Abs.integerVal, Code.encodeValue,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc, numtype_Inn] using represented

end Exec.Interp
