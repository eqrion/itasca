import Itasca.Runtime.Interp.Relations.Move
import Itasca.Runtime.Abs.Sim.Instruction

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem dispatch_localGet_refines {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (index src dst : U32)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (front : List val) (value : val)
    (lookup : f.locals[index.val]? = some value)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .LOCAL_GET (.mk_uN index.val) :: after, vals := front } :: rest, []⟩)
    (slots : FrameSlots exec raw { f with vals := front })
    (source : src.val = Code.offset (f.locals.map Code.valueType) index.val)
    (destination : dst.val = Code.slots ((f.locals ++ front).map Code.valueType))
    (capacity : raw.base.val + dst.val + Code.width (Code.valueType value) ≤ exec.slots.length) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex
      raw.instance raw.function raw.base (Code.move (Code.valueType value) dst src) ⦃ out =>
      out.1 = .Ok () ∧
      FrameSlots out.2.1 raw { f with code := after, vals := front ++ [value] } ∧
      { out.2.1 with slots := exec.slots } = exec ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      Abs.NextSim
        ⟨s, ambient, { f with code := .LOCAL_GET (.mk_uN index.val) :: after, vals := front } :: rest, []⟩
        ⟨s, ambient, { f with code := after, vals := front ++ [value] } :: rest, []⟩ ⦄ := by
  have typeLookup : (f.locals.map Code.valueType)[index.val]? = some (Code.valueType value) := by
    simpa using congrArg (Option.map Code.valueType) lookup
  have localEnd := Code.offset_add_width_le typeLookup
  have stackLength : (Code.encodeValues (f.locals ++ front)).length = dst.val := by
    rw [Code.encodeValues_length, destination]
  have order : raw.base.val + src.val + (Code.encodeValue value).length ≤ raw.base.val + dst.val := by
    rw [Code.encodeValue_length, source, destination]
    simp only [List.map_append, Code.slots_append]
    omega
  have sourceBound : raw.base.val + src.val + Code.width (Code.valueType value) ≤ exec.slots.length := by
    rw [Code.encodeValue_length] at order
    omega
  have values : ValuesAt exec.slots.val raw.base.val (f.locals ++ front) := slots
  have input : WordsAt exec.slots.val (raw.base.val + src.val) (Code.encodeValue value) := by
    simpa only [source] using values.locals.lookup lookup
  have represented := WordsAt.copy_append values input
    (by rw [stackLength]; exact Or.inr order)
    (by simpa only [Code.encodeValue_length] using sourceBound)
    (by simpa only [stackLength, Code.encodeValue_length] using capacity)
  rw [stackLength] at represented
  have step : Abs.astep ⟨s, ambient, { f with code := .LOCAL_GET (.mk_uN index.val) :: after, vals := front } :: rest, []⟩ =
      .next ⟨s, ambient, { f with code := after, vals := front ++ [value] } :: rest, []⟩ := by
    simp only [Abs.astep, lookup, Abs.advance]
  have simulation := Abs.instruction_simulation s ambient { f with vals := front } rest
    (.LOCAL_GET (.mk_uN index.val)) after _ (.local_get _) typed step
  apply WP.spec_mono (dispatch_move_effect memory hooks floats allocator exec store platform
    frameIndex raw.instance raw.function raw.base (Code.valueType value) dst src sourceBound capacity)
  intro out effect
  obtain ⟨success, ⟨written, unchanged⟩, sameStore, samePlatform⟩ := effect
  refine ⟨success, ?_, unchanged, sameStore, samePlatform, simulation⟩
  have result : ValuesAt out.2.1.slots.val raw.base.val ((f.locals ++ front) ++ [value]) := by
    rw [written]
    simpa only [ValuesAt, Code.encodeValues_append, Code.encodeValues, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, Code.encodeValue_length] using represented
  simpa only [FrameSlots, List.append_assoc] using result

end Itasca.Runtime.Interp
