import Itasca.Runtime.Interp.Relations.Regions
import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.SourceMachine.Sim.Instruction
import Itasca.Runtime.Interp.Control.PendingJump

/-!
Branch execution with a transferred or already-positioned result region. The transfer effect and ValuesAt transport justify eliding a redundant copy before the common source branch step.
-/

/-! ## Branch Transfer -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- The compiler specializes short branch transfers to fixed-width copies. -/
abbrev transferInstruction := Code.transferInstruction

set_option maxHeartbeats 800000 in
theorem dispatch_transfer_effect {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index inst function base : Usize) (dst src count : U32)
    (source : base.val + src.val + count.val ≤ exec.slots.length)
    (destination : base.val + dst.val + count.val ≤ exec.slots.length) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base
      (transferInstruction dst src count) ⦃ out => out.1 = .Ok () ∧
        SlotsEffect exec out.2.1 (copyWords exec.slots.val (base.val + dst.val) (base.val + src.val) count.val) ∧
        out.2.2.1 = store ∧ out.2.2.2 = platform ⦄ := by
  by_cases one : count.val = 1
  · simp only [transferInstruction, Code.transferInstruction, if_pos one, runtime.interp.dispatch]
    obtain ⟨out, result, success, effect⟩ := WP.spec_imp_exists
      (copy_effect exec base dst src (by omega) (by omega))
    rw [result, bind_ok]
    rcases out with ⟨answer, next⟩
    with_unfolding_all apply WP.spec.ret
    exact ⟨success, by simpa only [one, copyWords] using effect, rfl, rfl⟩
  · by_cases two : count.val = 2
    · simp only [transferInstruction, Code.transferInstruction, if_neg one, if_pos two, runtime.interp.dispatch]
      obtain ⟨out, result, success, effect⟩ := WP.spec_imp_exists
        (copy2_effect exec base dst src (by omega) (by omega))
      rw [result, bind_ok]
      rcases out with ⟨answer, next⟩
      with_unfolding_all apply WP.spec.ret
      exact ⟨success, by simpa only [two] using effect, rfl, rfl⟩
    · simp only [transferInstruction, Code.transferInstruction, if_neg one, if_neg two, runtime.interp.dispatch]
      obtain ⟨out, result, success, effect⟩ := WP.spec_imp_exists
        (copy_n_effect exec base dst src count source destination
          (by scalar_tac) (by scalar_tac))
      rw [result, bind_ok]
      rcases out with ⟨answer, next⟩
      with_unfolding_all apply WP.spec.ret
      exact ⟨success, effect, rfl, rfl⟩

/-- Removing an operand interval copies the retained results downward. This
includes overlapping source/destination regions and zero result words. -/
theorem ValuesAt.transfer {words : List U64} {base : Nat}
    {front discarded results : List val}
    (live : ValuesAt words base (front ++ discarded ++ results))
    (capacity : base + Code.slots ((front ++ discarded ++ results).map Code.valueType) ≤ words.length) :
    ValuesAt (copyWords words
      (base + Code.slots (front.map Code.valueType))
      (base + Code.slots ((front ++ discarded).map Code.valueType))
      (Code.slots (results.map Code.valueType))) base (front ++ results) := by
  have saved : WordsAt words base (Code.encodeValues front) := by
    apply WordsAt.append_left (right := Code.encodeValues discarded ++ Code.encodeValues results)
    simpa only [ValuesAt, Code.encodeValues_append, List.append_assoc] using live
  have input : WordsAt words (base + Code.slots ((front ++ discarded).map Code.valueType))
      (Code.encodeValues results) := by
    have suffix := live.operands
    simpa only [ValuesAt] using suffix
  have order : base + (Code.encodeValues front).length ≤
      base + Code.slots ((front ++ discarded).map Code.valueType) := by
    simp only [Code.encodeValues_length, List.map_append, Code.slots_append]
    omega
  have source : base + Code.slots ((front ++ discarded).map Code.valueType) +
      (Code.encodeValues results).length ≤ words.length := by
    simpa only [Code.encodeValues_length, List.map_append, Code.slots_append, Nat.add_assoc] using capacity
  have copied := WordsAt.copy_append saved input (Or.inl order) source (by omega)
  simpa only [ValuesAt, Code.encodeValues_append, Code.encodeValues_length] using copied

/-- The first instruction in a compiled branch pair performs the source
branch's operand transfer. A separate pending-jump phase retains its target. -/
theorem dispatch_branchTransfer_refines {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (dst src count : U32)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (depth : Nat) (target : Abs.Label)
    (front discarded results : List val)
    (lookup : f.labels[depth]? = some target)
    (height : target.height = front.length)
    (arity : target.arity = results.length)
    (types : results.map Abs.valueType = target.branchTypes)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .BR (.mk_uN depth) :: after, vals := front ++ discarded ++ results } :: rest, []⟩)
    (slots : FrameSlots exec raw { f with vals := front ++ discarded ++ results })
    (destination : dst.val = Code.slots ((f.locals ++ front).map Code.valueType))
    (source : src.val = Code.slots ((f.locals ++ front ++ discarded).map Code.valueType))
    (size : count.val = Code.slots (results.map Code.valueType))
    (capacity : raw.base.val + Code.slots ((f.locals ++ front ++ discarded ++ results).map Code.valueType) ≤ exec.slots.length) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex
      raw.instance raw.function raw.base (transferInstruction dst src count) ⦃ out =>
      out.1 = .Ok () ∧
      FrameSlots out.2.1 raw { f with code := target.cont ++ target.after, labels := f.labels.drop (depth + 1), vals := front ++ results } ∧
      { out.2.1 with slots := exec.slots } = exec ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      Abs.NextSim
        ⟨s, ambient, { f with code := .BR (.mk_uN depth) :: after, vals := front ++ discarded ++ results } :: rest, []⟩
        ⟨s, ambient, { f with code := target.cont ++ target.after, labels := f.labels.drop (depth + 1), vals := front ++ results } :: rest, []⟩ ⦄ := by
  have allValues : ValuesAt exec.slots.val raw.base.val ((f.locals ++ front) ++ discarded ++ results) := by
    simpa only [FrameSlots, List.append_assoc] using slots
  have copied := ValuesAt.transfer allValues capacity
  have hs : raw.base.val + src.val + count.val ≤ exec.slots.length := by
    simpa only [source, size, List.map_append, Code.slots_append, Nat.add_assoc] using capacity
  have hd : raw.base.val + dst.val + count.val ≤ exec.slots.length := by
    simp only [destination, source, size, List.map_append, Code.slots_append] at hs ⊢
    omega
  have step : Abs.astep
      ⟨s, ambient, { f with code := .BR (.mk_uN depth) :: after, vals := front ++ discarded ++ results } :: rest, []⟩ = .next
      ⟨s, ambient, { f with code := target.cont ++ target.after, labels := f.labels.drop (depth + 1), vals := front ++ results } :: rest, []⟩ := by
    have drop : (front ++ discarded ++ results).drop ((front ++ discarded ++ results).length - target.arity) = results := by
      rw [arity, List.length_append, Nat.add_sub_cancel]
      exact List.drop_left
    have take : (front ++ discarded ++ results).take target.height = front := by
      simp [height, List.append_assoc]
    have bound : target.height + target.arity ≤ (front ++ discarded ++ results).length := by
      simp only [height, arity, List.length_append]
      omega
    simp only [Abs.astep, Abs.branch, lookup, bound, drop, types, and_self, ↓reduceIte, take, Abs.advance]
  have simulation := Abs.instruction_simulation s ambient { f with vals := front ++ discarded ++ results } rest
    (.BR (.mk_uN depth)) after _ (.br _) typed step
  apply WP.spec_mono (dispatch_transfer_effect memory hooks floats allocator exec store platform
    frameIndex raw.instance raw.function raw.base dst src count hs hd)
  intro out effect
  obtain ⟨success, ⟨written, unchanged⟩, sameStore, samePlatform⟩ := effect
  refine ⟨success, ?_, unchanged, sameStore, samePlatform, simulation⟩
  simp only [FrameSlots, written]
  simpa only [destination, source, size, List.append_assoc] using copied

end Itasca.Runtime.Interp

end

/-! ## Branch No Copy -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem branch_no_transfer {locals front discarded results : List val} {dst src count : U32}
    (destination : dst.val = Code.slots ((locals ++ front).map Code.valueType))
    (source : src.val = Code.slots ((locals ++ front ++ discarded).map Code.valueType))
    (size : count.val = Code.slots (results.map Code.valueType))
    (elided : count = 0#u32 ∨ src = dst) :
    Code.slots (results.map Code.valueType) = 0 ∨ Code.slots (discarded.map Code.valueType) = 0 := by
  rcases elided with zero | same
  · left
    rw [zero] at size
    exact size.symm
  · right
    have equal := congrArg UScalar.val same
    simp only [source, destination, List.map_append, Code.slots_append] at equal
    omega

theorem ValuesAt.elide_transfer {words : List U64} {base : Nat} {front discarded results : List val}
    (live : ValuesAt words base (front ++ discarded ++ results))
    (noCopy : Code.slots (results.map Code.valueType) = 0 ∨ Code.slots (discarded.map Code.valueType) = 0) :
    ValuesAt words base (front ++ results) := by
  rcases noCopy with empty | same
  · have length := Code.length_le_slots (results.map Code.valueType)
    have nil : results = [] := by apply List.eq_nil_of_length_eq_zero; simp only [List.length_map] at length; omega
    subst results
    have h : ValuesAt words base (front ++ discarded) := by simpa only [List.append_nil] using live
    simpa only [List.append_nil] using h.locals
  · have length := Code.length_le_slots (discarded.map Code.valueType)
    have nil : discarded = [] := by apply List.eq_nil_of_length_eq_zero; simp only [List.length_map] at length; omega
    subst discarded
    simpa only [List.append_nil] using live

theorem branch_source_step (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (depth : Nat) (target : Abs.Label) (front discarded results : List val)
    (lookup : f.labels[depth]? = some target) (height : target.height = front.length)
    (arity : target.arity = results.length) (types : results.map Abs.valueType = target.branchTypes) :
    Abs.astep
      ⟨s, ambient, { f with code := .BR (.mk_uN depth) :: after, vals := front ++ discarded ++ results } :: rest, []⟩ = .next
      ⟨s, ambient, { f with code := target.cont ++ target.after, labels := f.labels.drop (depth + 1), vals := front ++ results } :: rest, []⟩ := by
  have drop : (front ++ discarded ++ results).drop ((front ++ discarded ++ results).length - target.arity) = results := by
    rw [arity, List.length_append, Nat.add_sub_cancel]
    exact List.drop_left
  have take : (front ++ discarded ++ results).take target.height = front := by
    simp [height, List.append_assoc]
  have bound : target.height + target.arity ≤ (front ++ discarded ++ results).length := by
    simp only [height, arity, List.length_append]
    omega
  simp only [Abs.astep, Abs.branch, lookup, bound, drop, types, and_self, ↓reduceIte, take, Abs.advance]

theorem step_branchNoCopy_refines {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (targetPC : U32)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (depth : Nat) (target : Abs.Label) (front discarded results : List val)
    (last : frameIndex.val + 1 = exec.frames.length)
    (frameLookup : exec.frames.val[frameIndex.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (fetched : compiled.code.val[raw.pc.val]? = some (.Jump targetPC))
    (lookup : f.labels[depth]? = some target) (height : target.height = front.length)
    (arity : target.arity = results.length) (types : results.map Abs.valueType = target.branchTypes)
    (noCopy : Code.slots (results.map Code.valueType) = 0 ∨ Code.slots (discarded.map Code.valueType) = 0)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .BR (.mk_uN depth) :: after, vals := front ++ discarded ++ results } :: rest, []⟩)
    (slots : FrameSlots exec raw { f with vals := front ++ discarded ++ results }) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out => out.1 = .Ok () ∧
      out.2.1 = { exec with frames := exec.frames.set frameIndex { raw with pc := targetPC } } ∧
      FrameSlots out.2.1 { raw with pc := targetPC }
        { f with code := target.cont ++ target.after, labels := f.labels.drop (depth + 1), vals := front ++ results } ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      Abs.NextSim
        ⟨s, ambient, { f with code := .BR (.mk_uN depth) :: after, vals := front ++ discarded ++ results } :: rest, []⟩
        ⟨s, ambient, { f with code := target.cont ++ target.after, labels := f.labels.drop (depth + 1), vals := front ++ results } :: rest, []⟩ ⦄ := by
  have allValues : ValuesAt exec.slots.val raw.base.val ((f.locals ++ front) ++ discarded ++ results) := by
    simpa only [FrameSlots, List.append_assoc] using slots
  have represented := allValues.elide_transfer noCopy
  have step := branch_source_step s ambient f rest after depth target front discarded results lookup height arity types
  have simulation := Abs.instruction_simulation s ambient { f with vals := front ++ discarded ++ results } rest
    (.BR (.mk_uN depth)) after _ (.br _) typed step
  apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
    frameIndex raw inst compiled targetPC last frameLookup hi hc pcBound fetched)
  intro out effect
  obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
  refine ⟨success, exactState, ?_, sameStore, samePlatform, simulation⟩
  rw [exactState]
  simpa only [FrameSlots, List.append_assoc] using represented

end Itasca.Runtime.Interp

end
