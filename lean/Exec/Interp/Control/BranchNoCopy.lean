import Exec.Interp.Control.BranchTransfer
import Exec.Interp.Control.PendingJump

namespace Exec.Interp
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

/-- A branch with zero result slots or an identical result position emits only
the jump. Dead discarded words need no physical erasure. -/
theorem dispatch_branchNoCopy_refines {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (targetPC : U32)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (depth : Nat) (target : Abs.Label) (front discarded results : List val)
    (frameLookup : exec.frames.val[frameIndex.val]? = some raw)
    (lookup : f.labels[depth]? = some target) (height : target.height = front.length)
    (arity : target.arity = results.length) (types : results.map Abs.valueType = target.branchTypes)
    (noCopy : Code.slots (results.map Code.valueType) = 0 ∨ Code.slots (discarded.map Code.valueType) = 0)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .BR (.mk_uN depth) :: after, vals := front ++ discarded ++ results } :: rest, []⟩)
    (slots : FrameSlots exec raw { f with vals := front ++ discarded ++ results }) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex
      raw.instance raw.function raw.base (.Jump targetPC) ⦃ out => out.1 = .Ok () ∧
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
  apply WP.spec_mono (dispatch_jump_exact memory hooks floats allocator exec store platform
    frameIndex raw.instance raw.function raw.base raw targetPC frameLookup)
  intro out effect
  obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
  refine ⟨success, exactState, ?_, sameStore, samePlatform, simulation⟩
  rw [exactState]
  simpa only [FrameSlots, List.append_assoc] using represented

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

end Exec.Interp
